module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0020
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LagrangianCondition
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.GramExtendZeroEmbedded
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0011
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartFacts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0008
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.NormLawK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.NormModulusHeisenberg
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.ThKW.NormModulusHeisenberg
end
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.NormModulusHeisenberg in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ =
          mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hht f hf
  obtain ⟨μW, 𝓕W, κ, hμW, h𝓕W, hκ, hcoef⟩ := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.coef_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕
  have hωf := hωd.om_pres (1, h) f hf
  obtain ⟨c1, i1, e1⟩ := hcoef _ hωf
  obtain ⟨c0, i0, e0⟩ := hcoef f hf
  obtain ⟨cL, iL, eL⟩ := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.change_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 t _ c0 i0
  have hκ0 : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hκ.ne'
  have key : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (ωd (1, h) f) = fun w =>
      ((mfac F E nS t : ℝ) : ℂ) ^ 2 * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f ((t.1.map (cAF σ))ᵀ * w) := by
    refine _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.finj_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 _ _ c1 (continuous_const.mul cL) i1
      (iL.const_mul _) fun y => ?_
    have hact : actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) = dC (AF F ⊗[F] E) nT * y := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 by unfold mtF; rw [map_one, Units.val_one], Matrix.mul_one,
        ← Matrix.mul_assoc, hht, Matrix.mul_assoc, ← Matrix.mul_assoc t.1, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    have u := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.unit_coef_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS ωd hωd μW 𝓕W hμW h𝓕W h
      (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) f hf
    rw [hact, e1 y, e0 ((t⁻¹).1 * y), eL y] at u
    have u' := mul_left_cancel₀ hκ0 u
    rw [u', ← integral_const_mul]
    congr 1
    funext w
    ring
  have k0 := congrFun key 0
  rw [Matrix.mul_zero, nrm_zero, nrm_zero] at k0
  have k1 : ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ ^ 2 =
      (mfac F E nS t * ‖GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖) ^ 2 := by
    rw [mul_pow]
    exact_mod_cast k0
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (mfac_pos' nS t).le (norm_nonneg _)) two_ne_zero).1 k1
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelSmallK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
def SiegelSmall_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
  ∀ (om1 : d.G →* Module.End ℂ ((K1 d.m n → AF F) → ℂ)),
    IsSplitting (adeleClass F) d.B.ψ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) (actB (cA σ)) om1 →
    SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J))
      (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) d.χ (diagCols (Fin d.n)) om1 →
  ∀ φ₀ ∈ schA F (Fin d.m × Fin 2), φ₀ 0 = 1 →
  ∀ (om' : G2 σ Y →* Module.End ℂ ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ)),
    (∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), om1 (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₀) →
    SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F Y.J)) dd' d.χ (diagCols (Fin n)) om'
def SmallS_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
  ∀ (S1 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((K1 d.m n → AF F) → ℂ)) (S1' : ((K1 d.m n → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ))
    (C : ℂ), C ≠ 0 →
    GlobalTheory.TowU.IsOp d.B.ψ (fun w => (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e (d.dd.e.symm w)) S1 S1' →
    (∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S1 Φ (crdB d.bs X ∘ eK d.m h)) →
  ∃ S' : UA σ d.A.J →* Module.End ℂ ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ),
    IsUSplitting (adeleClass F) d.B.ψ dd' (fun (g : UA σ d.A.J) x => mat g * x) S' ∧
    ∀ g, ∀ Φ ∈ schA F (Fin d.m × Fin n × Fin 2), ev0 _ (S' g Φ) = ev0 _ Φ
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def phz_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (f : d.G → ℂ) (s₁ z : ℂ) (x : d.G) : ℂ := ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x
abbrev Cs_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type := GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y)
def rep_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) : d.G := ((Quot.out q : rat2 σ d.Y) : d.G)
def FirstOrbit {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (γ : d.G) : Prop := ∀ i, inFrame d.b γ (Sum.inr i) (Sum.inl L.i₀) = 0
def kq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (T : nF σ d.Y d.b)
    (uM : (Fin L.n → AE F E) → d.G) (γ x : d.G) (p : (Fin L.n → AE F E) × nA σ d.Y d.b) : ℂ :=
  _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (γ * (nb p.2 * (uM p.1 * x))) *
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * p.2.1))))
def tm_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (γ x : d.G) : ℂ :=
  ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (fun g => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (γ * g)) T (uM u * x) ∂ν
def secondOrbitSection {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E))
    (𝓤 : Set (Fin L.n → AE F E)) (x : d.G) : ℂ :=
  ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x
def first_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb' : nA σ L.Y L.b → G2 σ L.Y) (lam' : Measure (nA σ L.Y L.b))
    (𝓖' : Set (nA σ L.Y L.b)) (T' : nF σ L.Y L.b) (x : d.G) : ℂ :=
  fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
    ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAfcOrbS
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem gram_incM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (gE d.A.J σ X) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by ext i j; rfl
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [h1]
  simp only [gE, incM, ← Matrix.transpose_map, ← Matrix.map_mul]
theorem cond_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) (M : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • M ↔
      ∀ k l, inclR (F := F) (AF F) (gE d.A.J σ X k l) = (-2 : ℤ) • M k l := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gram_incM_k, ← Matrix.ext_iff]
  rfl
theorem orb_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hmn : d.m < d.n) (T : nF σ d.Y d.b) (hT : IsND T) (Φ : d.Fn) : d.orb T Φ = 0 := by
  have hE : IsEmpty {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} := by
    refine ⟨fun ⟨X, hX⟩ => ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gram_incM_k] at hX
    have hdet := congrArg Matrix.det hX
    have h0 : (gE d.A.J σ X).det = 0 := by
      by_contra h
      have hu : IsUnit (gE d.A.J σ X) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
      have h1 := Matrix.rank_of_isUnit _ hu
      have h2 : (gE d.A.J σ X).rank ≤ d.m := by
        rw [gE, Matrix.mul_assoc]
        exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
      rw [h1, Fintype.card_fin] at h2
      omega
    have hm : ((gE d.A.J σ X).map (inclR (F := F) (AF F))).det = inclR (F := F) (AF F) (gE d.A.J σ X).det :=
      ((inclR (F := F) (AF F)).map_det _).symm
    rw [incM, hm, h0, map_zero, ← Int.cast_smul_eq_zsmul (AE F E), Matrix.det_smul, Fintype.card_fin] at hdet
    exact hT ((isUnit_neg_two_pow d.n).mul_right_eq_zero.1 hdet.symm)
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb, tsum_empty]
section Res
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def extendByZeroColumns (X' : Matrix (Fin d.m) (Fin L.n) E) : Matrix (Fin d.m) (Fin d.n) E := fun a => Function.extend L.em (X' a) 0
theorem extendZeroColumn_apply_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) (j : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X' a (L.em j) = X' a j :=
  L.inj.extend_apply _ _ _
theorem not_mem_range_k : L.i₀ ∉ Set.range L.em := fun h => ((L.rng L.i₀).2 h) rfl
theorem extendZeroColumn_apply_missing (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X' a L.i₀ = 0 :=
  Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => _root_.PositivityTheory.SiegelWeilFormula.Afc.not_mem_range_k L ⟨j, hj⟩
theorem cases_idx_k (k : Fin d.n) : k = L.i₀ ∨ ∃ j, L.em j = k := by
  by_cases h : k = L.i₀
  · exact Or.inl h
  · exact Or.inr ((L.rng k).1 h)
theorem hermForm_extendZeroColumn_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (i j : Fin L.n) :
    gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') (L.em i) (L.em j) = gE d.A.J σ X' i j := by
  simp only [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed]
theorem hermForm_extendZeroColumn_left (X' : Matrix (Fin d.m) (Fin L.n) E) (l : Fin d.n) : gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') L.i₀ l = 0 := by
  simp [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing]
theorem hermForm_extendZeroColumn_right (X' : Matrix (Fin d.m) (Fin L.n) E) (k : Fin d.n) : gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') k L.i₀ = 0 := by
  simp [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing]
theorem gE_sub_k (X : Matrix (Fin d.m) (Fin d.n) E) (i j : Fin L.n) :
    gE d.A.J σ (X.submatrix id L.em) i j = gE d.A.J σ X (L.em i) (L.em j) := by
  simp only [gE_apply, Matrix.submatrix_apply, id]
theorem col_zero_k (X : Matrix (Fin d.m) (Fin d.n) E) (h : gE d.A.J σ X L.i₀ L.i₀ = 0) (a : Fin d.m) : X a L.i₀ = 0 := by
  have hA : Aniso σ d.A.J := _root_.GlobalTheory.ThK.Dbl.aniso_of_k d.ok.good (d.ok.sign.elim (fun h => Or.inl h.1) fun h => Or.inr h.1) d.ok.aniso
  have key := hA (fun i => X i L.i₀) (by
    rw [← h, gE_apply]
    simp only [form, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring)
  exact congrFun key a
theorem extension_by_zero_submatrix (X : Matrix (Fin d.m) (Fin d.n) E) (h : ∀ a, X a L.i₀ = 0) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L (X.submatrix id L.em) = X := by
  ext a k
  rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L k with rfl | ⟨j, rfl⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing, h]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed]; rfl
theorem submatrix_extendZeroColumn (X' : Matrix (Fin d.m) (Fin L.n) E) : (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X').submatrix id L.em = X' := by
  ext a j
  exact _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed L X' a j
def eqv_k (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') :
    {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Matrix (Fin L.sd.m) (Fin L.sd.n) E // L.sd.gram (incM F X) (incM F X) = (-2 : ℤ) • T'.1.1} where
  toFun X := ⟨X.1.submatrix id L.em, by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k L.sd _ _).2 fun i j => ?_
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 (L.em i) (L.em j)
    show inclR (F := F) (AF F) (gE d.A.J σ (X.1.submatrix id L.em) i j) = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gE_sub_k, h, hs.2]
    rfl⟩
  invFun X' := ⟨_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X'.1, by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).2 fun k l => ?_
    rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L k with rfl | ⟨i, rfl⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_left, (hs.1 l).1, map_zero, smul_zero]
    rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L l with rfl | ⟨j, rfl⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_right, (hs.1 _).2, map_zero, smul_zero]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_embed]
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k L.sd _ _).1 X'.2 i j
    refine h.trans ?_
    rw [hs.2]
    rfl⟩
  left_inv X := by
    refine Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.Afc.extension_by_zero_submatrix L X.1 (_root_.PositivityTheory.SiegelWeilFormula.Afc.col_zero_k L X.1 ?_))
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm)
  right_inv X' := Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.Afc.submatrix_extendZeroColumn L X'.1)
theorem orb_res_k (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (Φ : d.Fn) (Φ' : L.sd.Fn)
    (hr : L.IsRes Φ Φ') : d.orb T Φ = L.sd.orb T' Φ' := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.orb
  refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Afc.eqv_k L T T' hs).tsum_eq]
  refine tsum_congr fun X => ?_
  have hc : ∀ a, X.1 a L.i₀ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Afc.col_zero_k L X.1 (by
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm))
  have hz : ∀ a, (mat g⁻¹ * incM F X.1) a L.i₀ = 0 := fun a => by
    simp [Matrix.mul_apply, incM, hc]
  rw [← hr.2 _ hz]
  congr 1
end Res
theorem orbRes_k : _root_.PositivityTheory.SiegelWeilFormula.OrbRes_k := fun _F _E _ _ _ _ _ _σ d =>
  ⟨fun hmn T hT Φ => _root_.PositivityTheory.SiegelWeilFormula.Afc.orb_zero_k d hmn T hT Φ, fun L T T' hs Φ Φ' hr => _root_.PositivityTheory.SiegelWeilFormula.Afc.orb_res_k L T T' hs Φ Φ' hr⟩
end PositivityTheory.SiegelWeilFormula.Afc
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldCut
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
def YFrame_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ), n + 1 = d.n → 1 ≤ n →
  ∃ (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ), _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y ∧ IsFrame2 σ Y b ∧
    d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε
def JEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ j : G2 σ Y →* d.G, _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j
def KStd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), IsFrame2 σ Y b → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j → IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j)
def HgtPull_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j → IsHgt (d.K.comap j) (d.a ∘ j)
def ModelEx_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  (∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∃ (κ : Type) (_ : Fintype κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), IsDbl (σ := σ) (A := d.A) (Y := Y) d.B.ψ dd d.χ om S l ∧ _root_.PositivityTheory.SiegelWeilFormula.Ald.Res_k d h b j dd om l
theorem ldEx_of_leaves_k (h1 : _root_.PositivityTheory.SiegelWeilFormula.Ald.YFrame_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.Ald.JEx_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.Ald.KStd_k) (h4 : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k) (h5 : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k) : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.LDEx_k := by
  intro hT hA F E _ _ _ _ _ σ d hn
  have h : (d.n - 1) + 1 = d.n := by omega
  have hn1 : 1 ≤ d.n - 1 := by omega
  obtain ⟨Y, b, ε, hs, hb, e1, e2⟩ := h1 F E σ d (d.n - 1) h hn1
  obtain ⟨j, hj⟩ := h2 F E σ d (d.n - 1) h Y b ε e1 e2
  obtain ⟨κ, _, dd, om, S, l, hd, hr⟩ := h5 hT hA F E σ d (d.n - 1) h Y b j hn1 hs hb ⟨ε, e1, e2⟩ hj
  let L0 : _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d :=
    { n := d.n - 1, Y := Y, κ := κ, dd := dd, om := om, S := S, l := l, b := b, K := d.K.comap j, a := fun x => d.a (j x),
      ok := ⟨d.ok.good, d.ok.hm, hn1, d.ok.aniso, hs, d.ok.hecke, d.ok.res, hd, hb, h3 F E σ d _ h Y b j hb hj,
        h4 F E σ d _ h Y b j hn1 hs hb hj, d.ok.haar, d.ok.dom⟩ }
  exact ⟨{ toLiftedSchrodingerDatum := L0, i₀ := i0 h, em := em0 h, inj := em0_injective h, rng := ne_last_iff_mem_range h, j := j, cont := hj.1,
             j_in := hj.2.1, j_out := hj.2.2, res := hr }⟩
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldMSpec
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def ChartFacts_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
    (∀ w', (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e (emb h b d.b w') =
      (Sum.elim (dd'.e w').1 (0 : Fin d.m × Fin 2 → AF F), Sum.elim (dd'.e w').2 (0 : Fin d.m × Fin 2 → AF F))) ∧
    (∀ u v : Fin d.m × Fin 2 → AF F, ∃ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w =
      (Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) u, Sum.elim (0 : Fin d.m × Fin n × Fin 2 → AF F) v)) ∧
    (∀ g w, ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).1 ∘ Sum.inl = 0 →
      ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w).2 ∘ Sum.inl = 0 → actB (cA σ) (j g) w = w) ∧
    (∀ g (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), actB (cA σ) (j g) (emb h b d.b w') = emb h b d.b (actB (cA σ) g w')) ∧
    ∀ (u : UA σ d.A.J) (w' : Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)), mat u * emb h b d.b w' = emb h b d.b (mat u * w')
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSiegelC
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem jPar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {n : ℕ} (h : n + 1 = d.n) {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    {j : G2 σ Y →* d.G} (hj : _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j) (p : G2 σ Y) (t : GL (Fin n) (AE F E))
    (hpt : p.1.1 * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * t.1) :
    ∃ t' : GL (Fin d.n) (AE F E), (j p).1.1 * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * t'.1 ∧
      Matrix.GeneralLinearGroup.det t' = Matrix.GeneralLinearGroup.det t := by
  obtain ⟨tb, hTb⟩ := frame_fromRows hb
  obtain ⟨td, hTd⟩ := frame_fromRows d.ok.frame
  set P := inFrame b p with hPdef
  set R0 := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (0 : Matrix (Fin n) (Fin n) (AE F E)) with hR0
  set R0N := Matrix.fromRows (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) with hR0N
  set A : Matrix (Fin n) (Fin n) (AE F E) := incM F (tb⁻¹).1 * t.1 * incM F tb.1 with hA
  have hDn := diag_of_frame b tb hTb
  have hDN := diag_of_frame d.b td hTd
  have hp := mat_of_inFrame b p
  have hP : P * R0 = R0 * A := by
    have e := hpt
    rw [hp, hDn] at e
    have e2 : incM F b.1 * (P * R0) * incM F (tb⁻¹).1 = incM F b.1 * (R0 * A) * incM F (tb⁻¹).1 := by
      rw [hA]
      calc incM F b.1 * (P * R0) * incM F (tb⁻¹).1
          = incM F b.1 * P * incM F (b⁻¹).1 * (incM F b.1 * R0 * incM F (tb⁻¹).1) := by
            simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
        _ = incM F b.1 * R0 * incM F (tb⁻¹).1 * t.1 := e
        _ = incM F b.1 * (R0 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1)) * incM F (tb⁻¹).1 := by
            simp only [Matrix.mul_assoc, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one]
    have e3 := congrArg (fun X => incM F (b⁻¹).1 * X * incM F tb.1) e2
    simpa only [Matrix.mul_assoc, cancel_l, cancel_l', incM_mul_inv, incM_inv_mul, Matrix.mul_one] using e3
  have hblk := blk_fromRows h P A hP
  have hjp : inFrame d.b (j p) = blk h P 1 := eq_blk h _ _ (hj.2.1 p) (hj.2.2 p)
  have hjm := mat_of_inFrame d.b (j p)
  rw [hjp] at hjm
  set blkA := (Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (AE F E)).submatrix (eI h) (eI h)
    with hblkA
  set T : Matrix (Fin d.n) (Fin d.n) (AE F E) := incM F td.1 * blkA * incM F (td⁻¹).1 with hT
  have hdet : T.det = t.1.det := by
    rw [hT, det_conj, hblkA, det_blkA, hA, det_conj']
  have hu : IsUnit T.det := by
    rw [hdet, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  refine ⟨Matrix.nonsingInvUnit T hu, ?_, ?_⟩
  · show (j p).1.1 * _ = _ * T
    rw [hjm, hDN]
    calc incM F d.b.1 * blk h P 1 * incM F (d.b⁻¹).1 * (incM F d.b.1 * R0N * incM F (td⁻¹).1)
        = incM F d.b.1 * (blk h P 1 * R0N) * incM F (td⁻¹).1 := by simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
      _ = incM F d.b.1 * (R0N * blkA) * incM F (td⁻¹).1 := by rw [hblk]
      _ = incM F d.b.1 * R0N * incM F (td⁻¹).1 * T := by
          rw [hT]; simp only [Matrix.mul_assoc, cancel_l, incM_mul_inv, incM_inv_mul, Matrix.mul_one]
  · ext
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopChiW
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.uW (w : InfinitePlace F) (z : ℂ) : AE F E :=
  (Place.exists_sec d.cm d.B.emb).choose (Function.update (fun _ => 1) w z) + finOne F • 1
def _root_.PositivityTheory.SiegelWeilFormula.SD_k.chiW (w : InfinitePlace F) (z : ℂ) : ℂ := if h : IsUnit (d.uW w z) then ((d.χ h.unit : Circle) : ℂ) else 1
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end

