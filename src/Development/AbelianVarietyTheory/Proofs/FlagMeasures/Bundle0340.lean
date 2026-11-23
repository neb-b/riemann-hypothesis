module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsOfFixedInt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureGaussian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0307
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjLinearIsometryCompactUnitaryTypeWeylMo
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMeanOfWeilSiegel
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Count GlobalTheory.GaussMean
open Formalism.MainNotions.S (AutInst uMat)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SiegelWeilMean

theorem lintegral_eq_of_meanC {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (hS : μ S < ⊤)
    (G : α → ENNReal) (hG : Measurable G) (hfin : ∫⁻ a in S, G a ∂μ < ⊤) (c : ℝ)
    (h : meanC μ S (fun a => ((G a).toReal : ℂ)) = (c : ℂ)) :
    ∫⁻ a in S, G a ∂μ = μ S * ENNReal.ofReal c := by
  by_cases h0 : μ S = 0
  · rw [h0, zero_mul, setLIntegral_measure_zero _ _ h0]
  have h1 : (μ S).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, hS.ne⟩
  unfold meanC at h
  beta_reduce at h
  rw [integral_complex_ofReal, integral_toReal hG.aemeasurable (ae_lt_top hG hfin.ne), Complex.real_smul] at h
  have h2 : (μ S).toReal⁻¹ * (∫⁻ a in S, G a ∂μ).toReal = c := by exact_mod_cast h
  rw [← h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin.ne, ← mul_assoc,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_toReal hS.ne, ENNReal.mul_inv_cancel h0 hS.ne, one_mul]

theorem exists_transport (I : AutInst) (T : HA (AF I.F) I.cm.sig I.J ≃ₜ* I.GA)
    (hT : ∀ h, (show HR (AF I.F) I.cm.sig I.J from h) ∈ HFinIn (AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset)
    (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund) :
    ∃ (μ : Measure (HA (AF I.F) I.cm.sig I.J)) (S : Set (HA (AF I.F) I.cm.sig I.J)), μ.IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF I.F) I.cm.sig I.J) S μ ∧ Measurable T ∧ μ S = I.muA μf fund ∧
      ∀ f : I.GA → ENNReal, ∫⁻ h in S, f (T h) ∂μ = ∫⁻ x in fund, f x ∂(I.muA μf) := by
  obtain ⟨_, _, _, -⟩ := GlobalTheory.CongTop.adelic_topology I
  haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => by unfold Formalism.REAL.muG; infer_instance
  haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  haveI : (I.muA μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  haveI : BorelSpace I.GA := inferInstance
  haveI : BorelSpace (HA (AF I.F) I.cm.sig I.J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF I.F) I.cm.sig I.J) := inferInstance
  obtain ⟨Γ, hΓ, -, -, hF⟩ := GlobalTheory.RatDiscrete.rational_points I
  let e : HA (AF I.F) I.cm.sig I.J ≃ᵐ I.GA := T.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e ((I.muA μf).map e.symm) (I.muA μf) :=
    (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
  have hmem : ∀ g : Γ, (show HR (AF I.F) I.cm.sig I.J from T.symm g) ∈ HFinIn (AF I.F) I.cm.sig I.J := fun g => by
    refine (hT (T.symm g)).2 ?_
    have : T (T.symm g) = g := T.apply_symm_apply _
    exact this.symm ▸ (hΓ ▸ g.2 : g.1 ∈ I.GFset)
  refine ⟨(I.muA μf).map e.symm, e ⁻¹' fund, T.symm.isHaarMeasure_map _, ?_, e.measurable,
    hp.measure_preimage_equiv _, fun f => hp.setLIntegral_comp_preimage_emb e.measurableEmbedding f _⟩
  refine (hF μf fund hfund).preimage_of_equiv hp.quasiMeasurePreserving
    (e := fun g => ⟨T.symm g, hmem g⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun g x => ?_
  · exact Subtype.ext (T.symm.injective (congrArg Subtype.val hab))
  · exact ⟨⟨T b.1, by rw [← SetLike.mem_coe, hΓ]; exact (hT _).1 b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩
  · change T (T.symm g * x) = g * T x
    rw [map_mul, T.apply_symm_apply]

theorem const_eq {ι κ : Type} [Fintype κ] (q : ι → ℝ) (hq : ∀ u, 0 < q u) (m : ι → ℤ)
    (hm : (Function.support m).Finite) (a : ι → ℝ) (Lv : ℝ) (ha : HasProd a Lv⁻¹) (lam g : κ → ℝ)
    (hlam : ∀ v, lam v ≠ 0) (w : ℝ) (hw : 0 < w) (n f : ℕ) (hf : Fintype.card κ = f)
    (hp : ∏ᶠ u, q u ^ m u = (2 * w) ^ f * ∏ v, |lam v|) :
    ((∏ v, 2 ^ n * |lam v| ^ ((n : ℝ) - 1 / 2) * g v : ℝ) : ℂ) *
      ∏' u, (((q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) * a u : ℝ) : ℂ) =
      (((2 * w) ^ ((f : ℝ) / 2) * (w ^ (n * f))⁻¹ / Lv * ∏ v, g v : ℝ) : ℂ) := by
  have hout : ∀ u ∉ hm.toFinset, m u = 0 := fun u hu => by simpa using hu
  have h1 : HasProd (fun u => (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)))
      (∏ u ∈ hm.toFinset, (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ))) :=
    hasProd_prod_of_ne_finset_one fun u hu => by simp [hout u hu]
  have h2 : ∏ u ∈ hm.toFinset, (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) =
      ((2 * w) ^ f * ∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) := by
    rw [Real.finsetProd_rpow _ _ (fun u _ => (zpow_pos (hq u) _).le) _, ← hp,
      finprod_eq_prod_of_mulSupport_subset _ (s := hm.toFinset)]
    intro u hu
    by_contra h
    exact hu (by simp [hout u h])
  have h3 := (h1.mul ha).map Complex.ofRealHom Complex.continuous_ofReal
  have h4 : ∏' u, (((q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) * a u : ℝ) : ℂ) = _ := h3.tprod_eq
  rw [h4, h2, Complex.ofRealHom_eq_coe, ← Complex.ofReal_mul]
  congr 1
  have hl : 0 < ∏ v, |lam v| := Finset.prod_pos fun v _ => abs_pos.2 (hlam v)
  have h5 : (∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2) * (∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) = 1 := by
    rw [← Real.rpow_add hl]; simp
  have h6 : ((2 * w) ^ f) ^ ((1 / 2 : ℝ) - (n : ℝ)) = (2 * w) ^ ((f : ℝ) / 2) * ((2 * w) ^ (n * f))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast (2 * w) (n * f),
      ← Real.rpow_neg (by positivity), ← Real.rpow_add (by positivity)]
    congr 1; push_cast; ring
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf,
    Real.finsetProd_rpow _ _ (fun v _ => abs_nonneg _) _, Real.mul_rpow (by positivity) hl.le, h6, mul_pow, pow_mul 2]
  have : (2 ^ n : ℝ) ^ f ≠ 0 := by positivity
  have h7 : (∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) = ((∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2))⁻¹ :=
    eq_inv_of_mul_eq_one_right h5
  have : (∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2) ≠ 0 := by positivity
  rw [h7]
  field_simp


end GlobalTheory.SiegelWeilMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetUnipotentOnBesselModels
section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TypeAsm.CovTrans

open Formalism.L2.SG.LocWSOf

section Gen

variable {n m : ℕ} {ε : Fin n → Bool}

theorem conj_cancel (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (h : Q * Qi = 1)
    (A : Matrix (Fin n) (Fin n) ℂ) : Q * (Qi * A * Q) * Qi = A := by
  calc Q * (Qi * A * Q) * Qi = (Q * Qi) * A * (Q * Qi) := by simp only [Matrix.mul_assoc]
    _ = A := by rw [h, Matrix.one_mul, Matrix.mul_one]

theorem inUJ_conj (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) (H : Matrix (Fin m) (Fin m) ℂ)
    (hQ : Q * Qi = 1) (hH : Qᴴ * Formalism.REAL.Jm ε * Q = H) (x : Matrix (Fin m) (Fin m) ℂ) (hx : xᴴ * H * x = H) :
    Formalism.REAL.inUJ ε (Q * x * Qi) := by
  unfold Formalism.REAL.inUJ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc Qiᴴ * (xᴴ * Qᴴ) * Formalism.REAL.Jm ε * (Q * x * Qi) = Qiᴴ * (xᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * x) * Qi := by
        simp only [Matrix.mul_assoc]
    _ = Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi := by rw [hH, hx, ← hH]
    _ = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hQ]; simp

theorem inv_mul_of_inUJ (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.REAL.inUJ ε M) :
    Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε * M = 1 := by
  calc Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε * (Mᴴ * Formalism.REAL.Jm ε * M) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h]; exact Formalism.REAL.Jm_mul_self ε

def mkUJ (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.REAL.inUJ ε M) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε, mul_eq_one_comm.1 (inv_mul_of_inUJ M h), inv_mul_of_inUJ M h⟩, h⟩

def mkUJ' (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.UJ ε :=
  if h : Formalism.REAL.inUJ ε M then mkUJ M h else 1

theorem mkUJ'_val (M : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.REAL.inUJ ε M) :
    Formalism.MainNotions.S.uMat (mkUJ' ε M) = M := by
  rw [mkUJ', dite_eq_left h]; rfl

theorem mkUJ'_coe (γ : Formalism.REAL.UJ ε) :
    mkUJ' ε (((γ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) = γ := by
  apply Subtype.ext; apply Units.ext
  exact mkUJ'_val _ γ.2

end Gen

section Tr

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

theorem trI_of (x : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix.of (trI C x τ) = C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ :=
  rfl

theorem vOf_pl (v : InfinitePlace X.B.I.F) : vOf X (X.pl v) = v := X.pl.symm_apply_apply v

theorem trI_mul (a b : X.B.I.Ginf) : trI C (a * b) = GlobalTheory.DegVol.mulP (trI C a) (trI C b) := by
  funext τ
  apply Matrix.of.injective
  show Matrix.of (trI C (a * b) τ) = Matrix.of (trI C a τ) * Matrix.of (trI C b τ)
  rw [trI_of, trI_of, trI_of]
  rw [show Formalism.MainNotions.S.uMat ((a * b) (vOf X τ)) = Formalism.MainNotions.S.uMat (a (vOf X τ)) * Formalism.MainNotions.S.uMat (b (vOf X τ)) from rfl]
  generalize Formalism.MainNotions.S.uMat (a (vOf X τ)) = A
  generalize Formalism.MainNotions.S.uMat (b (vOf X τ)) = B
  have h := (C.isT τ).2.1
  calc C.Qi τ * (A * B) * C.Q τ = C.Qi τ * A * (C.Q τ * C.Qi τ) * B * C.Q τ := by
        rw [h]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = C.Qi τ * A * C.Q τ * (C.Qi τ * B * C.Q τ) := by simp only [Matrix.mul_assoc]

theorem trI_inj : Function.Injective (trI C) := by
  intro a b h
  funext v
  have e := congrArg Matrix.of (congrFun h (X.pl v))
  rw [trI_of, trI_of] at e
  have e2 : C.Q (X.pl v) * (C.Qi (X.pl v) * Formalism.MainNotions.S.uMat (a (vOf X (X.pl v))) * C.Q (X.pl v)) * C.Qi (X.pl v) =
      C.Q (X.pl v) * (C.Qi (X.pl v) * Formalism.MainNotions.S.uMat (b (vOf X (X.pl v))) * C.Q (X.pl v)) * C.Qi (X.pl v) := by rw [e]
  rw [conj_cancel _ _ (C.isT _).2.1, conj_cancel _ _ (C.isT _).2.1, vOf_pl] at e2
  exact Subtype.ext (Units.ext e2)

end Tr

section Back

variable {D : D7} {X : HidaSetting D} (C : Choice X 1)

def back (x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : X.B.I.Ginf :=
  fun v => mkUJ' (X.B.I.ε v) (C.Q (X.pl v) * Matrix.of (x (X.pl v)) * C.Qi (X.pl v))

def Sg : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  {x | ∀ τ, Formalism.REAL.inUJ (X.B.I.ε (vOf X τ)) (C.Q τ * Matrix.of (x τ) * C.Qi τ)}

theorem back_trI (a : X.B.I.Ginf) : back C (trI C a) = a := by
  funext v
  unfold back
  rw [trI_of, conj_cancel _ _ (C.isT _).2.1, vOf_pl]
  exact mkUJ'_coe _

theorem trI_back {x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS} (hx : x ∈ Sg C) : trI C (back C x) = x := by
  funext τ
  apply Matrix.of.injective
  rw [trI_of]
  unfold back
  have h := hx τ
  simp only [vOf, Equiv.apply_symm_apply] at h ⊢
  rw [mkUJ'_val _ h]
  calc C.Qi τ * (C.Q τ * Matrix.of (x τ) * C.Qi τ) * C.Q τ = (C.Qi τ * C.Q τ) * Matrix.of (x τ) * (C.Qi τ * C.Q τ) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.of (x τ) := by rw [(C.isT τ).1, Matrix.one_mul, Matrix.mul_one]

theorem range_trI : Set.range (trI C) = Sg C := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩ τ
    rw [trI_of]
    rw [conj_cancel _ _ (C.isT _).2.1]
    exact (a (vOf X τ)).2
  · intro hx
    exact ⟨back C x, trI_back C hx⟩

theorem cont_uMat {n : ℕ} {ε : Fin n → Bool} : Continuous (fun γ : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat γ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem measurable_trI : Measurable (trI C) := by
  refine Measurable.of_eval (fun τ => ?_)
  have hc : Continuous (fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (C.Qi τ * Formalism.MainNotions.S.uMat γ * C.Q τ) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    (continuous_const.matrix_mul cont_uMat).matrix_mul continuous_const
  exact hc.measurable.comp (measurable_pi_apply (vOf X τ))

theorem measurableSet_Sg : MeasurableSet (Sg C) := by
  have : Sg C = ⋂ τ, (fun x : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => x τ) ⁻¹'
      {y : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | Formalism.REAL.inUJ (X.B.I.ε (vOf X τ)) (C.Q τ * Matrix.of y * C.Qi τ)} := by
    ext x; simp [Sg]
  rw [this]
  refine MeasurableSet.iInter (fun τ => measurable_pi_apply τ ?_)
  apply IsClosed.measurableSet
  unfold Formalism.REAL.inUJ
  have hm : Continuous (fun y : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => C.Q τ * Matrix.of y * C.Qi τ) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact isClosed_eq ((hm.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hm) continuous_const

theorem measurable_mkUJ' {n m : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (fun y : (Fin m → Fin m → ℂ) => mkUJ' ε (Q * Matrix.of y * Qi)) := by
  set S : Set (Fin m → Fin m → ℂ) := {y | Formalism.REAL.inUJ ε (Q * Matrix.of y * Qi)} with hS
  have hm : Continuous (fun y : (Fin m → Fin m → ℂ) => Q * Matrix.of y * Qi) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hSc : IsClosed S := by
    unfold Formalism.REAL.inUJ at hS
    rw [hS]
    exact isClosed_eq ((hm.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hm) continuous_const
  have hf : Continuous (fun y : S => mkUJ (ε := ε) (Q * Matrix.of (y : Fin m → Fin m → ℂ) * Qi) y.2) := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    refine ⟨hm.comp continuous_subtype_val, ?_⟩
    exact ((continuous_const.matrix_mul (hm.comp continuous_subtype_val).matrix_conjTranspose).matrix_mul
      continuous_const)
  have e : (fun y : (Fin m → Fin m → ℂ) => mkUJ' ε (Q * Matrix.of y * Qi)) =
      fun y => if hy : y ∈ S then mkUJ (ε := ε) (Q * Matrix.of y * Qi) hy else (fun _ : (Sᶜ : Set _) => (1 : Formalism.REAL.UJ ε)) ⟨y, hy⟩ := by
    funext y; rfl
  rw [e]
  exact Measurable.dite hf.measurable measurable_const hSc.measurableSet

theorem measurable_back : Measurable (back C) := by
  refine Measurable.of_eval (fun v => ?_)
  exact (measurable_mkUJ' _ _ _).comp (measurable_pi_apply (X.pl v))

theorem measEmb_trI : MeasurableEmbedding (trI C) :=
  MeasurableEmbedding.of_measurable_inverse (measurable_trI C) (by rw [range_trI]; exact measurableSet_Sg C)
    (measurable_back C) (back_trI C)

end Back

theorem isFund_trI : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    GlobalTheory.DegVol.IsFund (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u)
      (GlobalTheory.DegVol.RP D.R.k D.R.rS (fun _ => 1)) (trI C '' Y.FN u) := by
  intro D X Y u C
  have hsub : ∀ a b, a ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u → b ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u →
      a * b⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := by
    intro a b ha hb
    rw [← Formalism.L2.SG.Pf.NOsub_coe X u Y.hK] at ha hb ⊢
    exact Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb)
  obtain ⟨hFm, hcov, hstr⟩ := Y.FN_fund u
  refine ⟨(measEmb_trI C).measurableSet_image.2 hFm, fun x hx => ?_⟩
  have hxS : x ∈ Sg C := fun τ =>
    inUJ_conj _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _ (hx τ).1.1
  have hy : trI C (back C x) = x := trI_back C hxS
  obtain ⟨s, hs, hsF⟩ := hcov (back C x)
  refine ⟨trI C s, ⟨⟨s, hs, rfl⟩, ?_⟩, ?_⟩
  · rw [← hy, ← trI_mul]
    exact ⟨_, hsF, rfl⟩
  · rintro m ⟨⟨s', hs', rfl⟩, ⟨f, hf, hfe⟩⟩
    rw [← hy, ← trI_mul] at hfe
    have e : f = s' * back C x := trI_inj C hfe
    rw [e] at hf
    have h1 := hstr _ hsF (s' * s⁻¹) (hsub _ _ hs' hs) (by rwa [mul_assoc, inv_mul_cancel_left])
    rw [mul_inv_eq_one.1 h1]

end GlobalTheory.TypeAsm.CovTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.TenTypes

theorem fockF_eq_fockL {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockL g f := by
  classical
  rw [Formalism.L2.DIV.fockL_apply,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset Finset.subset_union_left ?_]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Formalism.L2.DIV.mfact]
    ring
  · intro m _ hm
    rw [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]

private theorem star_fockF_comm {σ : Type} (f g : MvPolynomial σ ℂ) :
    star (Formalism.REAL.fockF f g) = Formalism.REAL.fockF g f := by
  rw [fockF_eq_fockL g f, Formalism.L2.DIV.fockL_apply]
  unfold Formalism.REAL.fockF Formalism.L2.DIV.fockS
  rw [star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Formalism.L2.DIV.mfact, star_mul', star_star, star_natCast]

theorem nfAll_add_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (p p' q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (p + p') q = nfAll lam p q + nfAll lam p' q := by
  unfold nfAll
  rw [fockF_eq_fockL (p + p') q, map_add (f := _), ← fockF_eq_fockL p q, ← fockF_eq_fockL p' q, add_div]

theorem nfAll_smul_left {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (c : ℂ) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam (c • p) q = c * nfAll lam p q := by
  unfold nfAll
  rw [fockF_eq_fockL (c • p) q, map_smul, ← fockF_eq_fockL p q, smul_eq_mul, mul_div_assoc]

theorem nfAll_symm {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam q p = star (nfAll lam p q) := by
  unfold nfAll
  rw [← starRingEnd_apply, map_div₀, map_prod]
  simp only [starRingEnd_apply, star_fockF_comm]

theorem eval_rowAct {n : ℕ} (g x : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : Fin n × Fin n => x v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      MvPolynomial.eval (fun v : Fin n × Fin n => (g * x) v.1 v.2) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    have hX : MvPolynomial.eval (fun w : Fin n × Fin n => x w.1 w.2)
        (Formalism.GradedWeylDivisibility.rowAct ℂ g (MvPolynomial.X v)) = (g * x) v.1 v.2 := by
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
    simp only [map_mul, hp, hX, MvPolynomial.eval_X]

theorem factor_eq {n : ℕ} (m o a b : Matrix (Fin n) (Fin n) ℂ) (hm : m ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ho : IsUnit o.det) (s : ℤ) (p : MvPolynomial (Fin n × Fin n) ℂ) (hab : a = o * m * o⁻¹ * b) :
    (o⁻¹ * a).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * a) v.1 v.2)
        ((m.det ^ (-s)) • Formalism.GradedWeylDivisibility.rowAct ℂ mᴴ p) =
      (o⁻¹ * b).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * b) v.1 v.2) p := by
  have hmm : mᴴ * m = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hm
    rwa [Matrix.star_eq_conjTranspose] at this
  have hdet : m.det ≠ 0 := by
    have := congrArg Matrix.det hmm
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  have key : o⁻¹ * a = m * (o⁻¹ * b) := by
    rw [hab]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc o⁻¹ o, Matrix.nonsing_inv_mul o ho, Matrix.one_mul]
  rw [key, Matrix.det_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_rowAct mᴴ (m * (o⁻¹ * b)) p, ← Matrix.mul_assoc mᴴ m, hmm, Matrix.one_mul, mul_zpow, _root_.zpow_neg]
  have e : m.det ^ s * (m.det ^ s)⁻¹ = 1 := mul_inv_cancel₀ (zpow_ne_zero s hdet)
  linear_combination
    ((o⁻¹ * b).det ^ s * MvPolynomial.eval (fun v : Fin n × Fin n => (o⁻¹ * b) v.1 v.2) p) * e

theorem tensor_dict : ∀ (ι : Type) [Fintype ι] (k n : ℕ) (h : k = n) (lam : ι → DomWeight n) (u : ι → Fin k → ℝ), (∀ τ (i : Fin k), u τ i = ((lam τ).w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (Vl : ι → Type) [∀ τ, NormedAddCommGroup (Vl τ)] [∀ τ, InnerProductSpace ℂ (Vl τ)] (πl : ∀ τ, Matrix (Fin k) (Fin k) ℂ → (Vl τ →L[ℂ] Vl τ)), (∀ τ, IsHCTypeU k (u τ) (πl τ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (tens : (∀ τ, Vl τ) → W), (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ → ∃ Jp : W →ₗ⋆[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, (∀ ξ, Jp ξ ∈ CSpan lam) ∧ (∀ p ∈ CSpan lam, ∃ ξ, Jp ξ = p) ∧ (∀ ξ η, nfAll lam (Jp η) (Jp ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ (m : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, m τ ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ A : W →L[ℂ] W, (∀ x, A (tens x) = tens (fun τ => πl τ ((m τ).submatrix (Fin.cast h) (Fin.cast h)) (x τ))) → ∀ (G o : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (o τ).det) → ∀ (ξ : W) (y y' : Frames G), IsTr (fun τ => o τ * m τ * (o τ)⁻¹) y' y → fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp (A ξ)) y = fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp ξ) y' := by
  intro ι _ k n h lam u hu Vl _ _ πl hπ W _ _ tens htens hspan
  have hj := fun τ => _root_.GlobalTheory.WeylConjType.exists_conj_weyl k n h (lam τ) (u τ) (hu τ) (Vl τ) (πl τ) (hπ τ)
  choose j hjmem hjonto hjnorm hjeq using hj
  obtain ⟨hten, hdef, hfn⟩ := _root_.GlobalTheory.FockTen.nfAll_ten ι n lam
  obtain ⟨Jp, hJa, hJn⟩ := _root_.GlobalTheory.exists_conjLinear_of_gram_eq W (MvPolynomial (ι × Fin n × Fin n) ℂ) (nfAll lam)
    (∀ τ, Vl τ) tens (fun x => ten fun τ => j τ (x τ)) (nfAll_add_left lam) (nfAll_smul_left lam)
    (nfAll_symm lam) hdef hspan (fun x x' => by
      show nfAll lam (ten fun τ => j τ (x' τ)) (ten fun τ => j τ (x τ)) = _
      rw [hten, htens]
      exact Finset.prod_congr rfl fun τ _ => hjnorm τ (x τ) (x' τ))
  have hall : ∀ ξ : W, ξ ∈ Submodule.span ℂ (Set.range tens) := fun ξ => by
    rw [hspan]; exact Submodule.mem_top
  refine ⟨Jp, ?_, ?_, hJn, ?_⟩
  · have hle : Submodule.span ℂ (Set.range tens) ≤ (CSpan lam).comap Jp := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      show Jp (tens x) ∈ CSpan lam
      rw [hJa x]
      exact Submodule.subset_span ⟨fun τ => j τ (x τ), fun τ => hjmem τ (x τ), rfl⟩
    intro ξ
    exact hle (hall ξ)
  · intro p hp
    unfold CSpan at hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨f, hf, rfl⟩ := hp
      choose x hx using fun τ => hjonto τ (f τ) (hf τ)
      refine ⟨tens x, ?_⟩
      rw [hJa x]
      show (ten fun τ => j τ (x τ)) = ten f
      congr 1
      funext τ
      exact hx τ
    | zero => exact ⟨0, map_zero Jp⟩
    | add p q _ _ hp hq =>
      obtain ⟨ξ, rfl⟩ := hp
      obtain ⟨η, rfl⟩ := hq
      exact ⟨ξ + η, map_add Jp ξ η⟩
    | smul c p _ hp =>
      obtain ⟨ξ, rfl⟩ := hp
      refine ⟨(starRingEnd ℂ c) • ξ, ?_⟩
      rw [map_smulₛₗ, starRingEnd_self_apply]
  · intro m hm A hA G o ho ξ y y' hy
    induction hall ξ using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [hA x, hJa, hJa, hfn, hfn]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hjeq τ (m τ) (hm τ) (x τ)]
      exact factor_eq (m τ) (o τ) (y.1 τ) (y'.1 τ) (hm τ) (ho τ) (shiftOf lam τ) (j τ (x τ)) (hy τ)
    | zero => simp
    | add z w _ _ hz hw => simp only [map_add (f := _), Pi.add_apply, hz, hw]
    | smul c z _ hz => simp only [map_smul, map_smulₛₗ, Pi.smul_apply, smul_eq_mul, hz]

end GlobalTheory.TenTypes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrameStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_rational_points_stabiliser_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → ∀ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) → (∀ γ : Gam X u, ∃ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) ∧ (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ (∀ g : GL (Fin (D.R.N 0)) D.host.E, g ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) → ∃ γ : Gam X u, (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g) ∧ ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E), (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g → sTil X wt (iotaI X u γ : X.B.I.Ginf) = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1 := by
  first | exact @GlobalTheory.transport_rational_points | exact GlobalTheory.transport_rational_points | (intros; apply GlobalTheory.transport_rational_points <;> assumption)
end

