module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def yrotM (n : ℕ) (s : ℤˣ) (t : ℝ) : M2 n :=
  Matrix.fromBlocks ((Real.cos t : ℂ) • 1) ((((s : ℤ) : ℂ) * Real.sin t) • 1) ((-(((s : ℤ) : ℂ) * Real.sin t)) • 1)
    ((Real.cos t : ℂ) • 1)

theorem yrotM_mul (n : ℕ) (s : ℤˣ) (t t' : ℝ) : yrotM n s t * yrotM n s t' = yrotM n s (t + t') := by
  rcases Int.units_eq_one_or s with rfl | rfl <;>
  · simp only [yrotM, Matrix.fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      ← add_smul]
    refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;>
    · congr 1
      push_cast [Real.cos_add, Real.sin_add]
      ring

theorem yrotM_zero (n : ℕ) (s : ℤˣ) : yrotM n s 0 = 1 := by
  simp [yrotM, Matrix.fromBlocks_one]

theorem yrotM_ct (n : ℕ) (s : ℤˣ) (t : ℝ) : (yrotM n s t)ᴴ = yrotM n s (-t) := by
  simp only [yrotM, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Real.cos_neg, Real.sin_neg]
  refine Matrix.fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;>
  · congr 1
    simp [← Complex.cos_conj, ← Complex.sin_conj, Complex.conj_ofReal]

theorem JJ_comm_yrotM (n : ℕ) (s : ℤˣ) (t : ℝ) : JJ n * yrotM n s t = yrotM n s t * JJ n := by
  simp [JJ, yrotM, Matrix.fromBlocks_multiply]

theorem inK_yrotM (n : ℕ) (s : ℤˣ) (t : ℝ) : InK (yrotM n s t) := by
  have h1 : (yrotM n s t)ᴴ * yrotM n s t = 1 := by
    rw [yrotM_ct, yrotM_mul, neg_add_cancel, yrotM_zero]
  refine ⟨?_, h1⟩
  show (yrotM n s t)ᴴ * JJ n * yrotM n s t = JJ n
  rw [Matrix.mul_assoc, JJ_comm_yrotM, ← Matrix.mul_assoc, h1, Matrix.one_mul]

def yrot (n : ℕ) (s : ℤˣ) (t : ℝ) : GR n :=
  ⟨⟨yrotM n s t, yrotM n s (-t), by rw [yrotM_mul, add_neg_cancel, yrotM_zero],
    by rw [yrotM_mul, neg_add_cancel, yrotM_zero]⟩, (inK_yrotM n s t).1⟩

theorem mR_yrot (n : ℕ) (s : ℤˣ) (t : ℝ) : mR (yrot n s t) = yrotM n s t := rfl

variable {d : SD σ}

def rot (R : RD d) (t : ℝ) : d.G :=
  (((Finset.univ : Finset (InfinitePlace F)).toList).map fun w => R.ι w (yrot d.n (R.sg w) t)).prod

theorem rot_mem (R : RD d) (t : ℝ) : rot R t ∈ d.K := by
  unfold rot
  refine d.K.list_prod_mem fun x hx => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact KSplitW.iota_mem_K d R w _ (by rw [mR_yrot]; exact inK_yrotM _ _ _)

theorem exists_tw (R : RD d) (W : Mx F E d.m d.n) :
    ∃ W' : Mx F E d.m d.n, finOne F • W' = 0 ∧ ∀ w, d.cw w W' = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W := by
  obtain ⟨s, -, hs1, hs2, -, -⟩ := Place.exists_sec d.cm d.B.emb
  refine ⟨s (fun w => -(((R.sg w : ℤ) : ℂ) * R.ζ)) • W, ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← smul_mul_assoc, hs2, zero_mul]
  · ext i j
    simp only [SD.cw, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hs1]

def tw (R : RD d) (W : Mx F E d.m d.n) : Mx F E d.m d.n := (exists_tw R W).choose

def vline (R : RD d) (W : Mx F E d.m d.n) (z : ℂ) : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  (realAd F z.re • W) * (incM F d.b.1.toCols₂)ᵀ + (realAd F z.im • tw R W) * (incM F d.b.1.toCols₁)ᵀ

theorem finOne_mul_fst (a : AF F) : (finOne F * a).1 = 0 := by
  show (0 : InfiniteAdeleRing F) * a.1 = 0
  exact zero_mul _

theorem finOne_mul_snd (a : AF F) : (finOne F * a).2 = a.2 := by
  show (1 : Af F) * a.2 = a.2
  exact one_mul _

theorem finOne_mul_eq_zero_iff (a : AF F) : finOne F * a = 0 ↔ a.2 = 0 := by
  constructor
  · intro h
    have := congrArg Prod.snd h
    rw [finOne_mul_snd] at this
    exact this
  · intro h
    exact Prod.ext (finOne_mul_fst a) ((finOne_mul_snd a).trans h)

theorem fin_eq_zero_iff (X : Mx F E d.m d.n) : fin d X = 0 ↔ finOne F • X = 0 := by
  set bas := Algebra.TensorProduct.basis (AF F) d.bs
  have key : ∀ z : AE F E, finOne F • z = 0 ↔ ∀ l, (bas.repr z l).2 = 0 := by
    intro z
    rw [← bas.repr.injective.eq_iff, LinearEquiv.map_smul, LinearEquiv.map_zero]
    simp only [Finsupp.ext_iff, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
      finOne_mul_eq_zero_iff]
  constructor
  · intro h
    ext i j
    simp only [Matrix.smul_apply, Matrix.zero_apply]
    refine (key _).2 fun l => ?_
    exact congrFun h (i, j, l)
  · intro h
    funext ⟨i, j, l⟩
    exact (key (X i j)).1 (by simpa using congrFun (congrFun h i) j) l

end PositivityTheory.SiegelWeilFormula.KFP

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.MemLpSchM
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem memLpSchA {κ : Type} [Fintype κ] (m : MeasurableSpace (κ → AF F)) (hm : m = borel _)
    (μ : @Measure (κ → AF F) m) (hμ : @Measure.IsAddHaarMeasure _ _ _ m μ) {φ : (κ → AF F) → ℂ}
    (hφ : φ ∈ schA F κ) : MemLp φ 2 μ := by
  subst hm
  exact GlobalTheory.WeilM.schA_memLp_two F κ μ hμ φ hφ

theorem memLp_schM (d : SD σ) (ν : Measure (Mx F E d.m d.n)) (hν : ν.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) : MemLp f 2 ν := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Fin d.m × Fin d.n × Fin 2 → AF F) := Pi.borelSpace
  let e : (Fin d.m × Fin d.n × Fin 2 → AF F) ≃ᵐ Mx F E d.m d.n := (KFock.cmbE d).toHomeomorph.toMeasurableEquiv
  haveI : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (KFock.cmbE d).symm
  have h1 : MemLp (f ∘ e) 2 (Measure.map e.symm ν) := by
    have hf' : f ∘ d.cmb ∈ schA F (Fin d.m × Fin d.n × Fin 2) := Submodule.mem_comap.mp hf
    exact memLpSchA _ BorelSpace.measurable_eq _ inferInstance hf'
  have h2 := (e.memLp_map_measure_iff).2 h1
  rwa [MeasurableEquiv.map_map_symm] at h2

variable {d : SD σ}

def TL (d : SD σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' := KFock.T_add d
  map_smul' a Φ := KFock.T_smul d a Φ

theorem rho_smul (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • φ) = c • d.dd.rho d.B.ψ w φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem B_rel' (hT : TAll) (hU : TUnit) {ν : Measure (Mx F E d.m d.n)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0)
    (v : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * B ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  have hrho : ∀ w, ∀ φ ∈ d.sch, d.dd.rho d.B.ψ w φ ∈ d.sch := fun w φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ hψ d.κ _ φ hφ
  have hpow : ∀ i : ℕ, d.om (k ^ i) Ω = χ ^ i • Ω := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, map_mul, Module.End.mul_apply, hk, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hact : ∀ i : ℕ, actB (cA σ) (k ^ i) (actB (cA σ) (k⁻¹ ^ i) v) = v := by
    intro i
    have e1 : k ^ i * k⁻¹ ^ i = 1 := by rw [inv_pow, mul_inv_cancel]
    simp only [actB]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, e1]
    simp
  set Ψ := d.dd.rho d.B.ψ v Ω with hΨdef
  have hΨ : Ψ ∈ d.sch := hrho v Ω hΩ
  have hterm : ∀ i : ℕ, (star χ)⁻¹ ^ i * B ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) =
      B ν (d.om (k ^ i) Φ) Ψ := by
    intro i
    have h1 := hU F E σ d ν hν (k ^ i) Φ hΦ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      (hrho (actB (cA σ) (k⁻¹ ^ i) v) Ω hΩ)
    have h2 : d.om (k ^ i) (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = χ ^ i • Ψ := by
      rw [hS.impl _ _ Ω hΩ, hact, hpow, rho_smul]
    rw [h2, KFock.T_smul] at h1
    unfold B
    rw [← h1]
    have e3 : ∀ X, d.T (d.om (k ^ i) Φ) X * star ((χ ^ i • d.T Ψ) X) =
        star χ ^ i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) := by
      intro X
      rw [Pi.smul_apply, smul_eq_mul, star_mul', star_pow]
      ring
    simp_rw [e3]
    rw [integral_const_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (star_ne_zero.2 hχ), one_pow, one_mul]
  have hint : ∀ i : ℕ, Integrable (fun X => d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ν := by
    intro i
    have hA := memLp_schM d ν hν ((hT.1 F E σ d).1 (d.om (k ^ i) Φ) (hS.pres (k ^ i) Φ hΦ))
    have hB := (memLp_schM d ν hν ((hT.1 F E σ d).1 Ψ hΨ)).star
    exact hA.integrable_mul hB
  calc ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i * (star χ)⁻¹ ^ i * B ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * B ν (d.om (k ^ i) Φ) Ψ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, hterm]
    _ = ∫ X, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ∂ν := by
        unfold B
        rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]
        simp_rw [integral_const_mul]
    _ = ∫ X, TL d (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ) X * star (d.T Ψ X) ∂ν := by
        congr 1
        funext X
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        rfl
    _ = 0 := by
        rw [hq, map_zero]
        simp

end PositivityTheory.SiegelWeilFormula.KFP

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Spf
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

abbrev spf (d : SD σ) (a b : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : AF F :=
  symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.A.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) d.Y.J)) a b

end PositivityTheory.SiegelWeilFormula.KFP

end
end

