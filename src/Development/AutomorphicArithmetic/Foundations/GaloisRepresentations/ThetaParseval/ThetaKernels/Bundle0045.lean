module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDFr
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem epsEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.EpsEx_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  refine ⟨ε, hε, ?_⟩
  have hss : ∀ x, σ (σ x) = x := PositivityTheory.ThKG.Tow.Levi.sig_sig d.cm
  have i : Fin d.n := ⟨0, d.ok.hn⟩
  have key : ∀ c : E, (∀ i j, σ (d.Y.J j i) = c * d.Y.J i j) → ((ε : ℤ) : E) = c := fun c hc => by
    have e := congrFun (congrFun (conjT_frame c d.Y.J hc hss d.b.1) (Sum.inl i)) (Sum.inr i)
    rw [hε] at e
    simpa [Matrix.fromBlocks] using e
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · refine Or.inl ⟨hA, ?_⟩
    have e := key (-1) fun i j => by rw [hY, neg_one_mul]
    have e' : ((ε : ℤ) : E) = ((-1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')
  · refine Or.inr ⟨hA, ?_⟩
    have e := key 1 fun i j => by rw [hY, one_mul]
    have e' : ((ε : ℤ) : E) = ((1 : ℤ) : E) := by rw [e]; push_cast; rfl
    exact Units.ext (by simpa using Int.cast_injective (α := E) e')
theorem frEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.FrEx_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun hA => ?_, fun hA => ?_⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    exact ⟨fr, sg, fun w => by rw [one_smul, hfr w]⟩
  · choose fr sg hfr using fun w => frame_of_sig (hA.sig w) d.ok.aniso
    refine ⟨fr, sg, fun w => ?_⟩
    rw [← hfr w, Matrix.mul_smul, Matrix.smul_mul]
end PositivityTheory.SiegelWeilFormula.Krd
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Glue
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def sc_k : (InfinitePlace F → ℂ) → AE F E := (Place.exists_sec d.cm d.B.emb).choose
theorem sc_cont_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d) := (Place.exists_sec d.cm d.B.emb).choose_spec.1
theorem sc_pi_k (x : InfinitePlace F → ℂ) (w : InfinitePlace F) : piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d x) = x w :=
  (Place.exists_sec d.cm d.B.emb).choose_spec.2.1 x w
theorem sc_fin_k (x : InfinitePlace F → ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d x = 0 := (Place.exists_sec d.cm d.B.emb).choose_spec.2.2.1 x
variable {p : Type} [Fintype p] [DecidableEq p]
def atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) : Matrix p p (AE F E) :=
  Matrix.of fun i j => _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d (fun w' => fam w Z w' i j) + finOne F • (1 : Matrix p p (AE F E)) i j
theorem cw_mul_k {q : Type} [Fintype q] (w : InfinitePlace F) (A B : Matrix q q (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B :=
  Matrix.map_mul (f := piInf (d.B.emb w))
theorem cw_one_k {q : Type} [DecidableEq q] (w : InfinitePlace F) : d.cw w (1 : Matrix q q (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_atM_k (w w' : InfinitePlace F) (Z : Matrix p p ℂ) : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z) = fam w Z w' := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k, Matrix.of_apply, map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_pi_k, Place.piInf_finOne, add_zero]
theorem fin_atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z = finOne F • (1 : Matrix p p (AE F E)) := by
  ext i j
  simp only [Matrix.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k, Matrix.of_apply, smul_add, _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_fin_k, zero_add, smul_smul, fin_idem]
theorem atM_mul_k (w : InfinitePlace F) (Z Z' : Matrix p p ℂ) : _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (Z * Z') = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z' := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    unfold fam
    split_ifs <;> simp
  · rw [fin_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← fin_mul, Matrix.mul_one]
theorem atM_one_k (w : InfinitePlace F) : _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (1 : Matrix p p ℂ) = 1 := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k]
    unfold fam
    split_ifs <;> rfl
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k]
theorem continuous_atM_k (w : InfinitePlace F) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k (p := p) d w) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.add ((_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_cont_k d).comp (continuous_pi fun w' => ?_)) continuous_const
  unfold fam
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_id)
  · exact continuous_const
end Glue
section Iota
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem bb_k : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]
theorem bb'_k : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]
def Zm_k (ζ : ℂ) (y : GR d.n) : M2 d.n := dZ d.n ζ⁻¹ * mR y * dZ d.n ζ
theorem Zm_mul_k {ζ : ℂ} (h : ζ ≠ 0) (y y' : GR d.n) : _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ (y * y') = _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y * _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
  rw [show mR (y * y') = mR y * mR y' from rfl]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dZ d.n ζ) (dZ d.n ζ⁻¹), dZ_mul_inv h, Matrix.one_mul]
theorem Zm_one_k {ζ : ℂ} (h : ζ ≠ 0) : _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ 1 = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
  rw [show mR (1 : GR d.n) = 1 from rfl, Matrix.mul_one, dZ_inv_mul h]
def MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) * incM F (d.b⁻¹).1
theorem MxI_mul_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) (y y' : GR d.n) : _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ (y * y') = _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y * _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_mul_k d h, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), _root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.one_mul]
theorem MxI_one_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) : _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ 1 = 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_one_k d h, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k]
theorem inFrame_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) :
    incM F (d.b⁻¹).1 * _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y * incM F d.b.1 = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.mul_one, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.one_mul]
theorem dbl_incM_k : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
  simp only [dbl, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
  congr 1
  ext i j
  simp
theorem cw_transpose_k {p q : Type} (w : InfinitePlace F) (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ :=
  Matrix.transpose_map
theorem cw_incM_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) : d.cw w (incM F M) = M.map (d.B.emb w).1 :=
  Matrix.ext fun i j => PositivityTheory.ThKG.Tow.Levi.piInf_incl (d.B.emb w) (M i j)
theorem map_sig_emb_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) :
    (M.map σ).map (d.B.emb w).1 = (M.map (d.B.emb w).1).map star := by
  ext i j
  exact d.cm.2.2.2 _ _
theorem hQ_w_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * (dbl d.Y.J).map (d.B.emb w).1 * (d.b.1.map (d.B.emb w).1).map star = Qc d.n ε := by
  have h := congrArg (fun M => M.map (d.B.emb w).1) hε
  simp only [Matrix.map_mul (f := (d.B.emb w).1), _root_.PositivityTheory.SiegelWeilFormula.Krd.map_sig_emb_k] at h
  rw [Matrix.transpose_map] at h
  rw [h]
  simp only [Qc, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
theorem fin_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y = finOne F • 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, fin_mul, fin_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← fin_mul, ← fin_mul, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k]
theorem MxI_unitary_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y)ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y).map (cA σ) = dbl (incM F d.Y.J) := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k]
    have hM : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y) = d.b.1.map (d.B.emb w').1 * fam w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) w' * (d.b⁻¹).1.map (d.B.emb w').1 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    rw [hM]
    refine conj_unit _ _ _ _ _ ?_ (_root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d hε w') ?_
    · rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · unfold fam
      split_ifs
      · exact (unitary_iff hζ (mR y)).2 y.2
      · rw [Matrix.transpose_one, mapStar_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : (finOne F • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))).map (cA σ) = finOne F • 1 := by
      rw [map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [fin_mul, fin_mul, ← Matrix.transpose_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_MxI_k, ← map_cA_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_MxI_k, e1, Matrix.transpose_smul,
      Matrix.transpose_one, ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]
def iotaF_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) : d.G :=
  ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y⁻¹, by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ), mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ)],
    by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ), inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ)]⟩, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_unitary_k d hε hζ w y⟩
def iota_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : GR d.n →* d.G where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.Krd.iotaF_k d hε hζ w
  map_one' := Subtype.ext (Units.ext (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ) w))
  map_mul' a b := Subtype.ext (Units.ext (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ) w a b))
theorem inFrame_iota_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ w y) = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) :=
  _root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_MxI_k d w ζ y
theorem continuous_iota_k {ε : ℤˣ} {ζ : ℂ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ w) := by
  have hm : Continuous fun y : GR d.n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hz : Continuous fun y : GR d.n => _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y := (continuous_const.matrix_mul hm).matrix_mul continuous_const
  have hM : Continuous fun y : GR d.n => _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y :=
    (continuous_const.matrix_mul ((_root_.PositivityTheory.SiegelWeilFormula.Krd.continuous_atM_k d w).comp hz)).matrix_mul continuous_const
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨hM, ?_⟩
  exact hM.comp continuous_inv
theorem iotaEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.IotaEx_k := by
  intro F E _ _ _ _ _ σ d ε ζ hε hζ
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ, _root_.PositivityTheory.SiegelWeilFormula.Krd.continuous_iota_k d hε hζ, fun w y => ?_, fun w w' y hw => ?_, fun w y => ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [fam, if_true, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dZ_mul_inv (zeta_ne hζ), Matrix.one_mul]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [fam, if_neg hw]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k]
end Iota
end PositivityTheory.SiegelWeilFormula.Krd
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingNStr
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem nilpotentMap_add (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
theorem nb_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb) (β β' : nA σ d.Y d.b) :
    nb (β + β') = nb β * nb β' :=
  kfour.nb_add h β β'
theorem nb_rat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb) {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) :
    nb β ∈ rat2 σ d.Y :=
  kfour.nb_rat h β hβ
theorem continuous_nb_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb) : Continuous nb :=
  kfour.nb_continuous (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame h
theorem nCocompact_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ K : Set (nA σ d.Y d.b), IsCompact K ∧ ∀ β, ∃ l ∈ nF σ d.Y d.b, β - l ∈ K := by
  obtain ⟨K, hK, hKx⟩ := kfour.nF_cocompact (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame
  refine ⟨K, hK, fun β => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hKx β
  exact ⟨-γ, neg_mem hγ, by rwa [sub_neg_eq_add, add_comm]⟩
theorem aesm_of_continuous_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {u : nA σ d.Y d.b × (Fin d.n → Fin d.n → ℝ) → ℂ} (hu : Continuous u) :
    AEStronglyMeasurable u ((lam.restrict 𝓖).prod volume) :=
  kfour.aesm_of_continuous (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame lam 𝓖 hu
theorem chi_cont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) :
    Continuous fun β : nA σ d.Y d.b => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (Algebra.trace (AF F) (AE F E))
  exact d.ok.good.std.1.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace).neg)
theorem chi_per_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) {l : nA σ d.Y d.b} (hl : l ∈ nF σ d.Y d.b) :
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * l.1)))) = 1 := by
  obtain ⟨T₀, hT₀⟩ := (kfour.mem_nF_iff T.1).1 T.2
  obtain ⟨l₀, hl₀⟩ := (kfour.mem_nF_iff l).1 hl
  rw [hT₀, hl₀, ← kfour.incM_mul']
  exact psi_rat d.ok.good.std.2.1 (T₀ * l₀)
theorem chi_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) (β β' : nA σ d.Y d.b) :
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β + β').1)))) =
      d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) *
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β'.1)))) := by
  rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul]
set_option maxHeartbeats 800000 in
theorem fc_shift_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hCD : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (f : d.G → ℂ) (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (T : nF σ d.Y d.b) (β₁ : nA σ d.Y d.b) (z : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 f T (nb β₁ * z) = d.B.ψ (d.tt (T.1.1 * β₁.1)) * fc d.B.ψ d.b nb lam 𝓖 f T z := by
  obtain ⟨hN, hH, hD, -⟩ := hCD
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  set u : nA σ d.Y d.b → ℂ := fun β => f (nb β * z) * χ β with hu
  have hca : ∀ a b, χ (a + b) = χ a * χ b := fun a b => _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_add_k d T a b
  have hcp : ∀ l ∈ nF σ d.Y d.b, χ l = 1 := fun l hl => _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_per_k d T hl
  have hper : ∀ (γ : nF σ d.Y d.b) (x : nA σ d.Y d.b), u (γ +ᵥ x) = u x := by
    intro γ x
    show f (nb (γ.1 + x) * z) * χ (γ.1 + x) = f (nb x * z) * χ x
    rw [hca, hcp _ γ.2, one_mul, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, mul_assoc, hinv _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hN γ.2)]
  have hc : d.B.ψ (d.tt (T.1.1 * β₁.1)) * χ β₁ = 1 := by
    simp only [hχ, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have e1 : ∀ β, f (nb β * (nb β₁ * z)) * χ β = d.B.ψ (d.tt (T.1.1 * β₁.1)) * u (β₁ + β) := by
    intro β
    simp only [hu]
    rw [← mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, add_comm β₁ β, hca β β₁]
    linear_combination (-(f (nb (β + β₁) * z) * χ β)) * hc
  have eL : fc d.B.ψ d.b nb lam 𝓖 f T (nb β₁ * z) = d.B.ψ (d.tt (T.1.1 * β₁.1)) * ∫ β in 𝓖, u (β₁ + β) ∂lam := by
    unfold fc
    rw [← integral_const_mul]
    congr 1
    funext β
    exact e1 β
  rw [eL]
  congr 1
  have hmp := measurePreserving_add_left lam β₁
  have hme : MeasurableEmbedding fun β : nA σ d.Y d.b => β₁ + β := measurableEmbedding_addLeft β₁
  have hs : (fun β : nA σ d.Y d.b => β₁ + β) ⁻¹' ((fun β => -β₁ + β) ⁻¹' 𝓖) = 𝓖 := by
    ext β
    simp
  have h2 : IsAddFundamentalDomain (nF σ d.Y d.b) ((fun β => -β₁ + β) ⁻¹' 𝓖) lam := by
    refine hD.preimage_of_equiv (measurePreserving_add_left lam (-β₁)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => ?_
    show -β₁ + (γ.1 + x) = γ.1 + (-β₁ + x)
    abel
  calc ∫ β in 𝓖, u (β₁ + β) ∂lam
      = ∫ β in (fun β : nA σ d.Y d.b => β₁ + β) ⁻¹' ((fun β => -β₁ + β) ⁻¹' 𝓖), u (β₁ + β) ∂lam := by rw [hs]
    _ = ∫ β in (fun β => -β₁ + β) ⁻¹' 𝓖, u β ∂lam := hmp.setIntegral_preimage_emb hme u _
    _ = ∫ β in 𝓖, u β ∂lam := h2.setIntegral_eq hD hper
end PositivityTheory.SiegelWeilFormula.KSing
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitP
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KSplitP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem siegel_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {p : d.G} {t : GL (Fin d.n) (AE F E)} (hp : IsPar p t) :
    ∃ C : ℂ, ∀ Φ ∈ d.sch, d.l (d.om p Φ) = C * d.l Φ :=
  ⟨_, fun Φ hΦ => d.ok.dbl.weil.2.2 d.l d.ok.dbl.adm (fun z φ hφ => d.ok.dbl.kill z φ hφ) p t hp Φ hΦ⟩
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : d.T Φ 0 = d.l Φ := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.T
  congr 1
  funext x
  simp [Darboux.rho, schr, Matrix.zero_mul]
theorem loc_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : R.loc w 0 = 0 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
  ext i j
  simp
theorem iota_isPar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (q : GR d.n) (hq : (mR q).toBlocks₂₁ = 0) :
    ∃ t, IsPar (R.ι w q) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  have hn : 0 < d.n := d.ok.hn
  obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set M := inFrame d.b (R.ι w q) with hM
  have hζ : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have hw : dZ d.n R.ζ * d.cw w M = mR q * dZ d.n R.ζ := R.at_w w q
  set C := d.cw w M with hC
  have e1 : dZ d.n R.ζ * C = Matrix.fromBlocks C.toBlocks₁₁ C.toBlocks₁₂ (R.ζ • C.toBlocks₂₁) (R.ζ • C.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
    simp [dZ, Matrix.fromBlocks_multiply]
  have e2 : mR q * dZ d.n R.ζ = Matrix.fromBlocks (mR q).toBlocks₁₁ (R.ζ • (mR q).toBlocks₁₂) (mR q).toBlocks₂₁
      (R.ζ • (mR q).toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q)]
    simp [dZ, Matrix.fromBlocks_multiply]
  rw [e1, e2] at hw
  obtain ⟨h11, -, h21, -⟩ := Matrix.fromBlocks_inj.1 hw
  rw [hq] at h21
  have hC21 : C.toBlocks₂₁ = 0 := (smul_eq_zero.1 h21).resolve_left hζ
  have hoff := R.off_f w q
  have hmem : R.ι w q ∈ SiegelEisensteinSeries.Grp.parS σ d.Y d.b (SiegelEisensteinSeries.Grp.siegelS hn) := by
    refine (SiegelEisensteinSeries.Grp.mem_parS_siegelS hn).2 fun i j => ?_
    refine Place.ad_ext d.cm d.B.emb (fun w' => ?_) ?_
    · by_cases hw' : w' = w
      · subst hw'
        have := congrFun (congrFun hC21 i) j
        simpa [Matrix.toBlocks₂₁, hC, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] using this
      · have := congrFun (congrFun (R.off_w w w' q hw') (Sum.inr i)) (Sum.inl j)
        simpa [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, hM] using this
    · have := congrFun (congrFun hoff (Sum.inr i)) (Sum.inl j)
      simpa [hM] using this
  obtain ⟨t, hPt, hdet⟩ := SiegelEisensteinSeries.Grp.isPar_of_mem_siegelS ht0 hn hmem
  refine ⟨t, hPt, ?_⟩
  set N := M.toBlocks₁₁ with hN
  have hfinN : finOne F • N = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    ext i j
    have := congrFun (congrFun hoff (Sum.inl i)) (Sum.inl j)
    simpa [hN, Matrix.toBlocks₁₁, Matrix.one_apply] using this
  set e := algebraMap (AF F) (AE F E) (finOne F) with he
  have hidem : e * e = e := by rw [he, ← map_mul, Krd.fin_idem]
  have hpow' : ∀ k : ℕ, e ^ (k + 1) = e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hidem]
  have hpow : e ^ d.n = e := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hk]; exact hpow' k
  have hdetN : e * (N.det - 1) = 0 := by
    have h1 : (e • N).det = (e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))).det := by
      rw [he, algebraMap_smul, algebraMap_smul, hfinN]
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, hpow, Matrix.det_one, mul_one] at h1
    rw [mul_sub, h1, mul_one, sub_self]
  have hat : ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1 ∈ PositivityTheory.ThKG.CayleyTransformDarboux.atI F E := by
    rw [PositivityTheory.ThKG.CayleyTransformDarboux.mem_atI, hdet]
    intro u hu
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    have eu : u = u * finOne F :=
      Prod.ext (by change u.1 = u.1 * 0; rw [hu1, mul_zero]) (by change u.2 = u.2 * 1; rw [mul_one])
    rw [Algebra.smul_def, eu, map_mul, mul_assoc, ← he, hdetN, mul_zero]
  rw [PositivityTheory.ThKG.CayleyTransformDarboux.absE_inf d.cm d.B.emb hat]
  rw [Finset.prod_eq_single w (fun w' _ hne => ?_) (fun h => absurd (Finset.mem_univ w) h)]
  · rw [hdet, RingHom.map_det]
    have : (N.map (piInf (d.B.emb w))) = C.toBlocks₁₁ := by ext i j; rfl
    rw [RingHom.mapMatrix_apply, this, h11]
  · rw [hdet, RingHom.map_det]
    have : (N.map (piInf (d.B.emb w'))) = (d.cw w' M).toBlocks₁₁ := by ext i j; rfl
    rw [RingHom.mapMatrix_apply, this, R.off_w w w' q hne]
    have h1 : (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ).toBlocks₁₁ = 1 := by
      ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    rw [h1, Matrix.det_one, norm_one, one_pow]
end PositivityTheory.SiegelWeilFormula.KSplitP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitMeasND
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem meas_detA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.A.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact meas_det_of_hasSig (hA.sig w)
    · have h := meas_det_of_hasSig (hA.sig w)
      rw [Matrix.det_smul] at h
      intro h0; exact h (by rw [h0, mul_zero])
  intro h0
  apply key
  have hm := RingHom.map_det (d.B.emb w).1 d.A.J
  rw [RingHom.mapMatrix_apply, h0, map_zero] at hm
  exact hm.symm
theorem meas_hermND'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (hh : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hh j i
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.meas_detA_k d)
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

