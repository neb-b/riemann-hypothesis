module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FrameSignEqInvolutionScalar
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
theorem rel_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (y : d.G) :
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 * (inFrame d.b y).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hF : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
    rw [e1, e2, ← key, hε]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hM : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = dbl (incM F d.Y.J) := y.2
  have := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hM
  rw [← hF]
  exact this
theorem rel_nA_cond_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (β : nA σ d.Y d.b) :
    β.1ᵀ + ((ε : ℤ) : AE F E) • β.1.map (cA σ) = 0 := by
  obtain ⟨β, hβ⟩ := β
  show βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0
  induction hβ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := hx
    have h := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_frame_k d ε hε y
    rw [hy] at h
    simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
      Matrix.transpose_one, Matrix.map_zero _ (map_zero (cA σ)), Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.fromBlocks_inj] at h
    rw [add_comm]
    have h4 := h.2.2.2
    rw [Matrix.smul_mul, Matrix.one_mul] at h4
    exact h4
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.transpose_add, Matrix.map_add _ (map_add (cA σ)), smul_add]
    calc _ = (xᵀ + ((ε : ℤ) : AE F E) • x.map (cA σ)) + (yᵀ + ((ε : ℤ) : AE F E) • y.map (cA σ)) := by abel
      _ = 0 := by rw [hx, hy, add_zero]
  | neg x _ hx =>
    rw [Matrix.transpose_neg, Matrix.map_neg _ (map_neg (cA σ)), smul_neg, ← neg_add, hx, neg_zero]
theorem frameSign_eq_involution_scalar (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hσ : ∀ x, σ (σ x) = x) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (c : E)
    (hc : d.Y.J.map σ = c • d.Y.Jᵀ) (i : Fin d.n) : ((ε : ℤ) : E) = c := by
  have hD : (dbl d.Y.J).map σ = c • (dbl d.Y.J)ᵀ := by
    simp only [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_smul, hc,
      Matrix.map_neg _ (map_neg σ), Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero, Matrix.transpose_neg,
      smul_zero, smul_neg]
  have hbb : (d.b.1.map σ).map σ = d.b.1 := by
    ext i j
    simp [hσ]
  have h1 := congrArg σ.mapMatrix hε
  simp only [map_mul, AlgHom.mapMatrix_apply, hD, hbb] at h1
  have h2 := congrArg Matrix.transpose h1
  simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.transpose_map] at h2
  rw [← Matrix.mul_assoc, hε] at h2
  have := congrFun (congrFun h2 (Sum.inr i)) (Sum.inl i)
  simp [Matrix.fromBlocks_map] at this
  have hε2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  calc ((ε : ℤ) : E) = ((ε : ℤ) : E) * (c * ((ε : ℤ) : E)) := by rw [this, mul_one]
    _ = c * (((ε : ℤ) : E) * ((ε : ℤ) : E)) := by ring
    _ = c := by rw [hε2, mul_one]
theorem rel_sign_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ((∀ i j, σ (d.Y.J j i) = -d.Y.J i j) → ε = -1) ∧ ((∀ i j, σ (d.Y.J j i) = d.Y.J i j) → ε = 1) := by
  have hσ := rel_sigma_sigma d.ok.good.cm
  have i : Fin d.n := ⟨0, d.ok.hn⟩
  constructor
  · intro h
    have := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frameSign_eq_involution_scalar d hσ ε hε (-1) (by ext a b; simp [h b a]) i
    exact Units.ext (Int.cast_injective (α := E) (by simpa using this))
  · intro h
    have := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frameSign_eq_involution_scalar d hσ ε hε 1 (by ext a b; simp [h b a]) i
    exact Units.ext (Int.cast_injective (α := E) (by simpa using this))
theorem rel_eta_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    ∃ η : E, η ≠ 0 ∧ σ η = -(((ε : ℤ) : E) * η) ∧ ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j := by
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k d ε hε).1 hY
    subst he
    refine ⟨1, one_ne_zero, by simp, fun i j => by simp [hA.herm i j]⟩
  · have he := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k d ε hε).2 hY
    subst he
    obtain ⟨η, hη, hση⟩ := rel_anti d.ok.good.cm
    refine ⟨η, hη, by simp [hση], fun i j => ?_⟩
    rw [map_mul, hση, hA.skew i j, neg_mul_neg]
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GramSuppCmpK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def insW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (z : ℂ) : AE F E := (Place.exists_sec d.cm d.B.emb).choose (Pi.single w z)
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F)
theorem insW_self_k (z : ℂ) : piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z) = z := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.1, Pi.single_eq_same]
theorem insW_ne_k {w' : InfinitePlace F} (hw : w' ≠ w) (z : ℂ) : piInf (d.B.emb w') (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z) = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.1, Pi.single_eq_of_ne hw]
theorem insW_fin_k (z : ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, h.2.2.1]
theorem insW_add_k (z z' : ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w (z + z') = _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z + _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w z' := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_k, Pi.single_add, h.2.2.2.1]
end
def insL_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (v : Fin d.m → Fin d.n → ℂ) : Mx F E d.m d.n :=
  ((R.fr w).1 * (Matrix.of v).map star).map (_root_.PositivityTheory.SiegelWeilFormula.KW.insW_k d w)
section
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
def Supp_k (Z : Mx F E d.m d.n) : Prop := (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0
theorem cw_insL_k (v : Fin d.m → Fin d.n → ℂ) : d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v) = (R.fr w).1 * (Matrix.of v).map star := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_self_k]
theorem insL_supp_k (v : Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v) := by
  refine ⟨fun w' hw' => ?_, ?_⟩
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_ne_k d w hw', Matrix.zero_apply]
  · ext i j
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k, Matrix.smul_apply, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_fin_k, Matrix.zero_apply]
theorem insL_add_k (v v' : Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (v + v') = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v + _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w v' := by
  have e : (R.fr w).1 * (Matrix.of (v + v')).map star =
      (R.fr w).1 * (Matrix.of v).map star + (R.fr w).1 * (Matrix.of v').map star := by
    rw [← Matrix.mul_add]
    congr 1
    ext i j
    simp
  unfold _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k
  rw [e]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KW.insW_add_k]
theorem insL_zero_k : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 = 0 := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KW.insL_add_k R w 0 0
  rw [add_zero] at h
  calc _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 + _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 := by abel
    _ = _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w 0 := by rw [← h]
    _ = 0 := sub_self _
theorem insL_loc_k {Z : Mx F E d.m d.n} (hZ : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z) : _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z) = Z := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · by_cases hw : w' = w
    · rw [hw]
      change d.cw w (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) = d.cw w Z
      rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_insL_k]
      have h2 : (Matrix.of (R.loc w Z)).map star = ((R.fr w)⁻¹).1 * d.cw w Z := by
        ext i j
        exact star_star _
      rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    · change d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w Z)) = d.cw w' Z
      rw [(_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w _).1 w' hw, hZ.1 w' hw]
  · rw [(_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w _).2, hZ.2]
theorem rest_inv_k (X Z : Mx F E d.m d.n) (hZ : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z) :
    (X + Z) - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w (X + Z)) = X - _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w (R.loc w X) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add'_k d R w X Z, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_add_k, _root_.PositivityTheory.SiegelWeilFormula.KW.insL_loc_k R w hZ]
  abel
end
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem psi_add_right_k (ε : ℤˣ) (X Z Z' : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z + Z'))) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z')) := by
  have e : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]
theorem psi_add_left_k (ε : ℤˣ) (X X' Z : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (X + X') Z)) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X' Z)) := by
  have e : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul]
  rw [e, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]
theorem cw_gram_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) :
    d.cw w (d.gram X Z) = (d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * (d.cw w Z).map star := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
  have hJ : (incM F d.A.J).map (piInf (d.B.emb w)) = d.A.J.map (d.B.emb w).1 := by
    ext i j
    simp [incM, PositivityTheory.ThKG.Tow.Levi.piInf_incl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Place.map_cA d.cm (d.B.emb w) Z, hJ]
theorem gram_supp_cmp_k (w : InfinitePlace F) {Z' Z : Mx F E d.m d.n} (hZ' : _root_.PositivityTheory.SiegelWeilFormula.KW.Supp_k w Z') (hZ : d.cw w Z = 0) :
    d.gram Z' Z = 0 := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · change d.cw w' (d.gram Z' Z) = d.cw w' 0
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k]
    by_cases hw : w' = w
    · subst hw
      rw [hZ, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
    · rw [hZ'.1 w' hw, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
      ext i j
      simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw]
  · unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, hZ'.2]
    simp
theorem psi_zero_gram_k (ε : ℤˣ) : d.B.ψ (((ε : ℤ) : AF F) * d.tt (0 : Mx F E d.n d.n)) = 1 := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]
end
theorem zeta_ne_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.ζ ≠ 0 := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
section
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem cw_loc_k (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have h2 : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
theorem frJ_k : (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
  have h := R.hfr w
  calc (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star
      = R.ζ⁻¹ • (R.ζ • ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star)) := by
        rw [smul_smul, inv_mul_cancel₀ (_root_.PositivityTheory.SiegelWeilFormula.KW.zeta_ne_k R), one_smul]
    _ = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by rw [h, smul_smul]
end
theorem psi_at_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (ε : ℤˣ) (M : Mx F E d.n d.n)
    (hM1 : ∀ w', w' ≠ w → d.cw w' M = 0) (hM2 : finOne F • M = 0) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt M) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((2 * (((ε : ℤ) : ℂ) * (d.cw w M).trace).re : ℝ) : ℂ)) := by
  have hz : ((ε : ℤ) : AF F) * d.tt M = Algebra.trace (AF F) (AE F E) ((ε : ℤ) • M.trace) := by
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have ptr : ∀ u, piInf (d.B.emb u) M.trace = (d.cw u M).trace := fun u => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, map_sum]
  rw [hz, Place.psi_trace_at d.std d.cm d.B.emb w _ ?_ ?_, map_zsmul, ptr, zsmul_eq_mul]
  · rw [smul_comm, ← Matrix.trace_smul, hM2, Matrix.trace_zero, smul_zero]
  · intro u hu
    rw [map_zsmul, ptr, hM1 u hu, Matrix.trace_zero, smul_zero]
theorem kernel_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (ε : ℤˣ) (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u))) =
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u)).re : ℂ)) := by
  have hM1 : ∀ w', w' ≠ w → d.cw w' (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u)) = 0 := by
    intro w' hw
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w u).1 w' hw, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
  have hM2 : finOne F • d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u) = 0 := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram
    rw [← Matrix.mul_smul]
    have : finOne F • (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u).map (cA σ) = (finOne F • _root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u).map (cA σ) := by
      ext i j
      simp [map_smul]
    rw [this, (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_supp_k R w u).2]
    simp
  have e1 : d.cw w (d.gram X (_root_.PositivityTheory.SiegelWeilFormula.KW.insL_k R w u)) =
      (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KW.cw_gram_k, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_loc_k R w X, _root_.PositivityTheory.SiegelWeilFormula.KW.cw_insL_k, Matrix.transpose_mul]
    have h3 : ((R.fr w).1 * (Matrix.of u).map star).map star = (R.fr w).1.map star * Matrix.of u := by
      ext i j
      simp [Matrix.mul_apply]
    have h4 : ((Matrix.of (R.loc w X)).map star)ᵀ = (Matrix.of (R.loc w X))ᴴ := rfl
    rw [h3, h4]
    calc (Matrix.of (R.loc w X))ᴴ * (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * ((R.fr w).1.map star * Matrix.of u)
        = (Matrix.of (R.loc w X))ᴴ * ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of u := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [_root_.PositivityTheory.SiegelWeilFormula.KW.frJ_k, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KW.psi_at_w_k d w ε _ hM1 hM2, e1, Matrix.trace_smul, smul_eq_mul]
  congr 1
  have e2 : -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ * Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) =
      ((-2 : ℝ) : ℂ) * (((ε : ℤ) : ℂ) * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u))) := by
    push_cast
    ring
  rw [e2, Complex.re_ofReal_mul]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PadMatrixLowerBlockZero
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def emS_k : Fin L.n ⊕ Fin L.n → Fin d.n ⊕ Fin d.n := Sum.map L.em L.em
def padM_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  fun r c => if h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c then M h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r c
theorem emS_inj_k : Function.Injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) := Sum.map_injective.2 ⟨L.inj, L.inj⟩
theorem padM_emS_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (a a' : Fin L.n ⊕ Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = M a a' := by
  have h : (∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) ∧ ∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dite_eq_left h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.1.choose_spec, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.2.choose_spec]
theorem padM_out_row_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) (c : Fin d.n ⊕ Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dite_eq_right (fun h => hr h.1)]
theorem padM_out_col_k (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k]
  rw [dite_eq_right (fun h => hc h.2)]
theorem mem_out_k {r : Fin d.n ⊕ Fin d.n} (h : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) :
    r ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases r with i | i
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inl a, by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, ha]⟩).elim
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inr a, by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, ha]⟩).elim
theorem em_ne_k (a : Fin L.n) : L.em a ≠ L.i₀ := (L.rng (L.em a)).2 ⟨a, rfl⟩
theorem not_inl_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inl i := by
  rintro ⟨a | a, ha⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inl, Sum.inl.injEq] at ha
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L a (ha.trans hi)
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] at ha
theorem not_inr_k (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inr i := by
  rintro ⟨a | a, ha⟩
  · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] at ha
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.inr.injEq] at ha
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L a (ha.trans hi)
theorem inFrame_j_k (g : G2 σ L.Y) : inFrame d.b (L.j g) = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (inFrame L.b g) := by
  ext r c
  by_cases h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c
  · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := h
    rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k]
    have := congrFun (congrFun (L.j_in g) a) a'
    simpa [Matrix.submatrix_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k] using this
  · rcases not_and_or.1 h with h1 | h1
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ h1]
      exact (L.j_out g r (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L h1) c).1
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ r h1]
      exact (L.j_out g c (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L h1) r).2
theorem sub_mem_nA_k (β : nA σ d.Y d.b) : β.1.submatrix L.em L.em ∈ nA σ L.Y L.b := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := _root_.PositivityTheory.SiegelWeilFormula.Afc.eps_eq_k L hε hε'
  subst hee
  rw [kunf.mem_nA_iff hε']
  have h1 : β.1 ∈ kfour.nCond σ d.n ε := (kunf.mem_nA_iff hε β.1).1 β.2
  exact Afc.sub_nCond (σ := σ) L.em β.1 h1
def prj_k : nA σ d.Y d.b →+ nA σ L.Y L.b where
  toFun β := ⟨β.1.submatrix L.em L.em, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.sub_mem_nA_k L β⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' β β' := by
    apply Subtype.ext
    rfl
theorem prj_val_k (β : nA σ d.Y d.b) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β).1 = β.1.submatrix L.em L.em := rfl
theorem continuous_prj_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.matrix_submatrix L.em L.em
theorem pad_matrix_lower_block_zero (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (hM : M.toBlocks₂₁ = 0) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L M).toBlocks₂₁ = 0 := by
  ext i k
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hi : i = L.i₀
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L M (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L i hi)]
    simp
  · by_cases hk : k = L.i₀
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L M _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L k hk)]
      simp
    · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
      obtain ⟨a', rfl⟩ := (L.rng k).1 hk
      have h1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L M (Sum.inr a) (Sum.inl a')
      simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.map_inl] at h1
      rw [h1]
      have h2 := congrFun (congrFun hM a) a'
      simpa [Matrix.toBlocks₂₁] using h2
theorem embedding_lower_block_zero {x : G2 σ L.Y} (hx : ∃ t, IsPar x t) : (inFrame d.b (L.j x)).toBlocks₂₁ = 0 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨-, t₀, ht₀⟩ := L.ok.frame
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k]
  exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.pad_matrix_lower_block_zero L _ ((kunf.isPar_frame ht₀ x t).1 ht).1
theorem j_par_k {g : G2 σ L.Y} (h : g ∈ par2 σ L.Y) : L.j g ∈ par2 σ d.Y := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 h
  obtain ⟨-, t₁, ht₁⟩ := d.ok.frame
  set P := inFrame d.b (L.j g)
  set Q := inFrame d.b (L.j g⁻¹)
  have hP : P.toBlocks₂₁ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.embedding_lower_block_zero L ⟨t, ht⟩
  have hQ : Q.toBlocks₂₁ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.embedding_lower_block_zero L ⟨t⁻¹, ht.inv⟩
  have hPQ : P * Q = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hQP : Q * P = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have e1 := upper_block_mul_of_lower_zero hQ hPQ
  have e2 := upper_block_mul_of_lower_zero hP hQP
  set T0 := incM F t₁.1
  set Ti := incM F (t₁⁻¹).1
  have hT : T0 * Ti = 1 := by
    show incM F t₁.1 * incM F (t₁⁻¹).1 = 1
    rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
  have hT' : Ti * T0 = 1 := by
    show incM F (t₁⁻¹).1 * incM F t₁.1 = 1
    rw [← kunf.incM_mul', Units.inv_mul]; ext i j; simp [incM, Matrix.one_apply]
  let t' : GL (Fin d.n) (AE F E) := ⟨T0 * P.toBlocks₁₁ * Ti, T0 * Q.toBlocks₁₁ * Ti, by
      calc T0 * P.toBlocks₁₁ * Ti * (T0 * Q.toBlocks₁₁ * Ti) = T0 * (P.toBlocks₁₁ * (Ti * T0) * Q.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e1, Matrix.mul_one, hT], by
      calc T0 * Q.toBlocks₁₁ * Ti * (T0 * P.toBlocks₁₁ * Ti) = T0 * (Q.toBlocks₁₁ * (Ti * T0) * P.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e2, Matrix.mul_one, hT]⟩
  exact mem_parabolic_GL2_iff.2 ⟨t', (kunf.isPar_frame ht₁ (L.j g) t').2 ⟨hP, rfl⟩⟩
def padE_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  fun r c => if h : (∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) ∧ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c then N h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r c
theorem padM_incM_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (incM F N) = incM F (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N) := by
  ext r c
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k, incM, Matrix.map_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
theorem j_rat_k {g : G2 σ L.Y} (h : g ∈ rat2 σ L.Y) : L.j g ∈ rat2 σ d.Y := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 h
  have hm : mat2 g = incM F γ.1 := by
    show g.1.1 = _
    rw [← hγ]
    rfl
  have hf : inFrame L.b g = incM F ((L.b⁻¹).1 * γ.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]
    rfl
  refine kunf.rat_of_inFrame (b := d.b) (M := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L ((L.b⁻¹).1 * γ.1 * L.b.1)) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k, hf, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_incM_k]
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

