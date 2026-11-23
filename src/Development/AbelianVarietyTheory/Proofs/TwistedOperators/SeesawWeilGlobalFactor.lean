module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorProductIrreducibleCountableDimen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052

@[expose] public section

noncomputable section

namespace GlobalTheory.TripleAssembly.Irred

section Linear

theorem exists_descend {U P : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup P] [Module ℂ P] (S : Submodule ℂ U)
    (p : U →ₗ[ℂ] P) (hp : S.map p = ⊤) (Rel : U → U → Prop) (hex : ∀ f ∈ S, ∃ g, Rel f g)
    (hlin : ∀ f ∈ S, ∀ f' ∈ S, ∀ g g', Rel f g → Rel f' g' → ∀ a b : ℂ, Rel (a • f + b • f') (a • g + b • g'))
    (hker : ∀ f ∈ S, ∀ g, Rel f g → p f = 0 → p g = 0) :
    ∃ b : Module.End ℂ P, ∀ f ∈ S, ∀ g, Rel f g → p g = b (p f) := by
  have h1 : ∀ x : P, ∃ f ∈ S, p f = x := fun x => by
    have : x ∈ S.map p := hp ▸ Submodule.mem_top
    exact this
  choose s hs hps using h1
  choose t ht using fun x => hex (s x) (hs x)
  have key : ∀ f ∈ S, ∀ g, Rel f g → p g = p (t (p f)) := fun f hf g h => by
    have := hker _ (add_mem (S.smul_mem 1 hf) (S.smul_mem (-1) (hs (p f)))) _
      (hlin f hf _ (hs (p f)) g _ h (ht _) 1 (-1)) (by simp [hps])
    simpa [add_neg_eq_zero] using this
  have lin : ∀ (a b : ℂ) x y, p (t (a • x + b • y)) = a • p (t x) + b • p (t y) := fun a b x y => by
    have := key _ (add_mem (S.smul_mem a (hs x)) (S.smul_mem b (hs y))) _ (hlin _ (hs x) _ (hs y) _ _ (ht x) (ht y) a b)
    simp only [map_add (f := _), map_smul, hps] at this
    exact this.symm
  refine ⟨{ toFun := fun x => p (t x), map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, key⟩
  · simpa using lin 1 1 x y
  · simpa using lin a 0 x x

theorem nontrivial_tensor {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i)
    (hs : {i | s i = 0}.Finite) (hN : ∀ i, Nontrivial (N i)) (P : Type) [AddCommGroup P] [Module ℂ P] [Nontrivial P] :
    Nontrivial (TensorProduct ℂ P (GlobalTheory.SmallThetaModules.RTens s)) := by
  have h1 : ∀ i, ∃ x : N i, x ≠ 0 ∧ (s i ≠ 0 → x = s i) := fun i => by
    by_cases h : s i = 0
    · obtain ⟨x, hx⟩ := exists_ne (0 : N i)
      exact ⟨x, hx, fun k => absurd h k⟩
    · exact ⟨s i, h, fun _ => rfl⟩
  choose ξ hξ hξs using h1
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hξ i)
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.SmallThetaModules.pureT_sep s l (hs.subset fun i hi => by
    by_contra h
    exact hi (by rw [← hξs i h, hl]))
  have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ := hs.subset fun i hi => by
    by_contra h
    exact hi (hξs i h)
  obtain ⟨x, hx⟩ := exists_ne (0 : P)
  obtain ⟨m, hm⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  refine ⟨x ⊗ₜ GlobalTheory.SmallThetaModules.pureT s ξ, 0, fun h => ?_⟩
  have := congrArg (LinearMap.mul' ℂ ℂ ∘ₗ TensorProduct.map m Λ) h
  simp [hΛ ξ hr, hm, hl] at this

end Linear

section Darboux

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.RealLift.Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end Darboux

section MatrixPart

open scoped Matrix
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealLift.OneParam

theorem exists_lie_of_frame {k d r s : ℕ} (e : Fin k ≃ Fin d) (H : Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (hc : c ≠ 0)
    (C : Matrix (Fin k) (Ix r s) ℂ) (hC : IsFrame (c • (Hᴴ).submatrix e e) C) (Z : Mat r s) (hZ : Z ∈ upq r s) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, Yᴴ * H + H * Y = 0 ∧
      ∀ t : ℝ, ((NormedSpace.exp (t • Y)).map (starRingEnd ℂ)).submatrix e e * C = C * NormedSpace.exp (t • Z) := by
  obtain ⟨hF, C', hR⟩ := hC
  have hL : C' * C = 1 := frame_inv hF hR
  let φ : Mat r s →+* Matrix (Fin d) (Fin d) ℂ :=
    { toFun := fun Z => ((C * Z * C').map (starRingEnd ℂ)).submatrix e.symm e.symm
      map_one' := by simp [hR]
      map_mul' := fun Z Z' => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.map_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc C' C, hL, Matrix.one_mul]
      map_zero' := by simp
      map_add' := fun Z Z' => by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _)]
        rfl }
  have hφ : ∀ Z, φ Z = ((C * Z * C').map (starRingEnd ℂ)).submatrix e.symm e.symm := fun _ => rfl
  have hcont : Continuous φ :=
    (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_map
      Complex.continuous_conj).matrix_submatrix _ _
  refine ⟨φ Z, ?_, fun t => ?_⟩
  · set M := c • (Hᴴ).submatrix e e with hM
    have hM' : M = C'ᵀ * Jm r s * C'.map star := by
      rw [← hF]
      calc M = (C * C')ᵀ * M * (C * C').map star := by
            rw [hR, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (by simp) (by simp), Matrix.mul_one]
        _ = _ := by rw [map_star_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    have hL1 : Cᵀ * C'ᵀ = 1 := by rw [← Matrix.transpose_mul, hL, Matrix.transpose_one]
    have hL2 : C'.map star * C.map star = 1 := by rw [← map_star_mul, hL, Matrix.map_one _ (by simp) (by simp)]
    have hZ' : Zᵀ * Jm r s + Jm r s * Z.map star = 0 := by
      have h0 : Zᴴ * Jm r s + Jm r s * Z = 0 := hZ
      have := congrArg Matrix.transpose h0
      rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, jm_transpose, Matrix.transpose_zero,
        add_comm] at this
      exact this
    have h1 : (C * Z * C')ᵀ * M + M * (C * Z * C').map star = 0 := by
      calc _ = C'ᵀ * (Zᵀ * (Cᵀ * C'ᵀ) * Jm r s + Jm r s * (C'.map star * C.map star) * Z.map star) * C'.map star := by
            rw [hM', map_star_mul, map_star_mul, Matrix.transpose_mul, Matrix.transpose_mul]
            simp only [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
        _ = 0 := by rw [hL1, hL2, Matrix.mul_one, Matrix.mul_one, hZ', Matrix.mul_zero, Matrix.zero_mul]
    rw [hM, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_eq_zero, or_iff_right hc] at h1
    have h2 := congrArg (fun A => (Aᴴ).submatrix e.symm e.symm) h1
    rw [hφ]
    generalize C * Z * C' = Y at h2 ⊢
    have e1 : H = (H.submatrix e e).submatrix e.symm e.symm := by simp
    rw [e1, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_submatrix,
      Matrix.conjTranspose_conjTranspose] at h2
    rw [add_comm] at h2
    ext i j
    exact (congrFun (congrFun h2 i) j).trans (star_zero _)
  · have e1 : t • φ Z = φ (t • Z) := by
      rw [hφ, hφ, Matrix.mul_smul, Matrix.smul_mul]
      generalize C * Z * C' = Y
      ext i j
      simp
    have e2 : NormedSpace.exp (φ (t • Z)) = φ (NormedSpace.exp (t • Z)) := by
      letI : NormedRing (Mat r s) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Mat r s) := Matrix.linftyOpNormedAlgebra
      letI : NormedAlgebra ℚ (Mat r s) := NormedAlgebra.restrictScalars ℚ ℂ (Mat r s)
      letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
      letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
      haveI : CompleteSpace (Mat r s) := FiniteDimensional.complete ℂ _
      exact (NormedSpace.map_exp φ hcont _).symm
    rw [e1, e2, hφ]
    have e3 : ∀ A : Matrix (Fin k) (Fin k) ℂ,
        (((A.map (starRingEnd ℂ)).submatrix e.symm e.symm).map (starRingEnd ℂ)).submatrix e e = A := fun A => by
      ext i j; simp
    rw [e3, Matrix.mul_assoc, hL, Matrix.mul_one]

end MatrixPart

section Reading

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {D : D7}

theorem toUX_surj (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (hξ : D.host.xi0 ≠ 0) (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    ∃ g : GA D X, GlobalTheory.TripleRead.toUX X e hJ g = h := by
  subst hJ
  have h0 : (h.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e) * (h.1.1).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e) := h.2
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h0
  have h1 := congrArg (fun A => incA D D.host.xi0⁻¹ • A) h0
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hξ, map_one, one_smul] at h1
  have h2 := congrArg (fun A => Aᵀ.submatrix e.symm e.symm) h1
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((X.gramᵀ).submatrix e e))ᵀ = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e e := rfl
  simp only [transpose_mul, transpose_transpose, e1] at h2
  refine ⟨⟨⟨h.1.1.submatrix e.symm e.symm, h.1.2.submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, h.1.val_inv]; exact Matrix.submatrix_one_equiv e.symm,
    by rw [Matrix.submatrix_mul_equiv, h.1.inv_val]; exact Matrix.submatrix_one_equiv e.symm⟩, ?_⟩, ?_⟩
  · show ((h.1.1.submatrix e.symm e.symm).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram * h.1.1.submatrix e.symm e.symm =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram = ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram).submatrix e e).submatrix e.symm e.symm := by simp
    have e3 : ((h.1.1.submatrix e.symm e.symm).map (cA D))ᵀ = ((h.1.1.map (cA D))ᵀ).submatrix e.symm e.symm := rfl
    rw [e2, e3, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.mul_assoc]
    exact h2
  · apply Subtype.ext
    apply Units.ext
    show (h.1.1.submatrix e.symm e.symm).submatrix e e = h.1.1
    simp

theorem mem_GfC_of_at (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k)
    (hJ : Wd.J = D.host.xi0 • (X.gramᵀ).submatrix e e) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)) (g : GA D X)
    (hg : GlobalTheory.TripleRead.toUX X e hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.AdelicU.evFin D.host.F v)) :
    g ∈ GfC X := by
  let u : AF D.host.F := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 1 0
  have h := hg u (by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v 0 = 0
    exact map_zero _)
  have key : ∀ z : AE D, infPart D (u • z) = infPart D z := by
    intro z
    rw [Algebra.smul_def, map_mul]
    exact one_mul _
  show infHom X g = 1
  apply Units.ext
  ext i j
  have h1 := congrArg (infPart D) (congrFun (congrFun h (e.symm i)) (e.symm j))
  rw [Matrix.smul_apply, key, Matrix.sub_apply, map_sub, Matrix.zero_apply, map_zero, sub_eq_zero] at h1
  have h2 : infPart D (Formalism.L2.Theta.mt X g (e (e.symm i)) (e (e.symm j))) = _ := h1
  rw [e.apply_symm_apply, e.apply_symm_apply] at h2
  refine h2.trans ?_
  by_cases c : i = j
  · subst c; simp
  · have c' : e.symm i ≠ e.symm j := fun k => c (e.symm.injective k)
    simp [c, c']

theorem kapX_eq (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (hJ' : J = D.host.xi0 • reindex e.symm e.symm X.gramᵀ) (g : GA D X) :
    GlobalTheory.SquareAgree.kapX X e.symm hJ' g = GlobalTheory.TripleRead.toUX X e hJ g := by
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.TripleRead.toUX_val]
  exact GlobalTheory.SquareAgree.mat_kapX X e.symm hJ' g

theorem toUX_map (θ : InfFam D) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (τ : D.what₂.Tau) (π : AE D →+* ℂ)
    (hπ : ∀ y, π y = conj (θ τ (infPart D y))) (g : GA D X) :
    (GlobalTheory.TripleRead.toUX X e hJ g).1.1.map π = ((infMat D.sp.cm.sig X.gram (θ τ) g).map (starRingEnd ℂ)).submatrix e e := by
  rw [GlobalTheory.TripleRead.toUX_val]
  ext i j
  exact hπ _

theorem piInf_of_conj (θ : InfFam D) (hθ : IsInfFam θ) {w : InfinitePlace D.host.F} (t : GlobalTheory.AdelicU.EmbOver D.host.E w)
    (τ : D.what₂.Tau) (hE : t.1 = (starRingEnd ℂ).comp (tauE D τ)) (y : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf t y = conj (θ τ (infPart D y)) := by
  obtain ⟨t, ht⟩ := t
  dsimp only at hE
  subst hE
  exact GlobalTheory.ConjInfExp.piInf_eq θ hθ τ w ht y

theorem exists_line_at (θ : InfFam D) (hθ : IsInfFam θ) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k) (hJ : Wd.J = D.host.xi0 • (X.gramᵀ).submatrix e e)
    (hξ : D.host.xi0 ≠ 0) (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w)
    (hemb : ∀ w, ∃ τ, ∀ x, (emb w).1 x = conj (tauE D τ x)) {r s : ℕ}
    (C : InfinitePlace D.host.F → Matrix (Fin k) (Ix r s) ℂ)
    (hC : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • Wd.J.map (emb w).1) (C w)) (w : InfinitePlace D.host.F) (Z : Mat r s)
    (hZ : Z ∈ upq r s) [DecidableEq (InfinitePlace D.host.F)] :
    ∃ γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J,
      (∃ τ, ∃ Y ∈ lieAt X τ, ∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X e hJ (oneP θ X τ Y t)) ∧
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd ∧ GlobalTheory.RealLift.IsGen emb C γ (Function.update (fun _ => 0) w Z) := by
  choose τ hτ using hemb
  have hE : ∀ w, (emb w).1 = (starRingEnd ℂ).comp (tauE D (τ w)) := fun w => RingHom.ext (hτ w)
  have hpi : ∀ w y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w) y = conj (θ (τ w) (infPart D y)) := fun w y =>
    piInf_of_conj θ hθ (emb w) (τ w) (hE w) y
  have hinj : ∀ w', w' ≠ w → τ w' ≠ τ w := fun w' hw k => hw (by
    have h1 := (emb w').2
    rw [hE, k, ← hE, (emb w).2] at h1
    rw [← w.mk_embedding, h1, InfinitePlace.mk_embedding])
  have hM : Complex.I • Wd.J.map (emb w).1 =
      (Complex.I * (emb w).1 D.host.xi0) • ((gramAt D X (τ w))ᴴ).submatrix e e := by
    rw [hJ]
    ext i j
    simp [gramAt, hτ, mul_assoc]
  obtain ⟨Y, hY, hexp⟩ := exists_lie_of_frame e (gramAt D X (τ w)) _
    (mul_ne_zero Complex.I_ne_zero ((map_ne_zero _).2 hξ)) (C w) (by rw [← hM]; exact hC w) Z hZ
  have hJ' : Wd.J = D.host.xi0 • reindex e.symm e.symm X.gramᵀ := hJ
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X (τ w) Y hθ hY e.symm Wd hJ'
  simp only [kapX_eq X e hJ hJ'] at hγt
  refine ⟨γ, ⟨τ w, Y, hY, hγt⟩, hγ, fun t w' => ?_⟩
  have hat := GlobalTheory.Mem.Lift.isAtTau_oneP hθ (show Y ∈ lieAt X (τ w) from hY) t
  have e1 := toUX_map θ X e hJ (τ w') _ (hpi w') (oneP θ X (τ w) Y t)
  rw [← hγt t] at e1
  refine (congrArg (· * C w') e1).trans ?_
  by_cases c : w' = w
  · subst c
    rw [hat.2.1, hexp, Function.update_self]
  · rw [hat.2.2 _ (hinj w' c), Function.update_of_ne c]
    simp

end Reading

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

theorem end_ext {U P ι : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup P] [Module ℂ P] {V N : ι → Type}
    [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)] [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (S : Submodule ℂ U) (pr : U →ₗ[ℂ] P) (hpr : S.map pr = ⊤) (SV : ∀ v, Submodule ℂ (V v)) (pv : ∀ v, V v →ₗ[ℂ] N v)
    (hpv : ∀ v, (SV v).map (pv v) = ⊤) (m : ∀ v, V v) (hm : ∀ v, m v ∈ SV v)
    (T T' : Module.End ℂ (P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens fun v => pv v (m v)))
    (h : ∀ f ∈ S, ∀ φ : ∀ v, V v, (∀ v, φ v ∈ SV v) → (∀ᶠ v in Filter.cofinite, φ v = m v) →
      T (pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT _ fun v => pv v (φ v)) =
        T' (pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT _ fun v => pv v (φ v))) : T = T' := by
  refine TensorProduct.ext' fun x y => ?_
  obtain ⟨f, hf, rfl⟩ : x ∈ S.map pr := hpr ▸ Submodule.mem_top
  refine LinearMap.congr_fun (LinearMap.ext_on (GlobalTheory.SmallThetaModules.pureT_span fun v => pv v (m v))
    (f := T ∘ₗ TensorProduct.mk ℂ _ _ (pr f)) (g := T' ∘ₗ TensorProduct.mk ℂ _ _ (pr f)) ?_) y
  rintro _ ⟨ξ, hξ, rfl⟩
  have h1 : ∀ v, ∃ φ ∈ SV v, pv v φ = ξ v ∧ (pv v (m v) = ξ v → φ = m v) := by
    intro v
    by_cases hv : pv v (m v) = ξ v
    · exact ⟨m v, hm v, hv, fun _ => rfl⟩
    · obtain ⟨φ, hφ, e⟩ : ξ v ∈ (SV v).map (pv v) := (hpv v) ▸ Submodule.mem_top
      exact ⟨φ, hφ, e, fun k => absurd k hv⟩
  choose φ hφ hφ1 hφ2 using h1
  have h2 : ∀ᶠ v in Filter.cofinite, φ v = m v := by
    have h3 : ∀ᶠ v in Filter.cofinite, ξ v = pv v (m v) := hξ
    filter_upwards [h3] with v b using hφ2 v b.symm
  have := h f hf φ hφ h2
  rw [funext hφ1] at this
  exact this


end Main

end GlobalTheory.TripleAssembly.Irred

end
