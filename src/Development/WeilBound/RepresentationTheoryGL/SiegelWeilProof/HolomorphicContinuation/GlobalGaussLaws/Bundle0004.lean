module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def nbar (c : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks 1 0 c 1

def mM (a : Matrix (Fin n) (Fin n) ℂ) : M2 n := fromBlocks a 0 0 (aᴴ)⁻¹

def IsSch {m : ℕ} (f : (Fin m → Fin n → ℂ) → ℂ) : Prop := ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑S = f

def AwayCls {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (Ψ : Mx D m n → ℂ) : Prop :=
  (∀ x x' : Mx D m n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') → x.map (finPart D) = x'.map (finPart D) →
    Ψ x = Ψ x') ∧ ∀ f, IsSch f → tens θ τ fr f Ψ ∈ schwartzA θ m n

def Decomp : Prop :=
  ∀ (n : ℕ) (y : GR n), ∃ y₁ y₂ y₃ y₄ : GR n, y = y₁ * y₂ * y₃ * y₄ ∧
    (∃ t : ℝ, mR y₁ = nU ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) ∧ (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y₂ = nbar c) ∧
    (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y₃ = mM a) ∧ (∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y₄ = nU b)

def LNe : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ →
    HasRealPar ψ θ l → ∀ τ, l τ ≠ 0

def AwayIn : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (ε : Fin V.rank → Bool) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ →
    (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → IsTauFrame V τ s ε fr → (∀ τ', l τ' ≠ 0) → ∀ Ψ ∈ awayA θ V n l s τ,
      AwayCls θ τ fr Ψ

def SchFP : Prop := ∀ (m n : ℕ) (c : ℝ), 0 < c → ∀ P : PX m n, IsSch (fP c P)

def OpGen : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ y : GR n,
    ((∃ b : Matrix (Fin n) (Fin n) ℂ, bᴴ = b ∧ mR y = nU b) ∨ (∃ c : Matrix (Fin n) (Fin n) ℂ, cᴴ = c ∧ mR y = nbar c) ∨
      (∃ a : Matrix (Fin n) (Fin n) ℂ, IsUnit a.det ∧ mR y = mM a)) →
    ∃ L : ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ), (∀ f, IsSch f → IsSch (L f)) ∧
      ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
        (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L f) Ψ

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRhoF
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {n : ℕ}

def reIm {m : ℕ} : Fin m × Fin n × Bool → MvPolynomial (Fin m × Fin n × Bool) ℂ := fun k =>
  if k.2.2 then X (k.1, k.2.1, false) - C Complex.I * X (k.1, k.2.1, true)
  else X (k.1, k.2.1, false) + C Complex.I * X (k.1, k.2.1, true)

def reImInv {m : ℕ} : Fin m × Fin n × Bool → MvPolynomial (Fin m × Fin n × Bool) ℂ := fun k =>
  if k.2.2 then C (1 / (2 * Complex.I)) * (X (k.1, k.2.1, false) - X (k.1, k.2.1, true))
  else C (1 / 2) * (X (k.1, k.2.1, false) + X (k.1, k.2.1, true))

theorem evX_eq_zero {m : ℕ} (P : PX m n) (h : ∀ u : Fin m → Fin n → ℂ, evX P u = 0) : P = 0 := by
  have h2 : (C (1 / 2 : ℂ) + C (1 / 2) : MvPolynomial (Fin m × Fin n × Bool) ℂ) = 1 := by
    rw [← C_add, ← C_1]
    norm_num
  have hI : (C Complex.I * C (1 / (2 * Complex.I)) : MvPolynomial (Fin m × Fin n × Bool) ℂ) = C (1 / 2) := by
    rw [← C_mul]
    congr 1
    field_simp
  have hinv : ∀ k, bind₁ reImInv (reIm (n := n) (m := m) k) = X k := by
    rintro ⟨a, i, b⟩
    cases b
    · simp only [reIm, reImInv, Bool.false_eq_true, ↓reduceIte, map_add (f := _), map_mul, map_sub, bind₁_X_right, bind₁_C_right]
      linear_combination (X (a, i, false) - X (a, i, true)) * hI + X (a, i, false) * h2
    · simp only [reIm, reImInv, Bool.false_eq_true, ↓reduceIte, map_add (f := _), map_mul, map_sub, bind₁_X_right, bind₁_C_right]
      linear_combination -(X (a, i, false) - X (a, i, true)) * hI + X (a, i, true) * h2
  have hQ : bind₁ reIm P = 0 := by
    apply GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_real
    intro u
    let z : Fin m → Fin n → ℂ := fun a i => (u (a, i, false) : ℂ) + Complex.I * (u (a, i, true) : ℂ)
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ reIm P) = 0
    rw [eval₂Hom_bind₁]
    have hf : (fun k => eval₂Hom (RingHom.id ℂ) (fun v => ((u v : ℝ) : ℂ)) (reIm (n := n) (m := m) k)) =
        fun k => if k.2.2 = true then star (z k.1 k.2.1) else z k.1 k.2.1 := by
      funext ⟨a, i, b⟩
      cases b
      · simp [reIm, z]
      · apply Complex.ext <;> simp [reIm, z]
    rw [hf]
    exact h z
  calc P = bind₁ reImInv (bind₁ reIm P) := by
        rw [bind₁_bind₁]
        simp only [hinv]
        rw [bind₁_X_left]
        rfl
    _ = 0 := by rw [hQ, map_zero]

theorem gs_ne_zero {m : ℕ} (c : ℝ) (u : Fin m → Fin n → ℂ) : gs c u ≠ 0 := Complex.exp_ne_zero _

theorem fP_inj {m : ℕ} (c : ℝ) {P Q : PX m n} (h : fP c P = fP c Q) : P = Q := by
  have h0 : P - Q = 0 := by
    apply evX_eq_zero
    intro u
    have := congrFun h u
    unfold fP at this
    have h2 := mul_right_cancel₀ (gs_ne_zero c u) this
    unfold evX at h2 ⊢
    rw [map_sub, h2, sub_self]
  exact sub_eq_zero.1 h0

theorem fP_add_smul {m : ℕ} (c : ℝ) (a : ℂ) (P Q : PX m n) : fP c (a • P + Q) = a • fP c P + fP c Q := by
  funext u
  simp only [fP, evX, map_add (f := _), MvPolynomial.smul_eval, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Formalism.MainNotions.StandardLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

namespace PlaceFactsH

theorem compAt_eq_psiT {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a b : ℕ} (w : Mx D a b) :
    compAt θ τ w = w.map (Formalism.IndefR.Eqv.psiT D τ) := by
  have hθτ : θ τ = Formalism.IndefR.Eqv.thetaC D τ :=
    Formalism.IndefR.Eqv.infEmb_unique (hθ τ) (Formalism.IndefR.Eqv.isInfFam_thetaC D τ)
  ext i j
  change (θ τ) (Formalism.L2.Theta.infPart D (w i j)) = Formalism.IndefR.Eqv.psiT D τ (w i j)
  rw [hθτ]
  rfl

theorem mat_mul' (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' : mat (1 : G D n) = 1 := rfl

theorem mat_inj {g h : G D n} (e : mat g = mat h) : g = h := by
  delta GlobalTheory.StdUnn.mat at e
  exact Subtype.ext (Units.ext e)

theorem compAt_mul' {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a : ℕ} (A B : Mx D a a) :
    compAt θ τ (A * B) = compAt θ τ A * compAt θ τ B := by
  rw [compAt_eq_psiT hθ, compAt_eq_psiT hθ, compAt_eq_psiT hθ, Matrix.map_mul]

theorem compAt_one' {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {a : ℕ} :
    compAt θ τ (1 : Mx D a a) = 1 := by
  rw [compAt_eq_psiT hθ, Matrix.map_one _ (map_zero _) (map_one _)]

section GlobalTheory

variable {R S : Type} [CommRing R] [CommRing S]

def bOf (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

theorem upper_right_entry_block_matrix (a b c d : Matrix (Fin n) (Fin n) R) : bOf (blk4 a b c d) = b := by
  unfold bOf
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_submatrix]
  simp

theorem bOf_map (f : R →+* S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : bOf (M.map f) = (bOf M).map f := by
  ext i j
  rfl

theorem block_matrix_map (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  delta GlobalTheory.StdUnn.blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem submatrix_fromBlocks_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' = blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem reidx_nU (b : Matrix (Fin n) (Fin n) ℂ) : reidx (nU b) = blk4 1 b 0 1 := rfl

end GlobalTheory

theorem commute_of_tau {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    (z : G D n) (hz : compAt θ τ (mat z) = 1) (y' : GR n) : z * ι y' = ι y' * z := by
  obtain ⟨-, hι'⟩ := hι
  obtain ⟨-, h2, h3⟩ := hι' y'
  apply mat_inj
  rw [mat_mul', mat_mul']
  apply Formalism.IndefR.Eqv.mat_ext
  · intro τ'
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases ht : τ' = τ
    · subst ht
      rw [← compAt_eq_psiT hθ τ' (mat z), hz, one_mul, mul_one]
    · rw [← compAt_eq_psiT hθ τ' (mat (ι y')), h2 τ' ht, one_mul, mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, h3, one_mul, mul_one]

theorem herm_conjTranspose (x : Fin n → Fin n → ℝ) : (herm x)ᴴ = herm x := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  change star ((↑(x j i + x i j) : ℂ) / 2 + Complex.I * ↑(x j i - x i j) / 2) =
    (↑(x i j + x j i) : ℂ) / 2 + Complex.I * ↑(x i j - x j i) / 2
  apply Complex.ext <;> simp <;> ring

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  change (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) *
    Matrix.fromBlocks 0 1 (-1) 0 = -1
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem cT_map_psiT' (τ : D.what₂.Tau) {a : ℕ} (M : Mx D a a) :
    (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) M).map (Formalism.IndefR.Eqv.psiT D τ) = (M.map (Formalism.IndefR.Eqv.psiT D τ))ᴴ := by
  ext i j
  rw [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
  exact Formalism.IndefR.Eqv.psiT_sigR D τ (M j i)

theorem Jst_map_psiT (τ : D.what₂.Tau) :
    (JR (AF D.host.F) (Jst D n)).map (Formalism.IndefR.Eqv.psiT D τ) = blk4 0 1 (-1) 0 := by
  change ((GlobalTheory.StdUnn.blk4 (0 : Matrix (Fin n) (Fin n) D.host.E) 1 (-1) 0).map
    (inclR (AF D.host.F))).map (Formalism.IndefR.Eqv.psiT D τ) = _
  rw [block_matrix_map, Matrix.map_neg _ (map_neg _), Matrix.map_zero _ (map_zero _),
    Matrix.map_one _ (map_zero _) (map_one _), block_matrix_map, Matrix.map_neg _ (map_neg _),
    Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem tauComp {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (g : G D n) :
    ∃ y : GR n, reidx (mR y) = compAt θ τ (mat g) := by
  have hU : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mat g) * JR (AF D.host.F) (Jst D n) * mat g =
      JR (AF D.host.F) (Jst D n) := g.2
  have hUψ := congrArg (fun X => X.map (Formalism.IndefR.Eqv.psiT D τ)) hU
  simp only [Matrix.map_mul, cT_map_psiT', Jst_map_psiT] at hUψ
  rw [← compAt_eq_psiT hθ] at hUψ
  have hB : (GlobalTheory.StdUnn.blk4 (0 : Matrix (Fin n) (Fin n) ℂ) 1 (-1) 0).submatrix finSumFinEquiv
      finSumFinEquiv = JJ n := by
    delta GlobalTheory.StdUnn.blk4
    rw [Matrix.submatrix_submatrix]
    simp only [Equiv.symm_comp_self, Matrix.submatrix_id_id]
    rfl
  have hY : ((compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv)ᴴ * JJ n *
      (compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv = JJ n := by
    rw [← hB, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hUψ]
  have hL : (-(JJ n * ((compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv)ᴴ * JJ n)) *
      (compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv = 1 := by
    rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (JJ n), hY, JJ_mul_self, neg_neg]
  refine ⟨⟨⟨_, _, (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hL, hL⟩, hY⟩, ?_⟩
  change ((compAt θ τ (mat g)).submatrix finSumFinEquiv finSumFinEquiv).submatrix finSumFinEquiv.symm
    finSumFinEquiv.symm = _
  rw [Matrix.submatrix_submatrix]
  simp only [Equiv.self_comp_symm, Matrix.submatrix_id_id]

end PlaceFactsH

open PlaceFactsH

theorem splitTau {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    (g : G D n) : ∃ (y : GR n) (x : G D n), g = ι y * x ∧ ∀ y' : GR n, x * ι y' = ι y' * x := by
  obtain ⟨y, hy⟩ := tauComp hθ τ g
  have h1 : compAt θ τ (mat (ι y)) = compAt θ τ (mat g) := by
    obtain ⟨-, hι'⟩ := hι
    rw [(hι' y).1, hy]
  refine ⟨y, (ι y)⁻¹ * g, (mul_inv_cancel_left _ _).symm, ?_⟩
  apply commute_of_tau hθ hι
  rw [mat_mul', compAt_mul' hθ, ← h1, ← compAt_mul' hθ, ← mat_mul', inv_mul_cancel, mat_one',
    compAt_one' hθ]

namespace PlaceFactsH

theorem nb_mat (nb : hermA D n → G D n) (hnb : PositivityTheory.PfSWUS.IsNMap nb) (b b' : hermA D n) :
    mat (nb b * nb b') = blk4 1 (b.1 + b'.1) 0 1 := by
  rw [mat_mul', hnb b, hnb b', submatrix_fromBlocks_mul]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [add_comm (b'.1 : Mx D n n)]

theorem nb_mul_comm (nb : hermA D n → G D n) (hnb : PositivityTheory.PfSWUS.IsNMap nb) (b b' : hermA D n) :
    nb b * nb b' = nb b' * nb b := by
  apply mat_inj
  rw [nb_mat nb hnb, nb_mat nb hnb, add_comm (b.1 : Mx D n n)]

end PlaceFactsH

open PlaceFactsH

theorem nbTau {θ : InfFam D} (hθ : IsInfFam θ) {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι)
    (nb : hermA D n → G D n) (hnb : PositivityTheory.PfSWUS.IsNMap nb) (nb' : (Fin n → Fin n → ℝ) → GR n)
    (hnb' : ∀ x, mR (nb' x) = nU (herm x)) (x : Fin n → Fin n → ℝ) :
    ∃ b : hermA D n, ι (nb' x) = nb b ∧ b.1.map (finPart D) = 0 ∧ compAt θ τ b.1 = herm x ∧
      (∀ τ', τ' ≠ τ → compAt θ τ' b.1 = 0) ∧ ∀ b' : hermA D n, nb b' * ι (nb' x) = ι (nb' x) * nb b' := by
  classical
  obtain ⟨-, hι'⟩ := hι
  obtain ⟨h1y, h2y, h3y⟩ := hι' (nb' x)
  obtain ⟨β, hβ⟩ : ∃ β : Mx D n n, β = bOf (mat (ι (nb' x))) := ⟨_, rfl⟩
  have hψβ : ∀ τ', β.map (Formalism.IndefR.Eqv.psiT D τ') = if τ' = τ then herm x else 0 := by
    intro τ'
    rw [hβ, ← bOf_map, ← compAt_eq_psiT hθ]
    split_ifs with ht
    · subst ht
      rw [h1y, hnb', reidx_nU, upper_right_entry_block_matrix]
    · rw [h2y τ' ht, ← block_matrix_one, upper_right_entry_block_matrix]
  have hfβ : β.map (Formalism.L2.Theta.finPart D) = 0 := by
    rw [hβ, ← bOf_map, h3y, ← block_matrix_one, upper_right_entry_block_matrix]
  have hmat : mat (ι (nb' x)) = blk4 1 β 0 1 := by
    apply Formalism.IndefR.Eqv.mat_ext
    · intro τ'
      rw [block_matrix_map, hψβ τ', ← compAt_eq_psiT hθ, Matrix.map_zero _ (map_zero _),
        Matrix.map_one _ (map_zero _) (map_one _)]
      split_ifs with ht
      · subst ht
        rw [h1y, hnb', reidx_nU]
      · rw [h2y τ' ht, block_matrix_one]
    · rw [block_matrix_map, hfβ, h3y, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _),
        block_matrix_one]
  have hherm : GlobalTheory.MixModel.adj β = β := by
    apply Formalism.IndefR.Eqv.mat_ext
    · intro τ'
      rw [show GlobalTheory.MixModel.adj β = Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) β from rfl, cT_map_psiT',
        hψβ τ']
      split_ifs
      · exact herm_conjTranspose x
      · exact Matrix.conjTranspose_zero
    · rw [hfβ]
      ext i j
      change Formalism.L2.Theta.finPart D (Formalism.L2.Theta.cA D (β j i)) = 0
      have h0 : Formalism.L2.Theta.finPart D (β j i) = 0 := congrFun (congrFun hfβ j) i
      exact (Formalism.IndefR.Eqv.finPart_sigR D (β j i)).trans (by rw [h0, map_zero])
  have e : ι (nb' x) = nb ⟨β, hherm⟩ := by
    apply mat_inj
    rw [hmat, hnb ⟨β, hherm⟩]
  refine ⟨⟨β, hherm⟩, e, hfβ, ?_, ?_, ?_⟩
  · show compAt θ τ β = herm x
    rw [compAt_eq_psiT hθ, hψβ τ, if_pos rfl]
  · intro τ' ht
    show compAt θ τ' β = 0
    rw [compAt_eq_psiT hθ, hψβ τ', if_neg ht]
  · intro b'
    rw [e, nb_mul_comm nb hnb]

end PositivityTheory.Rg.Sw.Glob
end
end

