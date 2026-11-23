module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjEqSign
section
noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8

namespace GlobalTheory.CompanionTheory.LocalThetaTranslation

theorem phi_transpose (n : ℕ) (R : Type) [CommRing R] :
    (GlobalTheory.Tw.Phi n R)ᵀ = ((-1 : R) ^ (n + 1)) • GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + j + 1 = n
  · have h' : (j : ℕ) + i + 1 = n := by omega
    rw [if_pos h, if_pos h', ← pow_add]
    have e : n + 1 + (i : ℕ) = j + 2 * ((i : ℕ) + 1) := by omega
    rw [e, pow_add, pow_mul]
    simp
  · have h' : ¬ (j : ℕ) + i + 1 = n := by omega
    rw [if_neg h, if_neg h']
    simp

theorem phi_map (n : ℕ) {R : Type} [CommRing R] (c : R →+* R) : (GlobalTheory.Tw.Phi n R).map c = GlobalTheory.Tw.Phi n R := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_mul_self (n : ℕ) (R : Type) [CommRing R] :
    GlobalTheory.Tw.Phi n R * GlobalTheory.Tw.Phi n R = ((-1 : R) ^ (n + 1)) • (1 : Matrix (Fin n) (Fin n) R) := by
  have h := Phi_mul_transpose n R
  rw [phi_transpose, Matrix.mul_smul] at h
  have e : ((-1 : R) ^ (n + 1)) * ((-1 : R) ^ (n + 1)) = 1 := by
    rw [← mul_pow]; simp
  rw [← h, smul_smul, e, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_conj_eq_sign (n : ℕ) : ∃ s : E, s ≠ 0 ∧ conjE E s = (-1 : E) ^ (n + 1) * s := by
  rcases neg_one_pow_eq_or E (n + 1) with h | h
  · exact ⟨1, one_ne_zero, by rw [h, map_one, one_mul]⟩
  · have hx : ∃ x : E, conjE E x ≠ x := by
      by_contra hc
      push Not at hc
      exact IsCMField.complexConj_ne_one E (AlgEquiv.ext hc)
    obtain ⟨x, hx⟩ := hx
    have hcc : conjE E (conjE E x) = x := IsCMField.complexConj_apply_apply E x
    refine ⟨x - conjE E x, sub_ne_zero.2 hx.symm, ?_⟩
    rw [h, map_sub, hcc]
    ring


omit [NumberField E] [IsCMField E] in
theorem scalar_val {n : ℕ} (t : Eˣ) :
    (GeneralLinearGroup.scalar (Fin n) t).val = (t : E) • (1 : Matrix (Fin n) (Fin n) E) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h]


omit [NumberField E] [IsCMField E] in
theorem scalar_commute {n : ℕ} (t : Eˣ) (g : GL (Fin n) E) :
    GeneralLinearGroup.scalar (Fin n) t * g = g * GeneralLinearGroup.scalar (Fin n) t := by
  apply Units.ext
  simp only [Units.val_mul, scalar_val]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem thetaE_phiU (n : ℕ) : (thetaE E n (PhiU n E)).val = GlobalTheory.Tw.Phi n E := by
  change ((((PhiU n E)⁻¹).val).map (conjE E))ᵀ = _
  rw [phiU_inv_val, Matrix.transpose_map, Matrix.transpose_transpose, phi_map]

theorem thetaE_scalar {n : ℕ} (t : Eˣ) :
    (thetaE E n (GeneralLinearGroup.scalar (Fin n) t)).val =
      (conjE E (t : E))⁻¹ • (1 : Matrix (Fin n) (Fin n) E) := by
  change ((((GeneralLinearGroup.scalar (Fin n) t)⁻¹).val).map (conjE E))ᵀ = _
  rw [← map_inv, scalar_val]
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · have h' : j ≠ i := fun e => h e.symm
    simp [h, h']

theorem translEx : TranslEx := by
  intro E _ _ _ n
  obtain ⟨s, hs, hc⟩ := exists_conj_eq_sign (E := E) n
  have hcs : conjE E s ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hs
  refine ⟨GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E, ?_, ?_⟩
  · intro g
    have h1 : thE E n g = PhiU n E * thetaE E n g * (PhiU n E)⁻¹ := thetaGL_eq n E _ g
    rw [h1]
    have h2 := scalar_commute (Units.mk0 s hs) (PhiU n E * thetaE E n g * (PhiU n E)⁻¹)
    have h3 : GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E * thetaE E n g *
        (GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * PhiU n E)⁻¹ =
        GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs) * (PhiU n E * thetaE E n g * (PhiU n E)⁻¹) *
          (GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs))⁻¹ := by
      group
    rw [h3, h2, mul_inv_cancel_right]
  · apply Units.ext
    rw [map_mul, Units.val_mul, Units.val_mul, Units.val_mul, thetaE_phiU, thetaE_scalar, scalar_val, phiU_val]
    simp only [Units.val_mk0, Units.val_one]
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      phi_mul_self, smul_smul, smul_smul, hc]
    have hp : ((-1 : E) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    have : s * (((-1 : E) ^ (n + 1)) * s)⁻¹ * ((-1 : E) ^ (n + 1)) = 1 := by
      field_simp
    rw [this, one_smul]

end GlobalTheory.CompanionTheory.LocalThetaTranslation
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigenbasis
section
open Matrix Polynomial
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticTwist

theorem exists_eigenbasis {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (hs : N.charpoly.Separable) :
    ∃ (h : GL (Fin n) ℂ) (γ : Fin n → ℂ), Function.Injective γ ∧ (∀ i, N.charpoly.IsRoot (γ i)) ∧
      N * h.val = h.val * diagonal γ := by
  have hne : N.charpoly ≠ 0 := (Matrix.charpoly_monic N).ne_zero
  have hcard : N.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), splits_iff_card_roots.1 (IsAlgClosed.splits _),
      charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := Finset.equivFinOfCardEq hcard
  let γ : Fin n → ℂ := fun i => (e.symm i).1
  have hinj : Function.Injective γ := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hroot : ∀ i, N.charpoly.IsRoot (γ i) := fun i =>
    (mem_roots hne).1 (Multiset.mem_toFinset.1 (e.symm i).2)
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ (scalar (Fin n) (γ i) - N) *ᵥ v = 0 := fun i =>
    exists_mulVec_eq_zero_iff.2 (by rw [← eval_charpoly]; exact hroot i)
  choose v hv0 hv using hev
  have hNv : ∀ i, N *ᵥ v i = γ i • v i := fun i => by
    have h1 := hv i
    rw [sub_mulVec, sub_eq_zero] at h1
    rw [← h1]
    ext k
    simp [scalar_apply, mulVec_diagonal]
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' N) γ hinj v
      (fun i => Module.End.hasEigenvector_iff.2
        ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hNv i), hv0 i⟩)
  have hu : IsUnit (Matrix.of v)ᵀ := linearIndependent_cols_iff_isUnit.1 hli
  obtain ⟨h, hh⟩ := hu
  refine ⟨h, γ, hinj, hroot, ?_⟩
  have hh' : h.val = (Matrix.of v)ᵀ := hh
  rw [hh']
  ext i j
  have h2 := congrFun (hNv j) i
  rw [mul_diagonal]
  simpa [Matrix.mul_apply, mulVec, dotProduct, mul_comm] using h2

variable {n : ℕ}

theorem theta_val (g : GL (Fin n) ℂ) :
    (thetaR (starRingEnd ℂ) n g).val = (g⁻¹).valᴴ := by
  ext i j
  simp [thetaR_val, conjTranspose_apply]

theorem theta_inv_val (g : GL (Fin n) ℂ) :
    ((thetaR (starRingEnd ℂ) n g)⁻¹).val = g.valᴴ := by
  rw [← map_inv, theta_val, inv_inv]

theorem theta_theta (g : GL (Fin n) ℂ) :
    thetaR (starRingEnd ℂ) n (thetaR (starRingEnd ℂ) n g) = g :=
  Units.ext (by rw [theta_val, theta_inv_val, conjTranspose_conjTranspose])

theorem offDiag_eq_zero (D : Matrix (Fin n) (Fin n) ℂ) (γ : Fin n → ℂ) (hγ : ∀ i, ‖γ i‖ = 1)
    (hinj : Function.Injective γ) (hD : D = diagonal γ * Dᴴ) {i j : Fin n} (hij : i ≠ j) : D i j = 0 := by
  have h2 : Dᴴ = D * diagonal (star γ) := by
    conv_lhs => rw [hD]
    rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
  have h3 : D i j = γ i * (D i j * star (γ j)) := by
    conv_lhs => rw [hD, h2]
    rw [diagonal_mul, mul_diagonal]
    rfl
  by_contra hne
  have h4 : γ i * star (γ j) = 1 := by
    apply mul_left_cancel₀ hne
    linear_combination -h3
  have h5 : star (γ j) * γ j = 1 := by
    have := Complex.conj_mul' (γ j)
    rw [hγ j] at this
    simpa using this
  apply hij
  apply hinj
  linear_combination -γ i * h5 + γ j * h4

theorem ellDiag : EllDiag := by
  intro n d hd
  obtain ⟨hs, hn⟩ := hd
  obtain ⟨h, γ, hinj, hroot, hN⟩ := exists_eigenbasis _ hs
  have hγ : ∀ i, ‖γ i‖ = 1 := fun i => hn _ (hroot i)
  set θ := thetaR (starRingEnd ℂ) n with hθ
  let d₁ : GL (Fin n) ℂ := twConj θ h d
  have hnorm : (d₁ * θ d₁).val = diagonal γ := by
    have h1 : d₁ * θ d₁ = h⁻¹ * (d * θ d) * h := by
      simp [d₁, twConj, map_mul, map_inv, hθ, theta_theta, mul_assoc]
    rw [h1, Units.val_mul, Units.val_mul, mul_assoc, hN, ← mul_assoc, ← Units.val_mul]
    simp
  have hD : d₁.val = diagonal γ * d₁.valᴴ := by
    rw [← hnorm, ← theta_inv_val, ← Units.val_mul]
    simp [hθ]
  let b : Fin n → ℂ := fun i => d₁.val i i
  have hdiag : d₁.val = diagonal b := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [b]
    · rw [offDiag_eq_zero _ γ hγ hinj hD hij, diagonal_apply_ne _ hij]
  have hb0 : ∀ i, b i ≠ 0 := by
    intro i hi
    have h0 : d₁.val.det = 0 := by
      rw [hdiag, det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have h1 := (Matrix.isUnit_iff_isUnit_det _).1 d₁.isUnit
    rw [h0] at h1
    exact not_isUnit_zero h1
  have hbγ : ∀ i, b i = γ i * (starRingEnd ℂ) (b i) := by
    intro i
    have h1 := congrFun (congrFun hD i) i
    rw [diagonal_mul] at h1
    simpa [conjTranspose_apply] using h1
  let s : Fin n → ℂ := fun i => ((Real.sqrt ‖b i‖ : ℝ) : ℂ)
  have hnb : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (hb0 i)
  have hs0 : ∀ i, s i ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hnb i)).ne'
  have hss : ∀ i, s i * s i = (‖b i‖ : ℂ) := fun i => by
    simp only [s]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnb i).le]
  let t : GL (Fin n) ℂ := ⟨diagonal s, diagonal fun i => (s i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact mul_inv_cancel₀ (hs0 i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact inv_mul_cancel₀ (hs0 i)⟩
  have htinv : (t⁻¹).val = diagonal fun i => (s i)⁻¹ := rfl
  have htθ : (θ t).val = diagonal fun i => (s i)⁻¹ := by
    rw [hθ, theta_val, htinv, diagonal_conjTranspose]
    congr 1
    ext i
    simp [s]
  let z : Fin n → ℂ := fun i => b i / (‖b i‖ : ℂ)
  have hz2 : ∀ i, z i ^ 2 = γ i := by
    intro i
    have hne : (‖b i‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hnb i).ne'
    have h1 := Complex.mul_conj' (b i)
    simp only [z]
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hne), ← h1]
    conv_lhs => rw [sq]; enter [1]; rw [hbγ i]
    ring
  refine ⟨(h * t)⁻¹, twConj θ t d₁, z, ?_, ?_, ?_, ?_⟩
  · change (t⁻¹ * d₁ * θ t).val = _
    rw [Units.val_mul, Units.val_mul, htinv, hdiag, htθ, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    have := hss i
    have h0 := hs0 i
    simp only [z]
    rw [← this]
    field_simp
  · intro i
    simp only [z]
    rw [norm_div, Complex.norm_real, norm_norm, div_self (hnb i).ne']
  · intro i j hij
    apply hinj
    have := hz2 i
    have := hz2 j
    simp only at hij
    rw [← hz2 i, ← hz2 j, hij]
  · simp [twConj, d₁, map_mul, map_inv, mul_assoc]

end GlobalTheory.CompanionTheory.EllipticTwist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedBallIndicator
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.MirLevi.Bump

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

def IntM (m : GL (Fin n) k) : Prop :=
  ∀ i, Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i) ∈ polyBall (k := k) n 1

theorem intM_one : IntM (1 : GL (Fin n) k) := by
  intro i j
  show valuation k (((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ((1 : kˣ) : k)
  by_cases h : i = j
  · simp [h]
  · simp [one_apply, h]

theorem IntM.mulVec_mem {m : GL (Fin n) k} (hm : IntM m) {s : kˣ} {v : Fin n → k}
    (hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s) :
    Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v) ∈ polyBall (k := k) n s :=
  fun i => dotProduct_mem_cball (a := 1) (b := s) (c := s) (by simp) (hm i) hv

theorem isOpen_intM : IsOpen {m : GL (Fin n) k | IntM m} := by
  have h : {m : GL (Fin n) k | IntM m} = ⋂ i, (fun m : GL (Fin n) k =>
      Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i)) ⁻¹'
        (polyBall (k := k) n 1 : Set (Multiplicative (Fin n → k))) := by
    ext m
    simp [IntM]
  rw [h]
  refine isOpen_iInter_of_finite fun i => (isOpen_polyBall n 1).preimage ?_
  exact continuous_ofAdd.comp (continuous_pi fun j => Units.continuous_val.matrix_elem i j)

theorem continuous_colv : Continuous (colv : Mir k n → Fin n → k) :=
  continuous_pi fun i => (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)

theorem continuous_mvec : Continuous (mvec : Mir k n → Fin n → k) := by
  have h1 : Continuous fun x : Mir k n =>
      (((mirabolicProjection k n x)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    Units.continuous_val.comp (continuous_inv.comp (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n))
  exact h1.matrix_mulVec continuous_colv

theorem continuous_lv : Continuous (lv k n) :=
  continuous_induced_rng.2 (GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n)

def bumpF (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E) (g : Mir k n) : E :=
  @ite _ (Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s) (Classical.propDecidable _)
    (ρ (lv k n (mirabolicProjection k n g)) e) 0

variable (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E)

theorem bumpF_levi_mul (m : GL (Fin n) k) (g : Mir k n) :
    bumpF ρ s e (levi k n m * g) = ρ (lv k n m) (bumpF ρ s e g) := by
  unfold bumpF
  rw [mvec_levi_mul, map_mul, mirProj_levi, map_mul, map_mul, Module.End.mul_apply]
  split_ifs <;> simp

theorem bumpF_equi (h : LH k n) (g : Mir k n) :
    bumpF ρ s e ((h : Mir k n) * g) = ρ h (bumpF ρ s e g) := by
  obtain ⟨m, hm⟩ := h.2
  have e1 : h = lv k n m := Subtype.ext hm.symm
  rw [e1]
  exact bumpF_levi_mul ρ s e m g

theorem bumpF_levi_uv (q : GL (Fin n) k) (w : Fin n → k) :
    bumpF ρ s e (levi k n q * uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _)
        (ρ (lv k n q) e) 0 := by
  unfold bumpF
  rw [mvec_levi_mul_uv, map_mul, mirProj_levi, mirProj_uv, mul_one]

theorem bumpF_uv (w : Fin n → k) :
    bumpF ρ s e (uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  have h := bumpF_levi_uv ρ s e 1 w
  rw [map_one (levi k n), one_mul, map_one (lv k n), map_one ρ] at h
  simpa using h

theorem mul_formula (p m : GL (Fin n) k) (v a : Fin n → k) :
    (levi k n p * uv n v) * (levi k n m * uv n a) = levi k n (p * m) *
      uv n (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) := by
  rw [uv_add, map_mul, mul_assoc (levi k n p), ← mul_assoc (uv n v), uv_mul_levi]
  simp only [mul_assoc]

theorem bumpF_fix (p m : GL (Fin n) k) (v a : Fin n → k) (h1 : IntM m) (h2 : IntM m⁻¹)
    (hm : ρ (lv k n m) e = e) (ha : Multiplicative.ofAdd a ∈ polyBall (k := k) n s) :
    bumpF ρ s e ((levi k n p * uv n v) * (levi k n m * uv n a)) = bumpF ρ s e (levi k n p * uv n v) := by
  rw [mul_formula, bumpF_levi_uv, bumpF_levi_uv, map_mul, map_mul, Module.End.mul_apply, hm]
  have hiff : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) ∈
      polyBall (k := k) n s ↔ Multiplicative.ofAdd v ∈ polyBall (k := k) n s := by
    constructor
    · intro h
      have h3 : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) ∈
          polyBall (k := k) n s := by
        have h4 := mul_mem h (inv_mem ha)
        rwa [ofAdd_add, mul_inv_cancel_right] at h4
      have h5 := h1.mulVec_mem h3
      rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h5
    · intro h
      rw [ofAdd_add]
      exact mul_mem (h2.mulVec_mem h) ha
  by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s
  · rw [if_pos hv, if_pos (hiff.2 hv)]
  · rw [if_neg hv, if_neg (fun c => hv (hiff.1 c))]

def nbhd : Set (Mir k n) :=
  {x | IntM (mirabolicProjection k n x) ∧ IntM (mirabolicProjection k n x)⁻¹ ∧ ρ (lv k n (mirabolicProjection k n x)) e = e ∧
    Multiplicative.ofAdd (mvec x) ∈ polyBall (k := k) n s}

theorem isOpen_nbhd (hρ : IsSmooth ρ) : IsOpen (nbhd ρ s e) := by
  unfold nbhd
  have hp := GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n
  exact (isOpen_intM.preimage hp).inter ((isOpen_intM.preimage (continuous_inv.comp hp)).inter
    (((hρ e).preimage (continuous_lv.comp hp)).inter
      ((isOpen_polyBall n s).preimage (continuous_ofAdd.comp continuous_mvec))))

theorem one_mem_nbhd : (1 : Mir k n) ∈ nbhd ρ s e := by
  have hm : mvec (1 : Mir k n) = 0 := by
    have h := mvec_uv (k := k) n 0
    rwa [uv_zero] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_one]; exact intM_one
  · rw [map_one, inv_one]; exact intM_one
  · simp
  · rw [hm]; exact one_mem _

theorem bumpF_mul_nbhd (g x : Mir k n) (hx : x ∈ nbhd ρ s e) :
    bumpF ρ s e (g * x) = bumpF ρ s e g := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have h := bumpF_fix ρ s e (mirabolicProjection k n g) (mirabolicProjection k n x) (mvec g) (mvec x) h1 h2 h3 h4
  rwa [← decomp g, ← decomp x] at h

theorem bumpF_mem : bumpF ρ s e ∈ indSpace (LH k n) ρ := fun h g => bumpF_equi ρ s e h g

theorem bumpF_smooth (hρ : IsSmooth ρ) :
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) ∈ smoothPart (ind (LH k n) ρ) := by
  have hfix : nbhd ρ s e ⊆ (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
      (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) : Set (Mir k n)) := by
    intro x hx
    apply Subtype.ext
    funext g
    exact bumpF_mul_nbhd ρ s e g x hx
  exact (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ)).isOpen_of_mem_nhds (g := 1)
    (Filter.mem_of_superset ((isOpen_nbhd ρ s e hρ).mem_nhds (one_mem_nbhd ρ s e)) hfix)

theorem bumpF_support : ∃ C : Set (Mir k n), IsCompact C ∧ ∀ g, bumpF ρ s e g ≠ 0 →
    ∃ h ∈ LH k n, ∃ c ∈ C, g = h * c := by
  refine ⟨unipIn k n '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))),
    (isCompact_polyBall n s).image (continuous_unipIn n), fun g hg => ?_⟩
  have hL : Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s := by
    by_contra hc
    exact hg (if_neg hc)
  exact ⟨levi k n (mirabolicProjection k n g), ⟨_, rfl⟩, uv n (mvec g), ⟨_, hL, rfl⟩, decomp g⟩

theorem exists_bump_restr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E),
    ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v =
      @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  intro k _ _ _ _ n E _ _ ρ hρ s e
  exact ⟨⟨⟨⟨bumpF ρ s e, bumpF_mem ρ s e⟩, bumpF_smooth ρ s e hρ⟩, bumpF_support ρ s e⟩,
    fun v => bumpF_uv ρ s e v⟩

end GlobalTheory.CompanionTheory.MirLevi.Bump

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSplit
section
open PositivityTheory.Rg.BcB.G8

open MeasureTheory

namespace GlobalTheory.CompanionTheory.HaarProd

theorem haarSplit : HaarSplit := by
  intro G A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ α _ e
  have : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  let β₀ : Measure B := Measure.haar
  have hc := Measure.isMulLeftInvariant_eq_smul (μ.map e) (α.prod β₀)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map e) (α.prod β₀)
  refine ⟨Measure.haarScalarFactor (μ.map e) (α.prod β₀) • β₀, ?_, ?_⟩
  · exact Measure.IsHaarMeasure.nnreal_smul _ hpos.ne'
  · rw [Measure.prod_smul_right]
    exact hc

end GlobalTheory.CompanionTheory.HaarProd
end

