module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0182
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
  Formalism.L2.Host GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev blkEq {a b n : ℕ} (h : a + b = n) : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)

def dgMat {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) (A : Matrix (Fin a) (Fin a) R)
    (D : Matrix (Fin b) (Fin b) R) : Matrix (Fin n) (Fin n) R :=
  reindex (blkEq h) (blkEq h) (fromBlocks A 0 0 D)

theorem dgMat_mul {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) (A A' : Matrix (Fin a) (Fin a) R)
    (D D' : Matrix (Fin b) (Fin b) R) : dgMat h A D * dgMat h A' D' = dgMat h (A * A') (D * D') := by
  simp only [dgMat, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem dgMat_one {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) :
    dgMat h (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  rw [dgMat, fromBlocks_one, reindex_apply, submatrix_one_equiv]

def dgM {a b n : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* GLw n w where
  toFun k := ⟨dgMat h k.1.val k.2.val, dgMat h (k.1⁻¹).val (k.2⁻¹).val,
    by rw [dgMat_mul, Units.mul_inv, Units.mul_inv, dgMat_one],
    by rw [dgMat_mul, Units.inv_mul, Units.inv_mul, dgMat_one]⟩
  map_one' := Units.ext (by simp [dgMat_one])
  map_mul' x y := Units.ext (by simp [dgMat_mul])

theorem dgM_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) :
    (dgM h w k).val = dgMat h k.1.val k.2.val := rfl

def lev₁ {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) :
    Subgroup (GLw a w) :=
  GlobalTheory.LFun.KGL w (n := a) ⊓ N.comap ((dgM h w).comp (MonoidHom.inl _ _)) ⊓ μ.ker.comap GeneralLinearGroup.det

def lev₂ {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) :
    Subgroup (GLw b w) :=
  GlobalTheory.LFun.KGL w (n := b) ⊓ N.comap ((dgM h w).comp (MonoidHom.inr _ _)) ⊓ μ.ker.comap GeneralLinearGroup.det

theorem blk_val {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = reindex (blkEq h) (blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hu : IsUnit (reindex (blkEq h) (blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [isUnit_iff_isUnit_det, det_reindex_self, det_fromBlocks_zero₂₁]
    exact (m.1.isUnit.map detMonoidHom).mul (m.2.isUnit.map detMonoidHom)
  unfold blk
  simp only
  rw [dite_eq_left hu]
  rfl

end GlobalTheory.BCT.CtLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegel
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SiegelChar

theorem eq_one_of_siegel : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1) := by
  intro F E _ _ _ _ _ σ hCM n J ε hJ hdet c hc hP
  letI i2 : Invertible (2 : AE F E) :=
    (Invertible.map (algebraMap (AF F) (AE F E)) (2 : AF F)).copy 2 (map_ofNat _ 2).symm
  have hw1 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
      Matrix.fromBlocks 1 0 0 (-1) = 1 := by
    rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  let w0 : GL (Fin n ⊕ Fin n) (AE F E) := ⟨_, _, hw1, hw1⟩
  have hwm : w0 ∈ UG (cA σ) (dbl (incM F J)) := by
    show (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ * dbl (incM F J) *
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)).map (cA σ) = dbl (incM F J)
    rw [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
    simp [Matrix.fromBlocks_multiply, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ)),
      Matrix.map_neg _ (map_neg (cA σ))]
  have hw0 : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (-1) := rfl
  let w : UG (cA σ) (dbl (incM F J)) := ⟨w0, hwm⟩
  have hww : w * w = 1 := Subtype.ext (Units.ext hw1)
  have hwD : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) = Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hw0, Matrix.fromBlocks_mul_fromRows]; simp
  have hwN : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) = Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hw0, Matrix.fromBlocks_mul_fromRows]; simp
  have hq : ∀ (q : UG (cA σ) (dbl (incM F J))) (s : GL (Fin n) (AE F E)),
      ((q : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) =
        Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * (s : Matrix (Fin n) (Fin n) (AE F E)) → c q = 1 := by
    intro q s hs
    have key : (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
        ((q : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) *
        (w0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) =
        Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (1 : Matrix (Fin n) (Fin n) (AE F E)) * (s : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hwD, hs, ← Matrix.mul_assoc, hwN]
    have h1 : c (w * q * w) = 1 := hP _ s key
    have h2 : c w * c w = 1 := by rw [← map_mul, hww, map_one]
    rw [map_mul, map_mul, mul_comm (c w), mul_assoc, h2, mul_one] at h1
    exact h1
  have hΩ : ∀ h : UG (cA σ) (dbl (incM F J)), (∃ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)),
      (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 ∧
      IsUnit (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * ((h * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))).det) →
      c h = 1 := by
    rintro h ⟨p, t, hp, hu⟩
    obtain ⟨p', q, t', s, hp', hq', e⟩ := _root_.GlobalTheory.BigCell.bigCell_factor (AF F) (AE F E) (cA σ) (Fin n) (incM F J) (h * p) hu
    have h1 : c (h * p) = 1 := by rw [e, map_mul, hP p' t' hp', hq q s hq', one_mul]
    rwa [map_mul, hP p t hp, mul_one] at h1
  have hcl : IsClosed {g : UG (cA σ) (dbl (incM F J)) | c g = 1} := isClosed_eq hc continuous_const
  refine MonoidHom.ext fun g => ?_
  exact hcl.closure_subset_iff.2 (fun h hh => hΩ h hh) (GlobalTheory.T.dense_invertible_antidiagonal_corner_doubledUnitary F E σ hCM n J ε hJ hdet g)

end GlobalTheory.SiegelChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdIntegralMonicCoprimeDerivativeBezoutFactor
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem monic_dvd_integral_factor_bezout : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (P₀ : (w.adicCompletionIntegers E)[X]), P₀.Monic →
    IsCoprime P₀ (derivative P₀) → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∃ (Q₁₀ Q₂₀ A B : (w.adicCompletionIntegers E)[X]) (c : w.adicCompletion E), c ≠ 0 ∧ P₀ = Q₁₀ * Q₂₀ ∧
      A * Q₁₀ + B * Q₂₀ = 1 ∧ Q₁ = C c * Q₁₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
  intro E _ _ w P₀ hP hc Q₁ hQ
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := IsFractionRing.injective (w.adicCompletionIntegers E) (w.adicCompletion E)
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (w.adicCompletion E) hP hQ
  have hPm : (P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))).Monic := hP.map _
  have hQ0 : Q₁ ≠ 0 := by
    rintro rfl
    exact hPm.ne_zero (zero_dvd_iff.mp hQ)
  have hlc : Q₁.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  have hgm' : g.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = Q₁ * C Q₁.leadingCoeff⁻¹ := by
    calc _ = g.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) * C Q₁.leadingCoeff * C Q₁.leadingCoeff⁻¹ := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]
      _ = Q₁ * C Q₁.leadingCoeff⁻¹ := by rw [hg]
  have hgmon : g.Monic := by
    apply Polynomial.monic_of_injective hinj
    rw [hgm']
    exact monic_mul_leadingCoeff_inv hQ0
  have hdvd : g ∣ P₀ := by
    rw [← map_dvd_map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) hinj hgmon]
    exact dvd_trans ⟨C Q₁.leadingCoeff, hg.symm⟩ hQ
  obtain ⟨Q₂, hQ₂⟩ := hdvd
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨g, Q₂, a * Q₂ + b * derivative Q₂, b * derivative g, Q₁.leadingCoeff, hlc, hQ₂, ?_, ?_⟩
  · rw [hQ₂, derivative_mul] at hab
    linear_combination hab
  · exact hg.symm.trans (mul_comm _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
section
noncomputable section

open Matrix
open scoped Quaternion

namespace GlobalTheory.PlaneSU

open Formalism.UG

section Emb

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def emb (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) (X : Matrix (Fin 2) (Fin 2) R) : Matrix n n R :=
  1 + A * (X - 1) * B

theorem emb_one (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) : emb A B 1 = 1 := by
  simp [emb]

theorem emb_mul {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X Y : Matrix (Fin 2) (Fin 2) R) : emb A B (X * Y) = emb A B X * emb A B Y := by
  have e1 : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  have e2 : A * (X - 1) * B * (A * (Y - 1) * B) = A * ((X - 1) * (Y - 1)) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]
  unfold emb
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, e2, e1,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

theorem det_emb {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).det = X.det := by
  unfold emb
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hBA, Matrix.mul_one, add_sub_cancel]

theorem emb_map {S : Type} [CommRing S] (f : R →+* S) (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).map f = emb (A.map f) (B.map f) (X.map f) := by
  simp [emb, Matrix.map_mul, Matrix.map_add (f := _), Matrix.map_sub, Matrix.map_one]

theorem cT_add (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P + Q) = cT c P + cT c Q := by
  ext i j; simp [cT]

theorem cT_sub (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P - Q) = cT c P - cT c Q := by
  ext i j; simp [cT]

theorem emb_unitary (c : R →+* R) {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} {J : Matrix n n R}
    {H X : Matrix (Fin 2) (Fin 2) R} (hBA : B * A = 1) (h1 : cT c A * J = H * B) (h2 : J * A = cT c B * H)
    (hX : cT c X * H * X = H) : cT c (emb A B X) * J * emb A B X = J := by
  have hc : cT c (emb A B X) = 1 + cT c B * (cT c X - 1) * cT c A := by
    unfold emb
    rw [cT_add, cT_one, cT_mul, cT_mul, cT_sub, cT_one, Matrix.mul_assoc]
  set P := X - 1 with hP
  set P' := cT c X - 1 with hP'
  have key : H * P + P' * H + P' * H * P = 0 := by
    rw [hP, hP']
    calc H * (X - 1) + (cT c X - 1) * H + (cT c X - 1) * H * (X - 1) = cT c X * H * X - H := by noncomm_ring
      _ = 0 := by rw [hX, sub_self]
  have h1' : ∀ Z : Matrix n n R, cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h1'' : ∀ {k : Type} [Fintype k] (Z : Matrix n k R), cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h2' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), J * (A * Z) = cT c B * (H * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
  have hBA' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), B * (A * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [hc]
  unfold emb
  rw [← hP]
  have e : (1 + cT c B * P' * cT c A) * J * (1 + A * P * B) =
      J + cT c B * ((H * P + P' * H + P' * H * P) * B) := by
    have hAB' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), cT c A * (cT c B * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, ← cT_mul, hBA, cT_one, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, h1, h1'', h2', hBA', hAB']
    abel
  rw [e, key, Matrix.zero_mul, Matrix.mul_zero, add_zero]

end Emb

section Quat

variable {S T : Type} [CommRing S] [CommRing T]

def qm (ι : S →+* T) (θ : T) {a b : S} (x : ℍ[S, a, b]) : Matrix (Fin 2) (Fin 2) T :=
  !![ι x.re + ι x.imI * θ, ι b * (ι x.imJ + ι x.imK * θ); ι x.imJ - ι x.imK * θ, ι x.re - ι x.imI * θ]

variable (ι : S →+* T) (θ : T) {a b : S}

theorem qm_one : qm ι θ (1 : ℍ[S, a, b]) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm]

theorem qm_sub (x y : ℍ[S, a, b]) : qm ι θ (x - y) = qm ι θ x - qm ι θ y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_smul (r : S) (x : ℍ[S, a, b]) : qm ι θ (r • x) = ι r • qm ι θ x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_mul (hθ : θ * θ = ι a) (x y : ℍ[S, a, b]) : qm ι θ (x * y) = qm ι θ x * qm ι θ y := by
  ext i j
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  fin_cases i <;> fin_cases j <;> simp [qm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp only [hθ2] <;> ring

theorem det_qm (hθ : θ * θ = ι a) (x : ℍ[S, a, b]) : (qm ι θ x).det = ι (GlobalTheory.QSA.nrm x) := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  simp [qm, Matrix.det_fin_two, GlobalTheory.QSA.nrm]
  ring_nf
  simp only [hθ2]
  ring

theorem qm_unitary (c : T →+* T) (hc : ∀ s, c (ι s) = ι s) (hcθ : c θ = -θ) (hθ : θ * θ = ι a)
    {h₁ h₂ : T} (hb : ι b * h₁ = -h₂) {x : ℍ[S, a, b]} (hx : GlobalTheory.QSA.nrm x = 1) :
    cT c (qm ι θ x) * Matrix.diagonal ![h₁, h₂] * qm ι θ x = Matrix.diagonal ![h₁, h₂] := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  have hn : ι x.re ^ 2 - ι a * ι x.imI ^ 2 - ι b * ι x.imJ ^ 2 + ι a * ι b * ι x.imK ^ 2 = 1 := by
    have := congrArg ι hx
    simp only [GlobalTheory.QSA.nrm, map_sub, map_add (f := _), map_mul, map_pow, map_one] at this
    exact this
  have hh2 : h₂ = -(ι b * h₁) := by rw [hb, neg_neg]
  subst hh2
  ext i j
  fin_cases i <;> fin_cases j
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination h₁ * hn
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination (-(ι b * h₁)) * hn

end Quat

section Plane

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [Field E] [Algebra F E] {M : ℕ}

def planeA (e₁ e₂ : Fin M → E) : Matrix (Fin M) (Fin 2) E := Matrix.of fun i k => ![e₁, e₂] k i

def planeH (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin 2) E :=
  Matrix.diagonal ![hE σ J e₁ e₁, hE σ J e₂ e₂]

def planeB (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin M) E :=
  Matrix.diagonal ![(hE σ J e₁ e₁)⁻¹, (hE σ J e₂ e₂)⁻¹] * cT (σ : E →+* E) (planeA e₁ e₂) * J

end Plane

end GlobalTheory.PlaneSU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfConstOfTendsto
section
noncomputable section

open MeasureTheory Filter Topology GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open Formalism.MainNotions.S (IsDS)
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.Pc1

def LocalPC4 : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), Gap4 r lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X))
      (hD : IsDS ε (fun a => (lam a : ℝ)) D) (μ : Measure (UJ ε)) [μ.IsHaarMeasure],
      ∃ f, GlobalTheory.PsCo.Pc.IsPC' ε lam μ D hD f

theorem eq_of_const_of_tendsto {a L : ℂ} {u : ℝ → ℂ} (h : ∀ t, 1 ≤ t → u t = a) (hL : Tendsto u atTop (𝓝 L)) : a = L :=
  tendsto_nhds_unique (tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun t ht => (h t ht).symm)) hL

theorem injective_of_regSS {n : ℕ} {z : Fin n → ℂ} (h : IsRegSS (Matrix.diagonal z)) : Function.Injective z := by
  rw [IsRegSS, Matrix.charpoly_diagonal] at h
  exact Polynomial.separable_prod_X_sub_C_iff.1 h

theorem dMode_ne_zero {n : ℕ} (ε : Fin n → Bool) {θ : Fin n → ℝ}
    (h : Function.Injective fun a => Complex.exp (θ a * Complex.I)) : (dMode ε θ : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 fun e => ?_)))
  have h1 := x.2.1
  rw [h e, x.2.2] at h1
  exact Bool.noConfusion h1

theorem torusPt_mem_KG {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) : torusPt ε θ ∈ KG ε := by
  change toM (torusPt ε θ) ∈ Formalism.REAL.Kset ε
  have e : toM (torusPt ε θ) = Matrix.diagonal fun a => Complex.exp (θ a * Complex.I) := rfl
  rw [e]
  refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem localPC4_of (hAlg : StAlg) (hProf : StProfile) (hFam : StFam) (hHom : StHomot) (hLim : StLim)
    (hSh : StShape) (hOA : StOrbAd) (hOC : StOrbCpt) (hNE : StNonEll) (hTr : StTr) (hTA : StTrAd)
    (hK : StKData) : LocalPC4 := by
  intro r hr ε lam hgap X _ _ D hD μ _
  haveI := hD.1
  haveI := hD.2.1
  obtain ⟨M, P, hP, hcl, htor, hone, hzero⟩ := hK r hr ε lam hgap X D hD
  obtain ⟨p, q, hpq, htop⟩ := hAlg r ε M P hP
  obtain ⟨G, hG⟩ := hProf (nMode ε)
  obtain ⟨d, hd, hfam⟩ := hFam r ε G p hG
  obtain ⟨c, hc, hlim⟩ := hLim r ε μ G hG
  obtain ⟨hl1, hl2⟩ := hlim p
  let φ : ℝ → Mat r → ℂ := fun t => c⁻¹ • famF ε G p t
  have hφ : ∀ t, 1 ≤ t → φ t ∈ ShapeM ε d := fun t ht => Submodule.smul_mem _ _ (hfam t (by linarith)).1
  have hdiff : ∀ t, 1 ≤ t → φ 1 - φ t ∈ AdSpanM ε := fun t ht => by
    rw [← smul_sub]; exact Submodule.smul_mem _ _ (hHom r ε G p q hG hpq t ht)
  have hsum : ∀ t, (fun g : UJ ε => φ 1 (toM g)) = (fun g => φ t (toM g)) + fun g => (φ 1 - φ t) (toM g) :=
    fun t => funext fun g => by simp
  have key : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
      (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∃ (B : U →L[ℂ] U) (a : ℂ),
        (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M P) • π k v ∂(muK ε)) ∧ HasTrace B a ∧
          HasTrace (repOp π μ fun g => φ 1 (toM g)) a := by
    intro U _ _ _ π hu hi
    obtain ⟨w, hw, hw1, hw2⟩ := hTr r ε μ U π hu hi d
    obtain ⟨B, hB, hBt⟩ := hw2 _ (hd _ le_rfl)
    rw [htop] at hB hBt
    refine ⟨B, _, hB, hBt, ?_⟩
    have hint : ∀ t, 1 ≤ t → Integrable (fun g : UJ ε => φ t (toM g) * w g) μ := fun t ht =>
      ((hSh r ε d _ (hφ t ht)).2.2.1.mul hw).integrable_of_hasCompactSupport (hSh r ε d _ (hφ t ht)).2.2.2.mul_right
    have hconst : ∀ t, 1 ≤ t → ∫ g, φ t (toM g) * w g ∂μ = ∫ g, φ 1 (toM g) * w g ∂μ := fun t ht => by
      have h1 := (hw1 _ (Submodule.sub_mem _ (hφ 1 le_rfl) (hφ t ht))).2
      rw [(hTA r ε μ U π hu hi _ (hdiff t ht)).2] at h1
      simp only [Pi.sub_apply, sub_mul] at h1
      rw [integral_sub (hint 1 le_rfl) (hint t ht)] at h1
      exact (sub_eq_zero.1 h1.symm).symm
    have hT := (hl1 w hw).const_mul c⁻¹
    rw [inv_mul_cancel_left₀ hc, htop] at hT
    rw [← eq_of_const_of_tendsto hconst (hT.congr fun t => by
      rw [← integral_const_mul]; simp [φ, mul_assoc])]
    exact hw1 _ (hφ 1 le_rfl)
  refine ⟨fun g => φ 1 (toM g), (hSh r ε d _ (hφ 1 le_rfl)).1, (hSh r ε d _ (hφ 1 le_rfl)).2.1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B, a, hB, hBa, h⟩ := key X (ujRep hD.2.2.1)
      (isUnitaryRep_repVia _ _ GlobalTheory.HCChar.continuous_ujMat)
      (isTopIrreducible_repVia _ _ (fun x hx => by
        have hJ : IsUnit x := by
          have h : x.conjTranspose * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := hx
          have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
            rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
            congr 1; funext a; split_ifs <;> simp
          have h2 : (Formalism.REAL.Jm ε * x.conjTranspose * Formalism.REAL.Jm ε) * x = 1 := by
            rw [mul_assoc, mul_assoc, ← mul_assoc x.conjTranspose, h, hJ]
          exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse h2)
        exact ⟨⟨hJ.unit, hx⟩, rfl⟩) hD.2.2.2.1)
    rwa [hone B a hB hBa] at h
  · intro U _ _ _ π hu hi hne
    obtain ⟨B, a, hB, hBa, h⟩ := key U π hu hi
    rwa [hzero U π hu hi hne B a hB hBa] at h
  · intro s hs hnc dt _ _
    obtain ⟨R, hR, hx⟩ := hNE r ε s hs hnc
    have ht : (1 : ℝ) ≤ 1 + 2 / R := by have := div_pos two_pos hR; linarith
    have h0 : HasOrbInt μ s dt (fun g => φ (1 + 2 / R) (toM g)) 0 := by
      have e : conjFn s (fun g : UJ ε => φ (1 + 2 / R) (toM g)) = 0 := funext fun x => by
        have h1 : 1 < (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x)) := by
          have h2 : (1 + 2 / R) * R ≤ (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x)) :=
            mul_le_mul_of_nonneg_left (hx x) (by linarith)
          have h3 : (1 + 2 / R) * R = R + 2 := by field_simp
          linarith
        simp [conjFn, φ, (hfam _ (by linarith)).2 _ h1]
      rw [HasOrbInt, e]
      exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
    rw [hsum (1 + 2 / R)]
    simpa using h0.add (hOA r ε μ s hs dt _ (hdiff _ ht))
  · intro s hs hcp y θ hy dt _ _
    have hreg : IsRegSS (ujMat ε (torusPt ε θ)) := by
      rw [← hy, IsRegSS, map_mul, Matrix.charpoly_mul_comm, ← map_mul, mul_inv_cancel_left]
      exact hs
    have hinj : Function.Injective fun a => Complex.exp (θ a * Complex.I) := injective_of_regSS hreg
    have hO := fun t (ht : 1 ≤ t) => hOC r ε μ s hs hcp dt y _ (hSh r ε d _ (hφ t ht)).2.2.1 (hSh r ε d _ (hφ t ht)).2.2.2
    rw [hy] at hO
    have hconst : ∀ t, 1 ≤ t → (∫ x, φ t (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ) =
        (∫ x, φ 1 (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ) := fun t ht => by
      have h1 := (hO t ht).add (hOA r ε μ s hs dt _ (hdiff t ht))
      rw [← hsum t, add_zero] at h1
      exact h1.2.symm.trans (hO 1 le_rfl).2
    have hT := ((hl2 θ (torusPt ε θ) rfl hinj fun k => by
      rw [htop]; exact hcl ⟨_, torusPt_mem_KG ε θ⟩ k).const_mul c⁻¹).div_const (dt.real Set.univ : ℂ)
    rw [htop, htor θ hinj, mul_div_assoc c, inv_mul_cancel_left₀ hc, mul_div_cancel_right₀ _ (dMode_ne_zero ε hinj)] at hT
    rw [← eq_of_const_of_tendsto hconst (hT.congr fun t => by
      rw [← integral_const_mul]; simp [φ])]
    exact hO 1 le_rfl

theorem localPC_of_steps : StAlg → StProfile → StFam → StHomot → StLim → StShape → StOrbAd → StOrbCpt → StNonEll → StTr →
    StTrAd → StKData → GlobalTheory.PsCo.Pc.LocalPC :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => localPC4_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end GlobalTheory.PsCo.Pc1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtensionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
theorem _root_.GlobalTheory.T.eq_of_framedPoint_lies_over_torus_extension : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre F) (w w' : Frm D.toPre F 1 g.b) (x x' : TFK (R := R) F ⟶ A.A) (fr : FrAt x) (fr' : FrAt x'), w.IsGen → w'.IsGen → fr.IsGen → fr'.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g w' x' fr' → x = x' := by
  first | exact @GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver | exact GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver | (intros; apply GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver <;> assumption)
end

