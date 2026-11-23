module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryCentralizerEquivNormOneTorus
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.CentTorusModel

variable {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))

def mulMat (a : B.A) : Matrix (Fin n) (Fin n) K.E :=
  LinearMap.toMatrix' (ψ.toLinearMap ∘ₗ LinearMap.mulLeft K.E a ∘ₗ ψ.symm.toLinearMap)

theorem mulMat_mulVec (a y : B.A) : mulMat B ψ a *ᵥ ψ y = ψ (a * y) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

theorem eq_mulMat {M : Matrix (Fin n) (Fin n) K.E} {a : B.A} (h : ∀ y, M *ᵥ ψ y = ψ (a * y)) :
    M = mulMat B ψ a := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨y, rfl⟩ := ψ.surjective v
  simp only [Matrix.toLin'_apply, h, mulMat_mulVec]

theorem mulMat_one : mulMat B ψ 1 = 1 :=
  (eq_mulMat B ψ (fun y => by simp)).symm

theorem mulMat_mul (a b : B.A) : mulMat B ψ (a * b) = mulMat B ψ a * mulMat B ψ b :=
  (eq_mulMat B ψ (fun y => by rw [← Matrix.mulVec_mulVec, mulMat_mulVec, mulMat_mulVec, mul_assoc])).symm

def mulHom : B.A →* Matrix (Fin n) (Fin n) K.E where
  toFun := mulMat B ψ
  map_one' := mulMat_one B ψ
  map_mul' := mulMat_mul B ψ

theorem commutant (hs : B.P.Separable) (f : B.A →ₗ[K.E] B.A) (hf : ∀ y, f (B.g * y) = B.g * f y) (y : B.A) :
    f y = f 1 * y := by
  obtain ⟨b, hb⟩ := exists_basis_pow_of_separable K B hs
  have key : f = LinearMap.mulRight K.E (f 1) := by
    refine b.ext fun i => ?_
    rw [hb i, LinearMap.mulRight_apply]
    generalize (i : ℕ) = k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', hf, ih, mul_assoc]
  rw [key, LinearMap.mulRight_apply, LinearMap.mulRight_apply, one_mul, mul_comm]

theorem stdH_mulVec_eq (M : Matrix (Fin n) (Fin n) K.E) (u v : Fin n → K.E) :
    stdH K n (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ ((Mᵀ * M.map K.c) *ᵥ fun k => K.c (v k)) := by
  have h1 : (fun k => K.c ((M *ᵥ v) k)) = M.map K.c *ᵥ fun k => K.c (v k) := by
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  have h2 : stdH K n (M *ᵥ u) (M *ᵥ v) = (M *ᵥ u) ⬝ᵥ fun k => K.c ((M *ᵥ v) k) := rfl
  rw [h2, h1, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
    Matrix.mulVec_mulVec]

theorem stdH_mulVec_iff (M : Matrix (Fin n) (Fin n) K.E) :
    (∀ u v, stdH K n (M *ᵥ u) (M *ᵥ v) = stdH K n u v) ↔ (M.map K.c)ᵀ * M = 1 := by
  constructor
  · intro h
    ext i j
    have := h (Pi.single j 1) (Pi.single i 1)
    simp [InertUnitOrb.stdH, Pi.single_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  · intro h u v
    have h' : Mᵀ * M.map K.c = 1 := by
      have := congrArg (fun X => X.map K.c) h
      simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero K.c) (map_one K.c)] at this
      convert this using 2
      ext a b; simp [K.c_c]
    rw [stdH_mulVec_eq, h', Matrix.one_mulVec]
    rfl

theorem isom_iff {γ' : Matrix (Fin n) (Fin n) K.E} {x : B.Aˣ} (hm : IsModel B γ' x ψ) (a : B.A) :
    (∀ u v, stdH K n (mulMat B ψ a *ᵥ u) (mulMat B ψ a *ᵥ v) = stdH K n u v) ↔ a * B.σ a = 1 := by
  have hh := hm.2.2
  constructor
  · intro h
    have h2 : ∀ y z, B.herm x (a * y) (a * z) = B.herm x y z := by
      intro y z
      rw [← hh, ← hh, ← mulMat_mulVec, ← mulMat_mulVec]
      exact h _ _
    have h3 : ∀ z, B.herm x (a * B.σ a - 1) z = 0 := by
      intro z
      have := h2 1 z
      simp only [InvAlg.herm] at this ⊢
      rw [show (x : B.A) * (a * B.σ a - 1) * B.σ z = (x : B.A) * (a * 1) * B.σ (a * z) - x * 1 * B.σ z by
        rw [map_mul]; ring, map_sub, this, sub_self]
    have h4 : ψ (a * B.σ a - 1) = 0 := by
      funext k
      have := h3 (ψ.symm (Pi.single k 1))
      rw [← hh, ψ.apply_symm_apply] at this
      simpa [InertUnitOrb.stdH, Pi.single_apply] using this
    exact sub_eq_zero.mp ((LinearEquiv.map_eq_zero_iff ψ).mp h4)
  · intro h u v
    obtain ⟨y, rfl⟩ := ψ.surjective u
    obtain ⟨z, rfl⟩ := ψ.surjective v
    rw [mulMat_mulVec, mulMat_mulVec, hh, hh]
    simp only [InvAlg.herm, map_mul]
    congr 1
    calc (x : B.A) * (a * y) * (B.σ a * B.σ z) = x * y * B.σ z * (a * B.σ a) := by ring
      _ = _ := by rw [h, mul_one]

theorem map_map_symm {R S : Type} [Ring R] [Ring S] (e : R ≃+* S) (M : Matrix (Fin n) (Fin n) R) :
    (M.map e).map e.symm = M := by
  ext i j; simp

theorem map_symm_map {R S : Type} [Ring R] [Ring S] (e : R ≃+* S) (M : Matrix (Fin n) (Fin n) S) :
    (M.map e.symm).map e = M := by
  ext i j; simp

theorem unitary_map {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E}
    (e : K.E ≃+* w.adicCompletion E) (he : ∀ x, e (K.c x) = cj w (e x)) (M : Matrix (Fin n) (Fin n) K.E) :
    cT (cj w) (M.map e) * 1 * M.map e = 1 ↔ (M.map K.c)ᵀ * M = 1 := by
  have h1 : cT (cj w) (M.map e) = ((M.map K.c)ᵀ).map e := by
    ext i j; simp [cT, he]
  rw [h1, mul_one, ← Matrix.map_mul]
  constructor
  · intro h
    have : ((((M.map K.c)ᵀ * M).map e).map e.symm) = (1 : Matrix (Fin n) (Fin n) _).map e.symm := by rw [h]
    rw [map_map_symm] at this
    simpa using this
  · intro h
    rw [h]; simp

theorem cent_equiv_torus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ) (γ : UL n w), IsModel B ((((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) x ψ → B.P.Separable → ∃ τ : twCent (MonoidHom.id (UL n w)) γ ≃* B.T, ∀ (t : twCent (MonoidHom.id (UL n w)) γ) (y : B.A), ψ (((τ t : B.Aˣ) : B.A) * y) = (((((t : UL n w) : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) *ᵥ ψ y := by
  intro E _ _ _ _ w hw K e he _ n B ψ x γ hm hs
  have hUL : UL n w = UJ (cj w) 1 := by simp [UL, hw]
  let ρ : B.A →* Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
    (e.toRingHom.mapMatrix : Matrix (Fin n) (Fin n) K.E →+* _).toMonoidHom.comp (mulHom B ψ)
  have hρa : ∀ a, ρ a = (mulMat B ψ a).map e := fun a => rfl
  have hγ' := eq_mulMat B ψ (fun y => (hm.2.1 y).symm)
  have hγ : (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = ρ B.g := by
    rw [hρa, ← hγ', map_symm_map]
  have hmem : ∀ u : B.Aˣ, u ∈ B.T → (Units.map ρ u : GLw n w) ∈ UL n w := by
    intro u hu
    rw [hUL]
    show cT (cj w) (((Units.map ρ u : GLw n w)) : Matrix (Fin n) (Fin n) _) * 1 * _ = 1
    rw [Units.coe_map, hρa, unitary_map e he, ← stdH_mulVec_iff, isom_iff B ψ hm]
    exact hu
  have hcent : ∀ (u : B.Aˣ) (hu : u ∈ B.T),
      (⟨Units.map ρ u, hmem u hu⟩ : UL n w) ∈ twCent (MonoidHom.id (UL n w)) γ := by
    intro u hu
    show _ * γ = γ * _
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, MonoidHom.id_apply, Units.coe_map, hγ]
    rw [← map_mul, ← map_mul, mul_comm]
  let φ : B.T →* twCent (MonoidHom.id (UL n w)) γ :=
    { toFun := fun u => ⟨⟨Units.map ρ u, hmem u u.2⟩, hcent u u.2⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        simp }
  have hφ : ∀ u : B.T, ((((φ u : twCent (MonoidHom.id (UL n w)) γ) : UL n w) : GLw n w) :
      Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (mulMat B ψ ((u : B.Aˣ) : B.A)).map e := fun u => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := congrArg (fun t : twCent (MonoidHom.id (UL n w)) γ =>
      (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm) hab
    simp only [hφ, map_map_symm] at h1
    have h2 : ψ (((a : B.Aˣ) : B.A) * 1) = ψ (((b : B.Aˣ) : B.A) * 1) := by
      rw [← mulMat_mulVec, ← mulMat_mulVec, h1]
    apply Subtype.ext; apply Units.ext
    simpa using ψ.injective h2
  have hsurj : Function.Surjective φ := by
    intro t
    set T : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (((t : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hT
    set T' := T.map e.symm with hT'
    have hc : T * (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) =
        (((γ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) _) * T := by
      have := t.2
      change (t : UL n w) * γ = γ * (t : UL n w) at this
      have := congrArg (fun s : UL n w => ((s : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) this
      simpa using this
    have hc' : T' * mulMat B ψ B.g = mulMat B ψ B.g * T' := by
      rw [← hγ', hT', ← Matrix.map_mul, ← Matrix.map_mul, hc]
    let f : B.A →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' T' ∘ₗ ψ.toLinearMap
    have hfa : ∀ y, ψ (f y) = T' *ᵥ ψ y := by
      intro y; simp [f]
    have hf : ∀ y, f (B.g * y) = B.g * f y := by
      intro y
      apply ψ.injective
      rw [hfa, ← mulMat_mulVec, ← mulMat_mulVec, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc']
    have ha : ∀ y, T' *ᵥ ψ y = ψ (f 1 * y) := by
      intro y; rw [← hfa, commutant B hs f hf y]
    have hM := eq_mulMat B ψ ha
    have hTu : cT (cj w) T * 1 * T = 1 := by
      have hULmem : ∀ g : GLw n w, g ∈ UL n w → g ∈ UJ (cj w) 1 := fun g hg => by rwa [hUL] at hg
      exact hULmem _ (t : UL n w).2
    have hu : f 1 * B.σ (f 1) = 1 := by
      rw [← isom_iff B ψ hm, stdH_mulVec_iff, ← hM, ← unitary_map e he, hT', map_symm_map]
      exact hTu
    let u : B.Aˣ := ⟨f 1, B.σ (f 1), hu, by rw [mul_comm]; exact hu⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    change (mulMat B ψ (f 1)).map e = T
    rw [← hM, hT', map_symm_map]
  refine ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm, fun t y => ?_⟩
  have h1 : φ ((MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm t) = t :=
    (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).apply_symm_apply t
  conv_rhs => rw [← h1]
  rw [hφ, map_map_symm, mulMat_mulVec]

end GlobalTheory.CentTorusModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactPolynomialBlockTimesConjDetPower
section
section

noncomputable section

open MvPolynomial Matrix
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF.BlockEvaluationOffDiagonal

variable {n : ℕ}

lemma ev_inl (k : Mat n) (a b : Fin n) : ev k (X (Sum.inl (a, b))) = k a b := by
  simp [GlobalTheory.PsCo.Pc1.ev]

lemma ev_inr (k : Mat n) (a b : Fin n) : ev k (X (Sum.inr (a, b))) = star (k a b) := by
  simp [GlobalTheory.PsCo.Pc1.ev]

lemma offdiag {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) {a b : Fin n} (hab : ε a ≠ ε b) :
    k a b = 0 := by
  have h := congrFun (congrFun hk.2 a) b
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, Bool.false_eq_true, if_false, if_true] at h hab
  · exact absurd rfl hab
  · linear_combination (1 / 2 : ℂ) * h
  · linear_combination (-1 / 2 : ℂ) * h
  · exact absurd rfl hab

def bM (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) (blockAlg ε) := fun a b =>
  if h : ε a = ε b then ⟨X (Sum.inl (a, b)), Algebra.subset_adjoin ⟨a, b, h, rfl⟩⟩ else 0

def evB (ε : Fin n → Bool) (k : Mat n) : blockAlg ε →+* ℂ := (ev k).comp (blockAlg ε).val.toRingHom

lemma evB_apply (ε : Fin n → Bool) (k : Mat n) (x : blockAlg ε) : evB ε k x = ev k (x : Poly n) := rfl

lemma map_bM {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : (bM ε).map (evB ε k) = k := by
  ext a b
  simp only [Matrix.map_apply, bM]
  split_ifs with h
  · rw [evB_apply, ev_inl]
  · rw [map_zero, offdiag hk h]

lemma det_bM {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : evB ε k (bM ε).det = k.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_bM hk]

lemma adj_bM {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (a b : Fin n) :
    evB ε k ((bM ε).adjugate a b) = k.adjugate a b := by
  have := congrFun (congrFun (RingHom.map_adjugate (evB ε k) (bM ε)) a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, map_bM hk] at this
  exact this

lemma ev_detbP (k : Mat n) : ev k (detbP n) = conj k.det := by
  rw [GlobalTheory.PsCo.Pc1.detbP, RingHom.map_det, (starRingEnd ℂ).map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply, ev_inr]

lemma conj_det_mul {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : conj k.det * k.det = 1 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.mp hk.1)
  rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at h
  simpa using h

lemma star_entry {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (a b : Fin n) :
    star (k a b) = conj k.det * k.adjugate b a := by
  have hu : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
  have h1 : k.adjugate * k = k.det • (1 : Mat n) := Matrix.adjugate_mul k
  have h2 : kᴴ = conj k.det • k.adjugate := by
    calc kᴴ = (conj k.det * k.det) • kᴴ := by rw [conj_det_mul hk, one_smul]
      _ = conj k.det • ((k.det • (1 : Mat n)) * kᴴ) := by rw [smul_mul_assoc, one_mul, smul_smul]
      _ = conj k.det • k.adjugate := by
        rw [← h1, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu, Matrix.mul_one]
  have := congrFun (congrFun h2 b) a
  simpa [Matrix.conjTranspose_apply] using this

def dB (ε : Fin n → Bool) : Poly n := ((bM ε).det : Poly n)

lemma dB_mem (ε : Fin n → Bool) : dB ε ∈ blockAlg ε := (bM ε).det.2

lemma ev_dB {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : ev k (dB ε) = k.det := det_bM hk

def Good (ε : Fin n → Bool) (P : Poly n) : Prop :=
  ∃ (M : ℕ) (Q : Poly n), Q ∈ blockAlg ε ∧ ∀ k ∈ Formalism.REAL.Kset ε, ev k P = ev k (detbP n ^ M * Q)

lemma good (ε : Fin n → Bool) (P : Poly n) : Good ε P := by
  refine MvPolynomial.induction_on P ?_ ?_ ?_
  · intro a
    refine ⟨0, C a, ?_, fun k _ => by simp⟩
    simpa [MvPolynomial.algebraMap_eq] using (blockAlg ε).algebraMap_mem a
  · rintro p q ⟨M1, Q1, h1, e1⟩ ⟨M2, Q2, h2, e2⟩
    refine ⟨M1 + M2, Q1 * dB ε ^ M2 + Q2 * dB ε ^ M1, ?_, fun k hk => ?_⟩
    · exact add_mem (mul_mem h1 (pow_mem (dB_mem ε) _)) (mul_mem h2 (pow_mem (dB_mem ε) _))
    · have hc : ∀ m : ℕ, conj k.det ^ m * k.det ^ m = 1 := fun m => by
        rw [← mul_pow, conj_det_mul hk, one_pow]
      rw [map_add (f := _), e1 k hk, e2 k hk]
      simp only [map_mul, map_pow, map_add (f := _), ev_detbP, ev_dB hk]
      rw [pow_add]
      linear_combination (-(conj k.det ^ M1 * ev k Q1)) * hc M2 + (-(conj k.det ^ M2 * ev k Q2)) * hc M1
  · rintro p i ⟨M, Q, hQ, e⟩
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · refine ⟨M, Q * ((bM ε a b : blockAlg ε) : Poly n), mul_mem hQ (bM ε a b).2, fun k hk => ?_⟩
      have h : ev k ((bM ε a b : blockAlg ε) : Poly n) = k a b := by
        have := congrFun (congrFun (map_bM hk) a) b
        rw [Matrix.map_apply] at this
        exact this
      rw [map_mul, e k hk, ev_inl]
      simp only [map_mul, h]
      ring
    · refine ⟨M + 1, Q * (((bM ε).adjugate b a : blockAlg ε) : Poly n),
        mul_mem hQ ((bM ε).adjugate b a).2, fun k hk => ?_⟩
      have h : ev k (((bM ε).adjugate b a : blockAlg ε) : Poly n) = k.adjugate b a := adj_bM hk b a
      rw [map_mul, e k hk, ev_inr, star_entry hk]
      simp only [map_mul, map_pow, h, ev_detbP]
      ring

end GlobalTheory.PsCo.PcEF.BlockEvaluationOffDiagonal

namespace GlobalTheory.PsCo.PcEF

theorem maxCompactPolynomial_blockTimesConjDetPower : BlockForm := by
  intro n ε P
  exact BlockEvaluationOffDiagonal.good ε P

end GlobalTheory.PsCo.PcEF

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKGLIffVal
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwKU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_KGL_iff_val {u : Pl E} (x : GLw n u) :
    x ∈ GlobalTheory.LFun.KGL u (n := n) ↔ (∀ i j, Valued.v (x.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((x⁻¹).val i j) ≤ 1 := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective (Ov E u).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective (Ov E u).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem mem_Kglob_iff (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    g ∈ GlobalTheory.EulerTw.Kglob E n ↔ ∀ u : Pl E, GeneralLinearGroup.map (pLoc E u) g ∈ GlobalTheory.LFun.KGL u (n := n) := by
  unfold GlobalTheory.EulerTw.Kglob
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]

theorem pLoc_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (u : Pl E) :
    GeneralLinearGroup.map (pLoc E u) (GlobalTheory.EulerTw.prjG E n T g) =
      if u ∈ T then GeneralLinearGroup.map (pLoc E u) g else 1 := by
  have hid : pLoc E u (GlobalTheory.EulerTw.idem E T) = if u ∈ T then 1 else 0 := rfl
  split_ifs with hu
  · refine Units.ext (Matrix.ext fun i j => ?_)
    show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = pLoc E u (g.val i j)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, hid, if_pos hu]
    simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, hid, if_neg hu]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]

theorem val_pLoc_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (u : Pl E) (i j : Fin n) :
    Valued.v ((GeneralLinearGroup.map (pLoc E u) (thF E n g)).val i j) =
      Valued.v ((GeneralLinearGroup.map (pLoc E (conjSrc (IsCMField.complexConj E).toRingEquiv u)) g⁻¹).val j.rev i.rev) := by
  show Valued.v (pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j)) = _
  rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, Valuation.map_mul, pLoc_conjFin, (conjLoc_spec _ u).2.2]
  have : Valued.v (pLoc E u ((-1) ^ ((i : ℕ) + j))) = 1 := by
    rw [map_pow, map_neg, map_one, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow]
  rw [this, one_mul]
  rfl

theorem thF_mem_Kglob (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hg : g ∈ GlobalTheory.EulerTw.Kglob E n) :
    thF E n g ∈ GlobalTheory.EulerTw.Kglob E n := by
  rw [mem_Kglob_iff] at hg ⊢
  intro u
  have hs := (mem_KGL_iff_val _).1 (hg (conjSrc (IsCMField.complexConj E).toRingEquiv u))
  rw [mem_KGL_iff_val]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [val_pLoc_thF, map_inv]
    exact hs.2 _ _
  · rw [← map_inv, ← map_inv, val_pLoc_thF, inv_inv]
    exact hs.1 _ _

end GlobalTheory.EulerTwKU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOpenNhdOneOfIntegralEqOneOnFinsetStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_open_nhd_one_of_integral_eq_one_on_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Set (finU (E := E) (n := n))), IsOpen U →
    (1 : finU (E := E) (n := n)) ∈ U → ∃ T : Finset (Pl E), ∀ u : finU (E := E) (n := n), (∀ v ∈ T, cLoc v (u : UA E n) = 1) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E) → u ∈ U := by
  first | exact @GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset | exact GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset | (intros; apply GlobalTheory.FixLevOpen.mem_of_isOpen_of_eq_one_on_finset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormComplexEmbeddingEntryDefiniteUnitaryRational
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SuppFin

theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ (γ.1.val i j)‖ ≤ 1 := by
  have h : (γ.1.val.map (IsCMField.complexConj E).toRingEquiv.toRingHom)ᵀ * 1 * γ.1.val = 1 := γ.2
  have hjj := congrFun (congrFun h j) j
  simp only [Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.one_apply_eq] at hjj
  have h2 : ∑ k, ((‖τ (γ.1.val k j)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    change _ = τ ((IsCMField.complexConj E) (γ.1.val k j)) * _
    rw [IsCMField.complexEmbedding_complexConj, Complex.conj_mul']
    push_cast; rfl
  have h3 : ∑ k, ‖τ (γ.1.val k j)‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 : ‖τ (γ.1.val i j)‖ ^ 2 ≤ 1 := by
    rw [← h3]
    exact Finset.single_le_sum (f := fun k => ‖τ (γ.1.val k j)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
  nlinarith [norm_nonneg (τ (γ.1.val i j))]

end GlobalTheory.BCT.SuppFin
end

