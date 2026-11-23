module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoostDecompositionNormBoundOfEmbeddingLaws
section
noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.BoostHilbertSchmidtTrace

theorem house : ∀ (m : ℕ) (ε : Fin m → Bool) (z : Fin m) (u : Fin m → ℂ), ε z = true → (∀ i, ε i = false → u i = 0) → ∑ i, ‖u i‖ ^ 2 = 1 → ∃ k ∈ UJset ε, kᴴ * k = 1 ∧ ∀ i, k i z = u i := GlobalTheory.T.exists_unitary_positiveBlock_column_eq

theorem boostMat : ∀ (m : ℕ) (ε : Fin m → Bool) (a b : Fin m → ℂ), (∀ i, ε i = false → a i = 0) → (∀ i, ε i = true → b i = 0) → ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 → ∃ A ∈ UJset ε, (∀ i, ∑ j, A i j * a j = (Real.sqrt (∑ j, ‖a j‖ ^ 2) : ℂ) * (a i + b i)) ∧ hsn A ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖a i + b i‖ ^ 2 := _root_.GlobalTheory.Boost.boost_exists

end GlobalTheory.SepReal.BoostHilbertSchmidtTrace

namespace GlobalTheory.SepReal.BoostHilbertSchmidtTrace

theorem hsn_sq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : hsn M ^ 2 = ∑ a, ∑ b, ‖M a b‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem hsn_sq_eq_trace {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : ((hsn M ^ 2 : ℝ) : ℂ) = (M * Mᴴ).trace := by
  rw [hsn_sq, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.mul_conj']
  rfl

theorem hsn_mul_unitary {m : ℕ} (M U : Matrix (Fin m) (Fin m) ℂ) (hU : Uᴴ * U = 1) : hsn (M * U) = hsn M := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have h : ((hsn (M * U) ^ 2 : ℝ) : ℂ) = ((hsn M ^ 2 : ℝ) : ℂ) := by
    rw [hsn_sq_eq_trace, hsn_sq_eq_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU', Matrix.one_mul]
  have h2 : hsn (M * U) ^ 2 = hsn M ^ 2 := by exact_mod_cast h
  have h0 : 0 ≤ hsn (M * U) := Real.sqrt_nonneg _
  have h1 : 0 ≤ hsn M := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (hsn (M * U) - hsn M), sq_nonneg (hsn (M * U) + hsn M)]

theorem inv_eq {m : ℕ} {ε : Fin m → Bool} {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ = Jm ε * gᴴ * Jm ε ∧ g * (Jm ε * gᴴ * Jm ε) = 1 := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hl : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Jm_mul_self]
  exact ⟨Matrix.inv_eq_left_inv hl, mul_eq_one_comm.mp hl⟩

theorem inv_mem {m : ℕ} {ε : Fin m → Bool} {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UJset ε) : g⁻¹ ∈ UJset ε := by
  obtain ⟨hi, hr⟩ := inv_eq hg
  have hJ : g * Jm ε * gᴴ = Jm ε := by
    have := congrArg (· * Jm ε) hr
    simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Matrix.one_mul] at this
    simpa [Matrix.mul_assoc] using this
  show (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε
  rw [hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
  calc Jm ε * (g * Jm ε) * Jm ε * (Jm ε * gᴴ * Jm ε) = Jm ε * (g * (Jm ε * Jm ε) * (Jm ε * gᴴ)) * Jm ε := by
        simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [Jm_mul_self, Matrix.mul_one, ← Matrix.mul_assoc g, hJ, Jm_mul_self, Matrix.one_mul]

theorem mul_mem {m : ℕ} {ε : Fin m → Bool} {g h : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) :
    g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

end GlobalTheory.SepReal.BoostHilbertSchmidtTrace

namespace GlobalTheory.SepReal.BoostHilbertSchmidtTrace

theorem transit {m : ℕ} (ε : Fin m → Bool) (z : Fin m) (hz : ε z = true) (y : Fin m → ℂ)
    (hy : ∑ i, (if ε i then (1 : ℝ) else -1) * ‖y i‖ ^ 2 = 1) :
    ∃ c ∈ UJset ε, (∀ i, c i z = y i) ∧ hsn c ^ 2 ≤ (m : ℝ) + 2 * ∑ i, ‖y i‖ ^ 2 := by
  set a : Fin m → ℂ := fun i => if ε i then y i else 0 with ha
  set b : Fin m → ℂ := fun i => if ε i then 0 else y i with hb
  have hab : ∀ i, a i + b i = y i := fun i => by by_cases h : ε i <;> simp [ha, hb, h]
  have hn : ∑ i, ‖a i‖ ^ 2 = 1 + ∑ i, ‖b i‖ ^ 2 := by
    rw [← hy, ← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : ε i <;> simp [ha, hb, h]
  have ha0 : ∀ i, ε i = false → a i = 0 := fun i h => by simp [ha, h]
  have hb0 : ∀ i, ε i = true → b i = 0 := fun i h => by simp [hb, h]
  set ch : ℝ := Real.sqrt (∑ j, ‖a j‖ ^ 2) with hch
  have hch1 : 1 ≤ ch := by
    rw [hch, Real.one_le_sqrt]
    rw [hn]; have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖b i‖); linarith
  have hch0 : (ch : ℂ) ≠ 0 := by exact_mod_cast (show ch ≠ 0 by linarith)
  set u : Fin m → ℂ := fun i => (ch : ℂ)⁻¹ * a i with hu
  have hu1 : ∑ i, ‖u i‖ ^ 2 = 1 := by
    have hs : ch ^ 2 = ∑ j, ‖a j‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    simp only [hu, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ch), mul_pow,
      ← Finset.mul_sum, ← hs, inv_pow]
    field_simp
  have hu0 : ∀ i, ε i = false → u i = 0 := fun i h => by simp [hu, ha0 i h]
  obtain ⟨k, hk, hkU, hkz⟩ := house m ε z u hz hu0 hu1
  obtain ⟨A, hA, hAa, hAn⟩ := boostMat m ε a b ha0 hb0 hn
  refine ⟨A * k, mul_mem hA hk, fun i => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    simp only [hkz, hu]
    have := hAa i
    rw [← hab i]
    calc ∑ j, A i j * ((ch : ℂ)⁻¹ * a j) = (ch : ℂ)⁻¹ * ∑ j, A i j * a j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ = a i + b i := by rw [this, ← hch]; field_simp
  · rw [hsn_mul_unitary A k hkU]
    simpa only [hab] using hAn

theorem col_inv_norm {n : ℕ} (e : Option (Fin n) ≃ Fin (n + 1)) (ε : Fin (n + 1) → Bool) (hz : ε (e none) = true)
    (g : Mat (n + 1)) (hg : g ∈ UJset ε) :
    ∑ i, (if ε i then (1 : ℝ) else -1) * ‖g⁻¹ i (e none)‖ ^ 2 = 1 := by
  have h : (g⁻¹)ᴴ * Jm ε * g⁻¹ = Jm ε := inv_mem hg
  have h2 := congrFun (congrFun h (e none)) (e none)
  simp only [Matrix.mul_apply, Jm, Matrix.diagonal_apply, Matrix.conjTranspose_apply, hz, if_true] at h2
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  have h3 : ((∑ i, (if ε i then (1 : ℝ) else -1) * ‖g⁻¹ i (e none)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [← h2]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.mul_conj']
    by_cases hi : ε i <;> simp [hi] <;> ring
  exact_mod_cast h3

end GlobalTheory.SepReal.BoostHilbertSchmidtTrace

namespace GlobalTheory.SepReal


open BoostHilbertSchmidtTrace in
theorem boost_of_embLaws : EmbLaws → Boost := by
  intro hE n e ε ε' hS g hg
  obtain ⟨-, -, -, -, -, hstab, -, -, -, -, -, hinvn, -⟩ := hE n e ε ε' hS
  obtain ⟨c, hc, hcz, hcn⟩ := transit ε (e none) hS.1 (fun i => g⁻¹ i (e none)) (col_inv_norm e ε hS.1 g hg)
  have hgi : g * g⁻¹ = 1 := by rw [(inv_eq hg).1]; exact (inv_eq hg).2
  have hgc : g * c ∈ UJset ε := mul_mem hg hc
  have hcol : ∀ i, (g * c) i (e none) = if i = e none then 1 else 0 := fun i => by
    rw [Matrix.mul_apply]
    simp only [hcz]
    rw [← Matrix.mul_apply, hgi, Matrix.one_apply]
  obtain ⟨h, hh, hgh⟩ := hstab (g * c) hgc hcol
  have hci : c * c⁻¹ = 1 := by rw [(inv_eq hc).1]; exact (inv_eq hc).2
  refine ⟨h, hh, c⁻¹, inv_mem hc, ?_, ?_⟩
  · rw [← hgh, Matrix.mul_assoc, hci, Matrix.mul_one]
  · rw [(hinvn c hc).2, colLen, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simpa using hcn
end GlobalTheory.SepReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffCoefficientSpaceActionMemRange
section
open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRho

theorem coeff_rhoVr_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff ((rhoVr emb lam g) v).1 m ∈ Set.range κ := by
  classical
  intro ι _ n E _ emb L _ κ hA0 lam γE v hv0 m
  set A : Subfield ℂ := κ.fieldRange with hAdef
  have hA : ∀ τ x, emb τ x ∈ A := fun τ x => RingHom.mem_fieldRange.2 (hA0 τ x)
  have hv : ∀ m, AddMonoidAlgebra.coeff (v : Formalism.L2.DIV.Pol ℂ ι n) m ∈ A := fun m => RingHom.mem_fieldRange.2 (hv0 m)
  rw [← RingHom.coe_fieldRange]
  show AddMonoidAlgebra.coeff ((rhoVr emb lam γE v : VV ℂ lam) : Formalism.L2.DIV.Pol ℂ ι n) m ∈ A
  let R₀ : Subring (Formalism.L2.DIV.Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Formalism.L2.DIV.Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, AddMonoidAlgebra.coeff F m ∈ A := by
    intro F
    constructor
    · rintro ⟨F', rfl⟩ m
      rw [coeff_map]
      exact (AddMonoidAlgebra.coeff F' m).2
    · intro h
      obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := A.subtype)).2 (fun c hc => by
        obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
        exact ⟨⟨_, h m⟩, rfl⟩)
      exact ⟨F', hF'⟩
  have hblock : ∀ M : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ a b, M τ a b ∈ A) → ∀ F ∈ R₀,
      Formalism.GradedWeylDivisibility.blockAct ℂ M F ∈ R₀ := by
    intro M hM F hF
    obtain ⟨F', rfl⟩ := hF
    induction F' using MvPolynomial.induction_on with
    | C a =>
      rw [map_C, Formalism.GradedWeylDivisibility.blockAct, aeval_C]
      exact ⟨C a, by rw [map_C]; rfl⟩
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hp hq
    | mul_X p w hp =>
      rw [map_mul, map_mul, map_X]
      refine mul_mem hp ?_
      rw [Formalism.GradedWeylDivisibility.blockAct, aeval_X]
      exact sum_mem fun b _ => mul_mem ⟨C ⟨_, hM _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩
  have hent : ∀ τ a b, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b ∈ A := by
    intro τ a b
    show ((((Formalism.UG.bc (emb τ) γE)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
    rw [← map_inv]
    exact hA τ _
  have hdet : ∀ τ, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ∈ A := by
    intro τ
    have e := RingHom.map_det A.subtype (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A))
    rw [show A.subtype.mapMatrix (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A)) =
      ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) from Matrix.ext fun a b => rfl] at e
    rw [← e]
    exact SetLike.coe_mem _
  have hdt : detTwK lam (invTrK (embGL emb γE)) ∈ A := by
    unfold detTwK
    refine prod_mem fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact zpow_mem (hdet τ) _
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show AddMonoidAlgebra.coeff (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n)) m ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end GlobalTheory.RowRho
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompressedWordsGlWordJetRelationsOfNoTypes
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.ModRel

theorem ew_append {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (l₁ l₂ : List (Fin n × Fin n)) : ew E (l₁ ++ l₂) = ew E l₁ * ew E l₂ := by
  induction l₁ with
  | nil => simp [ew]
  | cons p w ih => simp only [List.cons_append, ew, ih, mul_assoc]

theorem thetaA_one_onePositionArrayOfIsometry {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (G : Fin n × Fin n → W) : thetaA E 1 (arr1 j G) = ∑ p : Fin n × Fin n, E p.1 p.2 (j (G p)) := by
  rw [theta_map_word_sum_apply]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun α => ?_
  simp [ew, arr1, arrTo]

theorem theta_vminus {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V} (hg : GlRel E)
    (h0 : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) :
    Vminus ε E Λ u ≤ LinearMap.ker (thetaA E 1) := by
  obtain ⟨-, hθ⟩ := (arrModule V n ε E 1).1 hg
  apply isotypic_part_le_of_forall
  intro y hy μ hμ hyh
  apply compact_span_le_of_stable
  · intro c d _ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hθ, hx, map_zero]
  · rw [LinearMap.mem_ker]
    obtain ⟨a, b, hba, hne, rfl⟩ := hμ
    have hμeq : Λ + root a b = Λ - root b a := by
      rw [root_swap' a b, sub_eq_add_neg]
    refine h0 b a hba (Ne.symm hne) _ ⟨fun c => ?_, fun c d hcd hcomp => ?_⟩
    · rw [← hθ, hyh.1 c, map_smul, hμeq]
    · rw [← hθ, hyh.2 c d hcd hcomp, map_zero]

theorem modJet_jetRel (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ)
    (u : V) (j : W →ₗᵢ[ℂ] V) (hL : LowData ε E Λ u j)
    (h0 : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) :
    JetRel ε E Λ u j (modJet E j) := by
  obtain ⟨hg, hu, -, -, -⟩ := hL
  refine ⟨fun l₁ l₂ a b c d => ?_, fun l a b _ y x x' hx => ?_, fun l a b hab y y' x hy => ?_,
    fun l G hG y => ?_⟩
  · have key : ew E (l₁ ++ (a, b) :: (c, d) :: l₂) - ew E (l₁ ++ (c, d) :: (a, b) :: l₂) =
        (if b = c then ew E (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then ew E (l₁ ++ (c, b) :: l₂) else 0) := by
      have h := hg a b c d
      simp only [ew_append, ew]
      rw [← mul_sub, ← mul_assoc (E a b), ← mul_assoc (E c d), ← sub_mul, h]
      split_ifs <;> simp [mul_sub, sub_mul]
    ext y x
    have h2 := congrArg (fun T : Module.End ℂ V => ⟪j y, T (j x)⟫_ℂ) key
    split_ifs at h2 ⊢ <;>
      simpa [modJet_apply, inner_sub_right] using h2
  · simp only [modJet_apply, ew_append, ew, hx, mul_one, Module.End.mul_apply]
  · simp only [modJet_apply, ew, hy, Module.End.mul_apply]
    rw [isUnitary_kUnit ε E hu b a hab.symm]
  · have h := theta_vminus hg h0 hG
    rw [LinearMap.mem_ker, thetaA_one_onePositionArrayOfIsometry] at h
    simp only [modJet_apply, ew_append, ew, mul_one, Module.End.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← inner_sum, ← map_sum, h, map_zero, inner_zero_right]

end GlobalTheory.SphJet.ModRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FderivLeadingMinorPowerProductStrictUpperEqZero
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace GlobalTheory.PhiUpperDeriv

theorem differentiableAt_prod {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset ι)
    {f : ι → E → ℂ} {z : E} (h : ∀ i, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun y => ∏ i ∈ s, f i y) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableAt_const _
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem differentiableAt_leadMinor {n : ℕ} (l : ℕ) (hl : l ≤ n) (z : Matrix (Fin n) (Fin n) ℂ) :
    DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => leadMinor y l hl) z := by
  have hent : ∀ a b : Fin n, DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => y a b) z := by
    intro a b
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun y => y a b
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).differentiableAt
  have hexp : (fun y : Matrix (Fin n) (Fin n) ℂ => leadMinor y l hl) = fun y =>
      ∑ σ : Equiv.Perm (Fin l), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i) := by
    funext y
    simp only [leadMinor, Matrix.det_apply', Matrix.submatrix_apply]
  rw [hexp]
  have key : ∀ σ : Equiv.Perm (Fin l), DifferentiableAt ℂ (fun y : Matrix (Fin n) (Fin n) ℂ =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i : Fin l, y (Fin.castLE hl (σ i)) (Fin.castLE hl i)) z :=
    fun σ => (differentiableAt_prod Finset.univ fun i => hent _ _).const_mul _
  have hsum := DifferentiableAt.sum (u := Finset.univ) fun σ _ => key σ
  rw [Finset.sum_fn] at hsum
  exact hsum

theorem differentiableAt_Phi {n : ℕ} (lam : Fin n → ℝ) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ Omega n) :
    DifferentiableAt ℂ (Phi lam) y := by
  have hPhi : Phi lam = fun z => ∏ i : Fin n, leadMinor z (i.val + 1) i.isLt ^ (-(sInt lam i)) :=
    funext fun _ => rfl
  rw [hPhi]
  refine differentiableAt_prod Finset.univ fun i => ?_
  exact (differentiableAt_leadMinor (i.val + 1) i.isLt y).zpow (Or.inl (hy i))

theorem Phi_mul_unipotent {n : ℕ} (lam : Fin n → ℝ) {y N : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ Omega n)
    (hN : ∀ i i' : Fin n, i' ≤ i → N i i' = 0) (t : ℂ) : Phi lam (y + t • (y * N)) = Phi lam y := by
  have hline : y + t • (y * N) = 1 * y * (1 + t • N) := by
    rw [Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hlo : IsLo (1 : Matrix (Fin n) (Fin n) ℂ) := fun i j hij =>
    Matrix.one_apply_ne (ne_of_lt hij)
  have hup : IsUp (1 + t • N) := fun i j hji => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN i j hji.le, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  have hdiag : ∀ l, (1 : Matrix (Fin n) (Fin n) ℂ) l l ≠ 0 ∧ (1 + t • N) l l ≠ 0 := fun l => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]
    simp
  obtain ⟨-, hval⟩ := GlobalTheory.PhiTriangular.phiTri n lam 1 y (1 + t • N) hlo hup hdiag hy
  rw [hline, hval]
  have hone : ∀ l, ((1 : Matrix (Fin n) (Fin n) ℂ) l l * (1 + t • N) l l) = 1 := fun l => by
    rw [Matrix.add_apply, Matrix.smul_apply, hN l l le_rfl, Matrix.one_apply_eq]
    simp
  simp only [hone, _root_.one_zpow, Finset.prod_const_one, one_mul]

theorem fderiv_Phi_upper : ∀ (n : ℕ) (lam : Fin n → ℝ) (y N : Matrix (Fin n) (Fin n) ℂ), y ∈ Omega n →
    (∀ i i' : Fin n, i' ≤ i → N i i' = 0) → fderiv ℂ (Phi lam) y (y * N) = 0 := by
  intro n lam y N hy hN
  have hD : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) y) y := (differentiableAt_Phi lam hy).hasFDerivAt
  have hL : HasDerivAt (fun t : ℂ => y + t • (y * N)) (y * N) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℂ)).smul_const (y * N)).const_add y
    simpa only [one_smul, id] using h1
  have hcomp : HasDerivAt (fun t : ℂ => Phi lam (y + t • (y * N))) (fderiv ℂ (Phi lam) y (y * N)) 0 :=
    hD.comp_hasDerivAt_of_eq (0 : ℂ) hL (by simp)
  have hconst : (fun t : ℂ => Phi lam (y + t • (y * N))) = fun _ => Phi lam y :=
    funext fun t => Phi_mul_unipotent lam hy hN t
  rw [hconst] at hcomp
  exact hcomp.unique (hasDerivAt_const 0 (Phi lam y))

end GlobalTheory.PhiUpperDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLeOfNeighbourhoodVolumeStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_le_of_neighbourhoodVolume : LogNear → LieBound → VolBall → DegUpper := by
  first | exact @GlobalTheory.SepReal.degUpper_of | exact GlobalTheory.SepReal.degUpper_of | (intros; apply GlobalTheory.SepReal.degUpper_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HformSpanEqZero
section
noncomputable section

namespace GlobalTheory.HermitianFormLinearity

open NumberField

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem hform_add_left (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (x + x') y =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_add_right (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (y + y') =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (c • x) y =
      starRingEnd E c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (c • y) =
      c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_zero_left (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem hform_zero_right (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x 0 = 0 := by
  simp [Formalism.UG.hform]

theorem hform_span_eq_zero (J : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (hS : ∀ y ∈ S, ∀ z ∈ S, Formalism.UG.hform (starRingEnd E) J y z = 0) :
    ∀ x ∈ Submodule.span E S, ∀ y ∈ Submodule.span E S,
      Formalism.UG.hform (starRingEnd E) J x y = 0 := by
  have h1 : ∀ x ∈ S, ∀ y ∈ Submodule.span E S, Formalism.UG.hform (starRingEnd E) J x y = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hS x hx z hz
    | zero => exact hform_zero_right J x
    | add a b _ _ ha hb => rw [hform_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [hform_smul_right, ha, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem z hz => exact h1 z hz y hy
  | zero => exact hform_zero_left J y
  | add a b _ _ ha hb => rw [hform_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [hform_smul_left, ha, mul_zero]

theorem main : ∀ (I : Formalism.MainNotions.S.AutInst)
    (R : Submodule (NumberField.RingOfIntegers (Formalism.MainNotions.S.AutInst.E I))
      (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I)),
    R ≠ ⊥ →
    (∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd (Formalism.MainNotions.S.AutInst.E I)) (Formalism.MainNotions.S.AutInst.J I) y z
      = (0 : Formalism.MainNotions.S.AutInst.E I)) →
    Formalism.MainNotions.S.AutInst.IsIsot I (Submodule.span (Formalism.MainNotions.S.AutInst.E I)
      (↑R : Set (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I))) := by
  intro I R hR hiso
  refine ⟨?_, hform_span_eq_zero I.J _ hiso⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  intro h
  apply hr0
  have : r ∈ Submodule.span I.E (↑R : Set (Fin I.n → I.E)) := Submodule.subset_span hr
  rw [h] at this
  exact (Submodule.mem_bot _).1 this

end GlobalTheory.HermitianFormLinearity
end
end

