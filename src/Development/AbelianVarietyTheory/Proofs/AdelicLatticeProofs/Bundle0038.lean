module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsConjHarmOfSpan
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsCompletelyReducibleKroneckerOfSpanEqTop
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_finset_span_image_eq {G V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : G → V) : ∃ T : Finset G, ∀ S : Set G, (T : Set G) ⊆ S →
      Submodule.span ℂ (f '' S) = Submodule.span ℂ (Set.range f) := by
  classical
  have h : (Submodule.span ℂ (Set.range f)).FG := Submodule.FG.of_finite
  obtain ⟨s, hs, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 h
  have hs' : (s : Set V) ⊆ f '' Set.univ := by simpa using hs
  obtain ⟨T, -, hT⟩ := Finset.subset_set_image_iff.1 hs'
  refine ⟨T, fun S hS => le_antisymm (Submodule.span_mono (Set.image_subset_range _ _)) ?_⟩
  rw [hsp, ← hT, Finset.coe_image]
  exact Submodule.span_mono (Set.image_mono hS)

theorem ss_kronecker_of_span_top : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Type) [Group G] (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix κ κ ℂ), Submodule.span ℂ (Set.range ρ) = ⊤ → Submodule.span ℂ (Set.range ρ') = ⊤ → SS (Set.range fun g => ρ g ⊗ₖ ρ' g) := by
  intro ι _ _ κ _ _ G _ ρ ρ' h h'
  classical
  obtain ⟨T₁, h₁⟩ := exists_finset_span_image_eq (ρ : G → Matrix ι ι ℂ)
  obtain ⟨T₂, h₂⟩ := exists_finset_span_image_eq (ρ' : G → Matrix κ κ ℂ)
  obtain ⟨T₃, h₃⟩ := exists_finset_span_image_eq (fun g => ρ g ⊗ₖ ρ' g)
  set T : Finset G := T₁ ∪ T₂ ∪ T₃ with hT
  set S : Finset G := T ∪ T.image (fun g => g⁻¹) with hS
  have hinv : ∀ g ∈ S, g⁻¹ ∈ S := by
    intro g hg
    rw [hS, Finset.mem_union] at hg ⊢
    rcases hg with hg | hg
    · exact Or.inr (Finset.mem_image_of_mem _ hg)
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
      exact Or.inl (by simpa using ha)
  let τ : S ≃ S :=
    { toFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩
      invFun := fun s => ⟨s.1⁻¹, hinv _ s.2⟩
      left_inv := fun s => Subtype.ext (inv_inv _)
      right_inv := fun s => Subtype.ext (inv_inv _) }
  have hτ : ∀ s : S, (τ s : G) = (s : G)⁻¹ := fun _ => rfl
  have e₁ := h₁ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  have e₂ := h₂ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  have e₃ := h₃ (S : Set G) (by intro x hx; simp [hS, hT, Finset.mem_coe.1 hx])
  rw [Set.image_eq_range] at e₁ e₂ e₃
  have i₁ : ∀ s : S, ρ (τ s : G) * ρ (s : G) = 1 := fun s => by
    rw [hτ, ← map_mul, inv_mul_cancel, map_one]
  have i₂ : ∀ s : S, ρ' (τ s : G) * ρ' (s : G) = 1 := fun s => by
    rw [hτ, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨P, hP, HP⟩ := _root_.GlobalTheory.ClassFin.exists_conj_harm_of_span ι S τ (fun s => ρ (s : G)) i₁ (e₁.trans h)
  obtain ⟨Q, hQ, HQ⟩ := _root_.GlobalTheory.ClassFin.exists_conj_harm_of_span κ S τ (fun s => ρ' (s : G)) i₂ (e₂.trans h')
  have HK := harm_kronecker ι κ S _ _ HP HQ
  have hPQ : IsUnit (P ⊗ₖ Q).det := by
    rw [det_kronecker]
    exact (hP.pow _).mul (hQ.pow _)
  have key : ∀ s : S, (P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹) =
      (P ⊗ₖ Q) * (ρ (s : G) ⊗ₖ ρ' (s : G)) * (P ⊗ₖ Q)⁻¹ := fun s => by
    rw [inv_kronecker, mul_kronecker_mul, mul_kronecker_mul]
  have conj : ∀ {n : Type} [Fintype n] [DecidableEq n] (A X Y : Matrix n n ℂ), IsUnit A.det → X * Y = 1 →
      (A * X * A⁻¹) * (A * Y * A⁻¹) = 1 := by
    intro n _ _ A X Y hA hXY
    calc (A * X * A⁻¹) * (A * Y * A⁻¹) = A * (X * (A⁻¹ * A) * Y) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hA, Matrix.mul_one, hXY, Matrix.mul_one, mul_nonsing_inv _ hA]
  have hss := ss_of_harm (ι × κ) S τ _ (fun s => by
    show ((P * ρ (τ s : G) * P⁻¹) ⊗ₖ (Q * ρ' (τ s : G) * Q⁻¹)) *
      ((P * ρ (s : G) * P⁻¹) ⊗ₖ (Q * ρ' (s : G) * Q⁻¹)) = 1
    rw [← mul_kronecker_mul, conj _ _ _ hP (i₁ s), conj _ _ _ hQ (i₂ s), one_kronecker_one]) HK
  have hss' : SS (Set.range fun s : S => ρ (s : G) ⊗ₖ ρ' (s : G)) := by
    refine (ss_transfer (ι × κ) _ ∅).2 (P ⊗ₖ Q) hPQ ?_
    rw [← Set.range_comp]
    convert hss using 2
    funext s
    exact (key s).symm
  refine (ss_transfer (ι × κ) _ _).1 ?_ ?_ hss'
  · rintro _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · intro x hx
    have : x ∈ Submodule.span ℂ (Set.range fun g => ρ g ⊗ₖ ρ' g) := Submodule.subset_span hx
    rw [← e₃] at this
    exact this

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRatPolysVanishingOfAutStable
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem evC_map_ringEquiv {ι : Type} (σ : ℂ ≃+* ℂ) (f : MvPolynomial (ι × ι) ℂ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (σ : ℂ →+* ℂ) f) g = σ (evC f (g.map σ.symm)) := by
  unfold evC
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp => simp only [map_mul, hp]; simp

theorem evC_map_rat {ι : Type} (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  unfold evC ev
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

theorem mem_span_vanI_of_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ) := by
  intro ι _ _ Γ hΓ f hf
  let W : Submodule ℂ (MvPolynomial (ι × ι) ℂ) :=
    { carrier := {f | ∀ g ∈ Γ, evC f g = 0}
      add_mem' := by
        intro a b ha hb g hg
        have h1 := ha g hg
        have h2 := hb g hg
        unfold evC at *
        rw [map_add (f := _), h1, h2, add_zero]
      zero_mem' := by
        intro g hg
        simp [evC]
      smul_mem' := by
        intro c a ha g hg
        have h1 := ha g hg
        unfold evC at *
        rw [MvPolynomial.smul_eval, h1, mul_zero] }
  have hrepr : ∀ (p : MvPolynomial (ι × ι) ℂ) k,
      (MvPolynomial.basisMonomials (ι × ι) ℂ).repr p k = AddMonoidAlgebra.coeff p k := fun p k => rfl
  have key := _root_.GlobalTheory.ClassFin.GaloisDescent.le_span_rational _ _ (MvPolynomial.basisMonomials (ι × ι) ℂ) W (by
    intro σ w hw
    refine ⟨MvPolynomial.map (σ : ℂ →+* ℂ) w, ?_, ?_⟩
    · intro g hg
      rw [evC_map_ringEquiv, hw _ (hΓ σ.symm g hg), map_zero]
    · intro k
      rw [hrepr, hrepr, MvPolynomial.coeff_map]
      rfl)
  refine Submodule.span_mono ?_ (key (show f ∈ W from hf))
  rintro w ⟨hw, hq⟩
  have hl : w ∈ Set.range (MvPolynomial.map (σ := ι × ι) (algebraMap ℚ ℂ)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro c hc
    simp only [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hc
    obtain ⟨k, -, rfl⟩ := hc
    obtain ⟨q, hq⟩ := hq k
    exact ⟨q, by rw [← hrepr, hq]; rfl⟩
  obtain ⟨w₀, rfl⟩ := hl
  refine ⟨w₀, ?_, rfl⟩
  intro g hg
  rw [← evC_map_rat]
  exact hw g hg

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemSpanRationalKroneckerInvariants
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RationalInvariants

def invSub {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (n : ℕ) :
    Submodule ℂ ((Fin n → ι) → ℂ) where
  carrier := {μ | ∀ g ∈ Γ, μ ᵥ* tpow n g = μ}
  add_mem' := by
    intro a b ha hb g hg
    rw [Matrix.add_vecMul, ha g hg, hb g hg]
  zero_mem' := by
    intro g _
    exact Matrix.zero_vecMul _
  smul_mem' := by
    intro c a ha g hg
    rw [Matrix.smul_vecMul, ha g hg]

theorem mem_span_rational :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ (n : ℕ) (l : (Fin n → ι) → ℂ), (∀ g ∈ Γ, l ᵥ* tpow n g = l) → l ∈ Submodule.span ℂ {μ : (Fin n → ι) → ℂ | (∀ g ∈ Γ, μ ᵥ* tpow n g = μ) ∧ ∀ a, ∃ q : ℚ, μ a = q} := by
  intro ι _ _ Γ hΓ n l hl
  have h := _root_.GlobalTheory.ClassFin.GaloisDescent.le_span_rational _ _ (Pi.basisFun ℂ (Fin n → ι)) (invSub Γ n) (by
    intro σ w hw
    refine ⟨fun a => σ (w a), ?_, fun k => by simp⟩
    intro g hg
    funext b
    have h1 := congrArg σ (congrFun (hw _ (hΓ σ.symm g hg)) b)
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.vecMul, dotProduct, tpow, map_sum, map_prod])
  have h2 := h (show l ∈ invSub Γ n from hl)
  simp only [Pi.basisFun_repr] at h2
  exact h2

end GlobalTheory.ClassFin.RationalInvariants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MinNormTensorStabilizerConjTransposeInvariant
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma posDef_det_one_exists_unitary_exp_diagonal_sum_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℂ) (hP : P.PosDef) (hdet : P.det = 1) :
    ∃ (U : Matrix ι ι ℂ) (δ : ι → ℝ), U * Uᴴ = 1 ∧ ∑ i, δ i = 0 ∧
      P = (U * diagonal fun i => ((Real.exp (2 * δ i) : ℝ) : ℂ)) * Uᴴ := by
  refine ⟨(hP.1.eigenvectorUnitary : Matrix ι ι ℂ), fun i => Real.log (hP.1.eigenvalues i) / 2,
    ?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.mul_star_self_of_mem hP.1.eigenvectorUnitary.2
  · have h := hP.1.det_eq_prod_eigenvalues
    rw [hdet] at h
    have hprod' : ((∏ i, hP.1.eigenvalues i : ℝ) : ℂ) = 1 := by push_cast; exact h.symm
    have hprod : ∏ i, hP.1.eigenvalues i = 1 := by exact_mod_cast hprod'
    rw [← Finset.sum_div, ← Real.log_prod (fun i _ => (hP.eigenvalues_pos i).ne'), hprod,
      Real.log_one, zero_div]
  · conv_lhs => rw [hP.1.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    congr 3
    funext i
    change (hP.1.eigenvalues i : ℂ) = (Real.exp (2 * (Real.log (hP.1.eigenvalues i) / 2)) : ℂ)
    rw [show 2 * (Real.log (hP.1.eigenvalues i) / 2) = Real.log (hP.1.eigenvalues i) by ring,
      Real.exp_log (hP.eigenvalues_pos i)]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_diagonal_conjTranspose {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (δ : ι → ℝ) (s : ℝ) :
    ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ)ᴴ =
      (U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ := by
  simp [conjTranspose_mul, Matrix.mul_assoc, diagonal_conjTranspose, -Complex.ofReal_exp, Pi.star_def]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma unitary_conj_exp_diagonal_mul_add_exponents {ι : Type} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (δ : ι → ℝ) (s t : ℝ) :
    ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ) *
        ((U * diagonal fun i => ((Real.exp (t * δ i) : ℝ) : ℂ)) * Uᴴ) =
      (U * diagonal fun i => ((Real.exp ((s + t) * δ i) : ℝ) : ℂ)) * Uᴴ := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU', Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _),
    diagonal_mul_diagonal]
  simp only [← Complex.ofReal_mul, ← Real.exp_add, ← add_mul]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
private lemma exists_unitary_exp_diagonal_fixing_of_nsq_eq {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (hv : _root_.GlobalTheory.ClassFin.IsMinVec d v)
    (g : Matrix ι ι ℂ) (hg : g.det = 1)
    (hn : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v g) = _root_.GlobalTheory.ClassFin.nsq v) :
    ∃ (U : Matrix ι ι ℂ) (δ : ι → ℝ), U * Uᴴ = 1 ∧ ∑ i, δ i = 0 ∧
      g * gᴴ = (U * diagonal fun i => ((Real.exp (2 * δ i) : ℝ) : ℂ)) * Uᴴ ∧
      ∀ s : ℝ, _root_.GlobalTheory.ClassFin.act d v
        ((U * diagonal fun i => ((Real.exp (s * δ i) : ℝ) : ℂ)) * Uᴴ) = v := by
  have hdetP : (g * gᴴ).det = 1 := by simp [hg]
  have hP : (g * gᴴ).PosDef :=
    (posSemidef_self_mul_conjTranspose g).posDef_iff_isUnit.mpr
      ((isUnit_iff_isUnit_det _).mpr (by rw [hdetP]; exact isUnit_one))
  obtain ⟨U, δ, hU, hδ, hgP⟩ := posDef_det_one_exists_unitary_exp_diagonal_sum_zero _ hP hdetP
  refine ⟨U, δ, hU, hδ, hgP, ?_⟩
  obtain ⟨-, hactmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  have hgu : IsUnit g.det := by rw [hg]; exact isUnit_one
  have hhh : ((U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ) *
      ((U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ)ᴴ = g * gᴴ := by
    rw [unitary_conj_exp_diagonal_conjTranspose, unitary_conj_exp_diagonal_mul_add_exponents hU, hgP]
    norm_num
  set h : Matrix ι ι ℂ := (U * diagonal fun i => ((Real.exp (1 * δ i) : ℝ) : ℂ)) * Uᴴ with hh
  have hk : (g⁻¹ * h) * (g⁻¹ * h)ᴴ = 1 := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h, hhh, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, nonsing_inv_mul _ hgu, Matrix.one_mul, conjTranspose_nonsing_inv,
      mul_nonsing_inv _ (by simp [hg])]
  have hgk : h = g * (g⁻¹ * h) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hgu, Matrix.one_mul]
  have hnh : _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v h) = _root_.GlobalTheory.ClassFin.nsq v := by
    rw [hgk, hactmul, (_root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity ι m d).1 _ _ hk, hn]
  rw [hh] at hnh
  exact _root_.GlobalTheory.ClassFin.act_exp_eq_of_isMinVec ι m d v U δ hv hU hδ (by simpa only [one_mul] using hnh)


open Matrix in
open scoped Kronecker ComplexOrder TensorProduct MatrixOrder in
theorem _root_.GlobalTheory.ClassFin.act_conjTranspose_of_isMinVec : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ)
    (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ), _root_.GlobalTheory.ClassFin.IsMinVec d v → ∀ g : Matrix ι ι ℂ, g.det = 1 →
      _root_.GlobalTheory.ClassFin.act d v g = v → _root_.GlobalTheory.ClassFin.act d v gᴴ = v := by
  intro ι _ _ m d v hv g hg hgv
  obtain ⟨U, δ, -, -, hgP, hfix⟩ := exists_unitary_exp_diagonal_fixing_of_nsq_eq d v hv g hg (by rw [hgv])
  obtain ⟨-, hactmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  calc _root_.GlobalTheory.ClassFin.act d v gᴴ
      = _root_.GlobalTheory.ClassFin.act d (_root_.GlobalTheory.ClassFin.act d v g) gᴴ := by rw [hgv]
    _ = _root_.GlobalTheory.ClassFin.act d v (g * gᴴ) := (hactmul g gᴴ).symm
    _ = v := by rw [hgP]; exact hfix 2

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeMulCardPlacesLeCardOverKummer
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem prime_mul_card_le_card_over : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → p * S.card ≤ SE.card + (p - 1) * tNon p F δ S := by
  intro p F E _ _ _ _ _ ζ δ θ σ hq S SE hSE
  classical
  have hp := hq.prime
  obtain ⟨-, hrk, hgal, -, -, -, hemb⟩ := kummer_galois p F E ζ δ θ σ hq
  have h1 : SE.card = ∑ v ∈ S, (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun w hw => (hSE w).1 hw)
  have h2 : tNon p F δ S
      = ∑ v ∈ S, if (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ)
        then 1 else 0 := by
    rw [← Finset.card_filter, tNon, ← Set.ncard_coe_finset]
    congr 1
    ext v
    simp
  rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib, mul_comm, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_le_sum (fun v hv => ?_)
  by_cases hs : ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ
  · obtain ⟨w, hw⟩ := (places_over F E).2.1 v
    have : 0 < (SE.filter (fun w => w.under (𝓞 F) = v)).card :=
      Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨(hSE w).2 (hw ▸ hv), hw⟩⟩
    rw [if_pos hs]
    omega
  · rw [if_neg hs]
    push Not at hs
    obtain ⟨r, hr⟩ := hs
    have hδ : δ ≠ 0 := fun h0 => hq.nonpow 0 (by rw [h0, zero_pow hp.ne_zero])
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at hr
      exact hδ hr
    obtain ⟨ψ, hψ⟩ := hemb (v.adicCompletion F) r hr
    obtain ⟨ψ', hψ'⟩ := hemb (v.adicCompletion F) (algebraMap F (v.adicCompletion F) ζ * r)
      (by rw [mul_pow, ← map_pow, hq.root.pow_eq_one, map_one, one_mul, hr])
    have hne : ψ ≠ ψ' := by
      intro h
      rw [← h, hψ, eq_comm, mul_eq_right₀ hr0,
        ← map_one (algebraMap F (v.adicCompletion F))] at hψ'
      exact hq.root.ne_one hp.one_lt ((algebraMap F (v.adicCompletion F)).injective hψ')
    obtain ⟨w, w', hww, hw, hw'⟩ := two_places_of_embeddings F E v ψ ψ' hne
    have h3 := ncard_places_over_eq_of_prime_degree p F E hp hrk v w w' hww hw hw'
    have h4 : (SE.filter (fun w => w.under (𝓞 F) = v)).card = p := by
      rw [← h3, ← Set.ncard_coe_finset]
      congr 1
      ext u
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨fun h => h.2, fun h => ⟨(hSE u).2 (h ▸ hv), h⟩⟩
    omega

end GlobalTheory.CNorm
end

