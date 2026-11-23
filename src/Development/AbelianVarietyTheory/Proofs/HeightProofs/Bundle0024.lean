module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmooth
section
open GlobalTheory.FockCompare
open scoped ContDiff

namespace GlobalTheory.FockCompare

theorem hD_eq_fderiv {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) (u : R) (w : G) :
    hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w +
      fderiv ℝ (fun x : R => f (w + ι x)) 0 u := by
  have hd : DifferentiableAt ℝ (fun x : R => f (w + ι x)) ((0 : ℝ) • u) :=
    ((hf w).differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have h2 : HasDerivAt (fun t : ℝ => f (w + ι (t • u)))
      (fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul] at this
    exact this
  have h0 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ))
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) 0 := by
    refine HasDerivAt.const_mul _ (HasDerivAt.ofReal_comp ?_)
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (om (π w) u)
  have h3 := (h0.cexp.mul h2).deriv
  unfold hD
  refine Eq.trans h3 ?_
  simp

theorem hD_formula_smooth : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) →
    ∀ (f : G → ℂ), Sm ι f → ∀ u : R,
      (∀ w, hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w +
        fderiv ℝ (fun x : R => f (w + ι x)) 0 u) ∧ Sm ι (hD ι π om u f) := by
  intro G R _ _ _ _ ι π om hπ f hf u
  refine ⟨hD_eq_fderiv ι π om f hf u, fun w => ?_⟩
  have e : (fun x : R => hD ι π om u f (w + ι x)) = fun x : R =>
      -(Real.pi * Complex.I) * ((om.flip u (π w + x) : ℝ) : ℂ) * f (w + ι x) +
        fderiv ℝ (fun y : R => f (w + ι y)) x u := by
    funext x
    rw [hD_eq_fderiv ι π om f hf, map_add π, hπ, LinearMap.flip_apply]
    congr 2
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => f (w + ι y)) (x := 0) x
    rw [add_zero] at this
    rw [← this]
    congr 1
    funext y
    rw [map_add (f := _), add_assoc]
  rw [e]
  have h1 : ContDiff ℝ ∞ fun x : R => (om.flip u (π w + x) : ℝ) :=
    (LinearMap.toContinuousLinearMap (om.flip u)).contDiff.comp (contDiff_const.add contDiff_id)
  refine ContDiff.add (ContDiff.mul (ContDiff.mul contDiff_const
    (Complex.ofRealCLM.contDiff.comp h1)) (hf w)) ?_
  exact ((hf w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

end GlobalTheory.FockCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HermitianMajorantIsCartanInvolutionAndCommuteIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.CartanRel

theorem J_mul_J (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem J_conjTranspose (p q : ℕ) : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem isKC_iff {p q : ℕ} (b : Mat p q) : IsKC b ↔ b * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * b := by
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ]
  constructor
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases i with i | i <;> rcases j with j | j
    · simp
    · simp [h (Sum.inl i) (Sum.inr j) (by simp [sameBlock])]
    · simp [h (Sum.inr i) (Sum.inl j) (by simp [sameBlock])]
    · simp
  · intro h i j hij
    have e := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    rcases i with i | i <;> rcases j with j | j
    · simp [sameBlock] at hij
    · simp only [Sum.elim_inl, Sum.elim_inr] at e
      linear_combination (-1 / 2 : ℂ) * e
    · simp only [Sum.elim_inl, Sum.elim_inr] at e
      linear_combination (1 / 2 : ℂ) * e
    · simp [sameBlock] at hij

theorem cartan_rel : ∀ (n p q : ℕ), p + q = n → ∀ (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (G t : Matrix (Fin n) (Fin n) ℂ), G.det ≠ 0 → Aᴴ * Formalism.UG.Jpq p q * A = G → Formalism.UG.Jpq p q * A = A * t → IsCart G t ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, (∃ b : Mat p q, IsKC b ∧ b * A = A * g) ↔ Commute g t := by
  intro n p q hn A G t hG hA ht
  have hJ := J_mul_J p q
  have hJc := J_conjTranspose p q
  generalize hJdef : Formalism.UG.Jpq p q = J at hJ hJc hA ht
  obtain ⟨B, hBA, hAB⟩ : ∃ B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ, B * A = 1 ∧ A * B = 1 := by
    have h1 : (G⁻¹ * (Aᴴ * J)) * A = 1 := by
      rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ (Ne.isUnit hG)]
    exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 h1⟩
  have cancel : ∀ x y : Matrix (Fin n) (Fin n) ℂ, A * x = A * y → x = y := by
    intro x y h
    have := congrArg (B * ·) h
    simpa only [← Matrix.mul_assoc, hBA, Matrix.one_mul] using this
  have hJJ : J * (J * A) = A := by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hGt : G * t = Aᴴ * A := by
    rw [← hA, Matrix.mul_assoc, ← ht, Matrix.mul_assoc, hJJ]
  refine ⟨⟨?_, ?_, ?_⟩, fun g => ⟨?_, ?_⟩⟩
  · apply cancel
    rw [← Matrix.mul_assoc, ← ht, Matrix.mul_assoc, ← ht, hJJ, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hGt, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, ← ht,
      Matrix.conjTranspose_mul, hJc, hA]
  · rw [hGt]
    refine Matrix.PosDef.conjTranspose_mul_self A ?_
    intro x y h
    have := congrArg (B.mulVec) h
    simpa only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] using this
  · rintro ⟨b, hb, hbA⟩
    rw [isKC_iff, hJdef] at hb
    apply cancel
    calc A * (g * t) = b * (J * A) := by rw [← Matrix.mul_assoc, ← hbA, Matrix.mul_assoc, ← ht]
      _ = J * (A * g) := by rw [← Matrix.mul_assoc, hb, Matrix.mul_assoc, hbA]
      _ = A * (t * g) := by rw [← Matrix.mul_assoc, ht, Matrix.mul_assoc]
  · intro h
    refine ⟨A * g * B, ?_, ?_⟩
    · rw [isKC_iff, hJdef]
      have hBJ : B * J = t * B := by
        calc B * J = B * (J * A) * B := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc, hAB, Matrix.mul_one]
          _ = t * B := by rw [ht, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
      calc A * g * B * J = A * (g * t) * B := by
            rw [Matrix.mul_assoc, hBJ]; simp only [Matrix.mul_assoc]
        _ = A * t * (g * B) := by rw [h.eq]; simp only [Matrix.mul_assoc]
        _ = J * (A * g * B) := by rw [← ht]; simp only [Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hBA, Matrix.mul_one]

end GlobalTheory.FockCompare.CartanRel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKilledByOperatorProductsSuccCreationApply
section
namespace GlobalTheory.FockCompare.WeylCreate

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M] {a : I → Module.End ℂ M}

theorem killed_succ_iff (N : ℕ) (m : M) : Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    rcases List.eq_nil_or_concat l with rfl | ⟨l', i, rfl⟩
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

theorem foldr_add_smul (l : List I) (β : ℂ) (x y : M) :
    l.foldr (fun i x => a i x) (x + β • y) =
      l.foldr (fun i x => a i x) x + β • l.foldr (fun i x => a i x) y := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_add (f := _), map_smul]

theorem foldr_zero (l : List I) : l.foldr (fun i x => a i x) (0 : M) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, map_zero]

theorem killed_create : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a : I → Module.End ℂ M) (c : Module.End ℂ M),
    (∀ i, ∃ β : ℂ, a i * c - c * a i = β • (1 : Module.End ℂ M)) →
    ∀ (N : ℕ) (m : M), Killed a N m → Killed a (N + 1) (c m) := by
  intro I M _ _ a c hc N
  induction N with
  | zero =>
    intro m hm l _
    have h0 : m = 0 := hm [] rfl
    rw [h0, map_zero]
    exact foldr_zero l
  | succ N ih =>
    intro m hm
    rw [killed_succ_iff]
    intro i
    obtain ⟨β, hβ⟩ := hc i
    have e : a i (c m) = c (a i m) + β • m := by
      have := LinearMap.congr_fun hβ m
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      rw [← this]; abel
    have h1 := ih (a i m) ((killed_succ_iff N m).1 hm i)
    intro l hl
    rw [e, foldr_add_smul, h1 l hl, hm l hl, smul_zero, add_zero]

end GlobalTheory.FockCompare.WeylCreate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.JpqMulMonomialEqMulSignDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MonomialSign

theorem diagonal_mul_eq {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι) (ε : ι → ℝ) (hε : ∀ a, ε a = 1 ∨ ε a = -1)
    (M : Matrix ι κ ℂ) (d : κ → ℝ) (hd : ∀ i, d i ≠ 0)
    (hM : Mᴴ * Matrix.diagonal (fun a => (ε a : ℂ)) * M = Matrix.diagonal (fun i => (d i : ℂ)))
    (hrow : ∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) :
    Matrix.diagonal (fun a => (ε a : ℂ)) * M
      = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  have hsum : ∀ i, d i = ∑ a, ε a * Complex.normSq (M a i) := by
    intro i
    have h := congrFun (congrFun hM i) i
    rw [Matrix.diagonal_apply_eq, Matrix.mul_apply] at h
    apply Complex.ofReal_injective
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self,
      Complex.star_def]
    ring
  have hex : ∀ i, ∃ a, M a i ≠ 0 := by
    intro i
    by_contra hne
    push Not at hne
    apply hd i
    rw [hsum i]
    simp [hne]
  choose r hr using hex
  have hinj : Function.Injective r := fun i j hij => hrow (r i) i j (hr i) (hij ▸ hr j)
  have hbij : Function.Bijective r :=
    (Fintype.bijective_iff_injective_and_card r).2 ⟨hinj, hcard⟩
  have huniq : ∀ a i, M a i ≠ 0 → a = r i := by
    intro a i h
    obtain ⟨j, rfl⟩ := hbij.2 a
    rw [hrow (r j) i j h (hr j)]
  ext a i
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : M a i = 0
  · simp [h]
  · have ha := huniq a i h
    have hdi : d i = ε a * Complex.normSq (M a i) := by
      rw [hsum i]
      refine Finset.sum_eq_single a (fun b _ hb => ?_) (by simp)
      have : M b i = 0 := by
        by_contra hb'
        exact hb ((huniq b i hb').trans ha.symm)
      simp [this]
    have hpos : 0 < Complex.normSq (M a i) := Complex.normSq_pos.2 h
    rcases hε a with h1 | h1
    · have : 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]
    · have : ¬ 0 < d i := by rw [hdi, h1]; linarith
      simp [this, h1]

theorem Jpq_mul_eq : ∀ (n p q : ℕ), p + q = n → ∀ (M : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (d : Fin n → ℝ), (∀ i, d i ≠ 0) → Mᴴ * Formalism.UG.Jpq p q * M = Matrix.diagonal (fun i => (d i : ℂ)) → (∀ a i j, M a i ≠ 0 → M a j ≠ 0 → i = j) → Formalism.UG.Jpq p q * M = M * Matrix.diagonal (fun i => if 0 < d i then (1 : ℂ) else -1) := by
  intro n p q hn M d hd hM hrow
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal
      (fun a => ((Sum.elim (fun _ => 1) (fun _ => -1) a : ℝ) : ℂ)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ] at hM ⊢
  refine diagonal_mul_eq (by simp [hn]) _ ?_ M d hd hM hrow
  rintro (a | a) <;> simp

end GlobalTheory.MonomialSign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemOfIsKilledByOperatorProductsVacuumCreation
section
noncomputable section

namespace GlobalTheory.FockCompare.WeylInduct

open GlobalTheory.FockCompare

variable {I M : Type} [AddCommGroup M] [Module ℂ M]

theorem killed_zero (a : I → Module.End ℂ M) (m : M) : Killed a 0 m ↔ m = 0 := by
  constructor
  · intro h; exact h [] rfl
  · intro h l hl
    obtain rfl := List.length_eq_zero_iff.1 hl
    exact h

theorem killed_succ (a : I → Module.End ℂ M) (N : ℕ) (m : M) :
    Killed a (N + 1) m ↔ ∀ i, Killed a N (a i m) := by
  constructor
  · intro h i l hl
    have := h (l ++ [i]) (by simp [hl])
    simpa [List.foldr_append] using this
  · intro h l hl
    obtain rfl | ⟨l', i, rfl⟩ := List.eq_nil_or_concat l
    · simp at hl
    · have := h i l' (by simpa using hl)
      simpa [List.foldr_append] using this

noncomputable def prodE (E : Module.End ℂ M) (lam : ℂ) : ℕ → ℕ → M → M
  | 0, _, x => x
  | N + 1, j, x => prodE E lam N (j + 1) (E x - ((j : ℂ) * lam) • x)

theorem prodE_comm (E : Module.End ℂ M) (lam : ℂ) (N : ℕ) :
    ∀ (j : ℕ) (x : M), prodE E lam N j (E x) = E (prodE E lam N j x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [← ih, map_sub, map_smul]

theorem shift_prodE (E A : Module.End ℂ M) (lam : ℂ) (h : ∀ x, A (E x) = E (A x) + lam • A x) (N : ℕ) :
    ∀ (j : ℕ) (x : M), A (prodE E lam N (j + 1) x) = prodE E lam N j (A x) := by
  induction N with
  | zero => intro j x; rfl
  | succ N ih =>
    intro j x
    simp only [prodE]
    rw [ih, map_sub, map_smul, h]
    congr 1
    push_cast
    module

theorem killed_stable (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (N : ℕ) :
    ∀ (t : ℂ) (x : M), Killed a N x → Killed a N (E x - t • x) := by
  induction N with
  | zero => intro t x hx; rw [killed_zero] at hx ⊢; simp [hx]
  | succ N ih =>
    intro t x hx
    rw [killed_succ] at hx ⊢
    intro i
    have e : a i (E x - t • x) = E (a i x) - (t - lam) • a i x := by
      rw [map_sub, map_smul, h]; module
    rw [e]
    exact ih _ _ (hx i)

theorem prodE_kills (a : I → Module.End ℂ M) (E : Module.End ℂ M) (lam : ℂ)
    (h : ∀ i x, a i (E x) = E (a i x) + lam • a i x) (h0 : ∀ x, (∀ i, a i x = 0) → E x = 0) (N : ℕ) :
    ∀ x : M, Killed a N x → prodE E lam N 0 x = 0 := by
  induction N with
  | zero => intro x hx; exact (killed_zero a x).1 hx
  | succ N ih =>
    intro x hx
    rw [killed_succ] at hx
    simp only [prodE, Nat.cast_zero, zero_mul, zero_smul, sub_zero]
    rw [prodE_comm]
    refine h0 _ fun i => ?_
    rw [shift_prodE E (a i) lam (h i), ih _ (hx i)]

theorem peel (E : Module.End ℂ M) (lam : ℂ) (hl : lam ≠ 0) (S : M → Prop) (P : Submodule ℂ M)
    (hS : ∀ (t : ℂ) x, S x → S (E x - t • x)) (hE : ∀ x, S x → E x ∈ P) (K : ℕ) :
    ∀ (j : ℕ) (x : M), S x → prodE E lam K (j + 1) x ∈ P → x ∈ P := by
  induction K with
  | zero => intro j x _ hx; exact hx
  | succ K ih =>
    intro j x hx hp
    simp only [prodE] at hp
    have h1 := ih _ _ (hS _ x hx) hp
    have h2 := P.sub_mem (hE x hx) h1
    rw [sub_sub_cancel] at h2
    exact (P.smul_mem_iff (mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)) hl)).1 h2

theorem mem_of_killed : ∀ (I M : Type) [AddCommGroup M] [Module ℂ M] (a c : I → Module.End ℂ M) (n : ℕ) (e : Fin n → I) (lam : ℂ), lam ≠ 0 → (∀ i, a i * (∑ k, c (e k) * a (e k)) = ((∑ k, c (e k) * a (e k)) + lam • (1 : Module.End ℂ M)) * a i) → ∀ P : Submodule ℂ M, (∀ m, (∀ i, a i m = 0) → m ∈ P) → (∀ i, ∀ m ∈ P, c i m ∈ P) → ∀ (N : ℕ) (m : M), Killed a N m → m ∈ P := by
  intro I M _ _ a c n e lam hl hc P hv hP N
  set E : Module.End ℂ M := ∑ k, c (e k) * a (e k) with hEdef
  have hEx : ∀ x, E x = ∑ k, c (e k) (a (e k) x) := by
    intro x; simp [hEdef, LinearMap.sum_apply]
  have h : ∀ i x, a i (E x) = E (a i x) + lam • a i x := by
    intro i x
    have := LinearMap.congr_fun (hc i) x
    simpa using this
  have h0 : ∀ x, (∀ i, a i x = 0) → E x = 0 := by
    intro x hx; simp [hEx, hx]
  induction N with
  | zero => intro m hm; rw [(killed_zero a m).1 hm]; exact P.zero_mem
  | succ N ih =>
    intro m hm
    refine peel E lam hl (Killed a (N + 1)) P (killed_stable a E lam h (N + 1)) (fun x hx => ?_) N 0 m hm
      (hv _ fun i => ?_)
    · rw [hEx]
      exact P.sum_mem fun k _ => hP _ _ (ih _ ((killed_succ a N x).1 hx _))
    · rw [shift_prodE E (a i) lam (h i)]
      exact prodE_kills a E lam h h0 N _ ((killed_succ a N m).1 hm i)

end GlobalTheory.FockCompare.WeylInduct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NegTraceSymplecticFormComplexStructurePos
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder Kronecker

namespace GlobalTheory.FockCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sum_kron_pos {m n : ℕ} {P : Matrix (Fin m) (Fin m) ℂ} {Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) (x : Matrix (Fin m) (Fin n) ℂ) (hx : x ≠ 0) :
    0 < ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (x i j) * P i k * Q j l * x k l := by
  have h := (hP.kronecker hQ).dotProduct_mulVec_pos (x := fun p : Fin m × Fin n => x p.1 p.2)
    (fun h0 => hx (by ext i j; exact congrFun h0 (i, j)))
  convert h using 1
  simp only [dotProduct, mulVec, Fintype.sum_prod_type, Finset.mul_sum, kroneckerMap_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
  rw [Complex.star_def]; ring

theorem IsCart.adj_mul {n : ℕ} {G t : Matrix (Fin n) (Fin n) ℂ} (h : IsCart G t) :
    (t.map (starRingEnd ℂ))ᵀ * G = G * t := by
  have e : (t.map (starRingEnd ℂ))ᵀ = tᴴ := by ext i j; rfl
  rw [e]
  calc tᴴ * G = tᴴ * G * (t * t) := by rw [h.1, Matrix.mul_one]
    _ = G * t := by rw [← Matrix.mul_assoc, h.2.1]

theorem hC_actC_pos {D : D7} (V W : HSp D) (τ : D.what₂.Tau) (t : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (t' : Matrix (Fin W.rank) (Fin W.rank) ℂ) (h : IsCart (gramAt D V τ) t) (h' : IsCart (gramAt D W τ) t')
    (x : WC V W) (hx : x ≠ 0) : 0 < hC V W τ x (actC V W t t' x) := by
  unfold hC actC
  split_ifs with hr
  · have p := sum_kron_pos h.2.2.transpose h'.2.2 x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_small] at p ⊢
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    convert p using 2
    rw [← h.adj_mul]
    simp only [Matrix.mul_assoc]
  · have p := sum_kron_pos h.2.2 h'.2.2.transpose x hx
    simp only [Matrix.transpose_apply] at p
    rw [GlobalTheory.DualPairCheck.sum_large] at p ⊢
    convert p using 2
    rw [← h'.adj_mul]
    simp only [Matrix.mul_assoc]

theorem symplC_jAt_neg : ∀ (D : D7) (V W : HSp D) (τ : D.what₂.Tau) (s : Module.End D.host.E V.V)
    (s' : Module.End D.host.E W.V), IsCart (gramAt D V τ) (thAt V τ s) → IsCart (gramAt D W τ) (thAt W τ s') →
    ∀ x : WC V W, x ≠ 0 → 0 < -symplC V W τ (jAt V W τ s s' x) x := by
  intro D V W τ s s' h h' x hx
  have p := hC_actC_pos V W τ _ _ h h' x hx
  have q := xi_zero_im_pos D τ
  unfold symplC jAt
  rw [hC_smul_right]
  obtain ⟨p1, p2⟩ := Complex.pos_iff.1 p
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, ← p2]
  nlinarith [mul_pos p1 q]

end GlobalTheory.FockCompare
end

