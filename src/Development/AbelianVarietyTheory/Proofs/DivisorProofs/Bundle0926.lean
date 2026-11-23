module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import GroundTheory.Brauer.TensorSimple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicGroupLawSplitByIdempotent
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemImage

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def lin {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : Fin m → MvPowerSeries (Fin n) C :=
  fun a => ∑ b, N a b • X b

theorem lin_const {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : constantCoeff (lin N a) = 0 := by
  simp [lin]

theorem lin_hs {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : HasSubst (lin N) :=
  hasSubst_of_constantCoeff_zero (lin_const N)

theorem int_comb {σ ι : Type} [Fintype ι] {c : ι → C} (hc : ∀ i, IsIntV v (c i))
    {f : ι → MvPowerSeries σ C} (hf : ∀ i, MvIsInt v (f i)) : MvIsInt v (∑ i, c i • f i) :=
  (ptIntSer v σ).sum_mem fun i _ => ptIntSer_smul (hc i) (hf i)

theorem lin_int {m n : ℕ} {N : Matrix (Fin m) (Fin n) C} (h : ∀ a b, IsIntV v (N a b)) (a : Fin m) :
    MvIsInt v (lin N a) := int_comb (h a) fun b => ptIntSer_X b

theorem lin_coeff {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (lin N a) = N a i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin, map_sum, pt_coeff_single_X]

theorem const_comb {σ ι : Type} [Fintype ι] (c : ι → C) {f : ι → MvPowerSeries σ C}
    (hf : ∀ i, constantCoeff (f i) = 0) : constantCoeff (∑ i, c i • f i) = 0 := by
  simp [hf]

theorem comb_comb {σ : Type} {l m n : ℕ} (A : Matrix (Fin l) (Fin m) C) (B : Matrix (Fin m) (Fin n) C)
    (f : Fin n → MvPowerSeries σ C) (b : Fin l) :
    ∑ a, A b a • ∑ e, B a e • f e = ∑ e, (A * B) b e • f e := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem comb_one {σ : Type} {n : ℕ} (f : Fin n → MvPowerSeries σ C) (b : Fin n) :
    ∑ e, (1 : Matrix (Fin n) (Fin n) C) b e • f e = f b := by
  simp [Matrix.one_apply, ite_smul]

theorem subst_lin {σ : Type} {m n : ℕ} {s : Fin n → MvPowerSeries σ C} (hs : HasSubst s)
    (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : subst s (lin N a) = ∑ b, N a b • s b := by
  rw [lin, subst_sum_smul hs]
  simp only [subst_X hs]

theorem coeff_comb_lg {d m n : ℕ} (G : LogFGL v d) (N : Matrix (Fin m) (Fin d) C)
    (L : Matrix (Fin d) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (∑ e, N a e • (subst (lin L) (G.lg e) : MvPowerSeries (Fin n) C)) = (N * L) a i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, pt_coeff_single_subst (lin_hs L) (lin_const L) (G.lg_const _), G.lg_lin, lin_coeff,
    Matrix.mul_apply]

theorem lg_add {σ : Type} [Finite σ] {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    subst (fun b => (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C)) (G.lg a) =
      subst x (G.lg a) + subst y (G.lg a) := by
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero (by rintro (b | b) <;> simp [hx, hy])
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) hs, G.lg_F, subst_add hs,
    subst_comp_subst_apply hl hs, subst_comp_subst_apply hr hs]
  simp only [subst_X hs, Sum.elim_inl, Sum.elim_inr]

theorem add_const {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (b : Fin d) :
    constantCoeff (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) = 0 :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (G.F_const b)

theorem add_int {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0)
    (ix : ∀ a, MvIsInt v (x a)) (iy : ∀ a, MvIsInt v (y a)) (b : Fin d) :
    MvIsInt v (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  ptIntSer_subst (hasSubst_of_constantCoeff_zero h) (by rintro (b | b); exacts [ix b, iy b]) (G.F_int b)

theorem lg_hom {σ : Type} {d m : ℕ} {f : MvPowerSeries (Fin d) C} {φ : Fin d → MvPowerSeries (Fin m) C}
    (h0 : ∀ a, constantCoeff (φ a) = 0) {c : Fin m → C} {g : Fin m → MvPowerSeries (Fin m) C}
    (h : subst φ f = ∑ a, c a • g a) {s : Fin m → MvPowerSeries σ C} (hs : HasSubst s) :
    subst (fun b => (subst s (φ b) : MvPowerSeries σ C)) f = ∑ a, c a • (subst s (g a) : MvPowerSeries σ C) := by
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hs, h, subst_sum_smul hs]

theorem exists_retraction [CharZero C] {d d' : ℕ} (G : LogFGL v d) {I : Matrix (Fin d) (Fin d') C}
    {P : Matrix (Fin d') (Fin d) C} (hI : ∀ a b, IsIntV v (I a b)) (hP : ∀ a b, IsIntV v (P a b))
    (hPI : P * I = 1) {φ ψ : Fin d → MvPowerSeries (Fin d) C} (hφ : IsIntHom G G φ (I * P))
    (hψ : IsIntHom G G ψ (1 - I * P)) :
    ∃ q : Fin d' → MvPowerSeries (Fin d) C, (∀ b, constantCoeff (q b) = 0) ∧ (∀ b, MvIsInt v (q b)) ∧
      ∀ b, subst q (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) = ∑ a, P b a • G.lg a := by
  have hMi : ∀ a b, IsIntV v ((I * P) a b) := fun a b => by
    rw [Matrix.mul_apply]
    exact (ptIntSub v).sum_mem fun c _ => (ptIntSub v).mul_mem (hI a c) (hP c b)
  have hNi : ∀ a b, IsIntV v ((1 - I * P : Matrix (Fin d) (Fin d) C) a b) := fun a b => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine (ptIntSub v).sub_mem ?_ (hMi a b)
    split_ifs
    exacts [(ptIntSub v).one_mem, (ptIntSub v).zero_mem]
  have hPM : P * (I * P) = P := by rw [← Matrix.mul_assoc, hPI, Matrix.one_mul]
  have hPN : P * (1 - I * P : Matrix (Fin d) (Fin d) C) = 0 := by rw [Matrix.mul_sub, hPM, Matrix.mul_one, sub_self]
  have hMM : I * P * (I * P) = I * P := by rw [Matrix.mul_assoc, hPM]
  have hsq : I * P * (I * P) + (1 - I * P : Matrix (Fin d) (Fin d) C) * (1 - I * P : Matrix (Fin d) (Fin d) C) = 1 := by
    rw [mul_sub, sub_mul, sub_mul, hMM]; simp
  generalize hM : I * P = M at *
  generalize (1 - M : Matrix (Fin d) (Fin d) C) = N at *
  set x : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin M) (φ a) with hx
  set y : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin N) (ψ a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs M) (lin_const M) (hφ.1 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs N) (lin_const N) (hψ.1 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst (lin_hs M) (lin_int hMi) (hφ.2.1 a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst (lin_hs N) (lin_int hNi) (hψ.2.1 a)
  set Θ : Fin d → MvPowerSeries (Fin d) C := fun b => subst (Sum.elim x y) (G.F b) with hΘ
  have Θ0 : ∀ a, constantCoeff (Θ a) = 0 := add_const G x0 y0
  have Θs : HasSubst Θ := hasSubst_of_constantCoeff_zero Θ0
  have hlg : ∀ a, subst Θ (G.lg a) = ∑ e, M a e • (subst (lin M) (G.lg e) : MvPowerSeries (Fin d) C) +
      ∑ e, N a e • (subst (lin N) (G.lg e) : MvPowerSeries (Fin d) C) := fun a => by
    rw [hΘ, lg_add G x0 y0, hx, hy, lg_hom hφ.1 (hφ.2.2 a) (lin_hs M), lg_hom hψ.1 (hψ.2.2 a) (lin_hs N)]
  have Θ1 : ∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0 := fun a b => by
    have h := congrArg (coeff (Finsupp.single b 1)) (hlg a)
    rw [map_add (f := _), coeff_comb_lg, coeff_comb_lg, ← Matrix.add_apply, hsq, Matrix.one_apply,
      pt_coeff_single_subst Θs Θ0 (G.lg_const a)] at h
    simpa [G.lg_lin] using h
  obtain ⟨Ψ, Ψi, Ψ0, hΨ, -⟩ := GlobalTheory.IntInv.exists_int_inv C v d Θ (add_int G x0 y0 xi yi) Θ0 Θ1
  have Ψs : HasSubst Ψ := hasSubst_of_constantCoeff_zero Ψ0
  refine ⟨fun b => ∑ a, P b a • Ψ a, fun b => const_comb _ Ψ0, fun b => int_comb (hP b) Ψi, fun b => ?_⟩
  have key : subst (lin P) (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) =
      subst Θ (∑ a, P b a • G.lg a) := by
    have hl : (fun a => (subst (lin P) (lin I a) : MvPowerSeries (Fin d) C)) = lin M := by
      funext a
      rw [subst_lin (lin_hs P), ← hM]
      exact comb_comb I P _ a
    rw [subst_sum_smul (lin_hs P), subst_sum_smul Θs]
    simp only [hlg, smul_add, Finset.sum_add_distrib, comb_comb, hPM, hPN,
      subst_comp_subst_apply (lin_hs I) (lin_hs P), hl]
    simp
  have h := congrArg (subst Ψ) key
  rw [subst_comp_subst_apply (lin_hs P) Ψs, subst_comp_subst_apply Θs Ψs] at h
  simp only [subst_lin Ψs, hΨ] at h
  rw [h, show (fun a => (X a : MvPowerSeries (Fin d) C)) = X from rfl, subst_self]
  rfl

theorem exists_image (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d d' : ℕ) (G : LogFGL v d)
    (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C) (hI : ∀ a b, IsIntV v (I a b))
    (hP : ∀ a b, IsIntV v (P a b)) (hPI : P * I = 1) (hφ : ∃ φ, IsIntHom G G φ (I * P))
    (hψ : ∃ ψ, IsIntHom G G ψ (1 - I * P)) :
    ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨ψ, hψ⟩ := hψ
  obtain ⟨q, q0, qi, hq⟩ := exists_retraction G hI hP hPI hφ hψ
  set lg' : Fin d' → MvPowerSeries (Fin d') C := fun b => ∑ a, P b a • subst (lin I) (G.lg a) with hlg'
  set j : Fin d → MvPowerSeries (Fin d') C := fun a => subst (lin I) (φ a) with hjdef
  have j0 : ∀ a, constantCoeff (j a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (hφ.1 a)
  have ji : ∀ a, MvIsInt v (j a) := fun a => ptIntSer_subst (lin_hs I) (lin_int hI) (hφ.2.1 a)
  have hj : ∀ a, subst j (G.lg a) = ∑ e, I a e • lg' e := fun a => by
    rw [hjdef, lg_hom hφ.1 (hφ.2.2 a) (lin_hs I), hlg']
    exact (comb_comb I P _ a).symm
  have hl0 : ∀ b : Fin d', constantCoeff (X (Sum.inl b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hr0 : ∀ b : Fin d', constantCoeff (X (Sum.inr b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hl := hasSubst_of_constantCoeff_zero hl0
  have hr := hasSubst_of_constantCoeff_zero hr0
  set x : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inl b)) (j a) with hx
  set y : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inr b)) (j a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a => constantCoeff_subst_eq_zero hl hl0 (j0 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a => constantCoeff_subst_eq_zero hr hr0 (j0 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst hl (fun _ => ptIntSer_X _) (ji a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst hr (fun _ => ptIntSer_X _) (ji a)
  have s0 := add_const G x0 y0
  have ss := hasSubst_of_constantCoeff_zero s0
  refine ⟨{ lg := lg'
            lg_const := fun b => const_comb _ fun a =>
              constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (G.lg_const a)
            lg_lin := fun a b => by rw [hlg', coeff_comb_lg, hPI, Matrix.one_apply]
            F := fun b => subst (fun a => (subst (Sum.elim x y) (G.F a) : MvPowerSeries (Fin d' ⊕ Fin d') C)) (q b)
            F_int := fun b => ptIntSer_subst ss (add_int G x0 y0 xi yi) (qi b)
            F_const := fun b => constantCoeff_subst_eq_zero ss s0 (q0 b)
            lg_F := fun b => ?_ }, ⟨j, j0, ji, hj⟩, q, q0, qi, hq⟩
  rw [lg_hom q0 (hq b) ss]
  simp only [lg_add G x0 y0, smul_add, Finset.sum_add_distrib]
  simp only [hx, hy, lg_hom j0 (hj _) hl, lg_hom j0 (hj _) hr, comb_comb, hPI, comb_one]

end GlobalTheory.IdemImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEq
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.MarkEll

theorem star_mulVec_dot {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) :
    star (M *ᵥ a) ⬝ᵥ (A *ᵥ (M *ᵥ b)) = star a ⬝ᵥ ((Mᴴ * A * M) *ᵥ b) := by
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]

theorem normSq_eq_of_form {n : ℕ} (Γ A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hΓ : Γᴴ * A * Γ = (c : ℂ) • A)
    (x : Fin n → ℂ) (w : ℂ) (hx : Γ *ᵥ x = w • x) (h0 : star x ⬝ᵥ (A *ᵥ x) ≠ 0) : ‖w‖ ^ 2 = c := by
  have h := star_mulVec_dot Γ A x x
  rw [hΓ, hx] at h
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  rw [← mul_assoc] at h
  have h2 : w * star w = (c : ℂ) := mul_right_cancel₀ h0 h
  have h3 : ((‖w‖ ^ 2 : ℝ) : ℂ) = (c : ℂ) := by
    rw [← h2, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h3

theorem natDegree_minpoly_le_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := Polynomial.aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [Polynomial.coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem eigA : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g : G.C) (v : InfinitePlace G.F) (z : ℂ),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).eval₂ v.embedding z = 0 →
    ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v g *ᵥ x = z • x := by
  intro p _ G g v z hdeg hz
  letI alg : Algebra G.F ℂ := v.embedding.toAlgebra
  have halg : ∀ a : G.F, algebraMap G.F ℂ a = v.embedding a := fun a => rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun a => by
        change G.psi v (algebraMap G.F G.C a) = _
        rw [G.psi_F]
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply, halg] }
  let Θ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  have hinj : Function.Injective Θ :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain Θ.toRingHom).resolve_right
      (by haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩; exact not_subsingleton _)
  set x : ℂ ⊗[G.F] G.C := (1 : ℂ) ⊗ₜ[G.F] g with hx
  have hxi : IsIntegral ℂ x := IsIntegral.of_finite ℂ x
  have hge := natDegree_minpoly_le_tmul ℂ g hxi
  have hΘx : Θ x = G.psi v g := by
    rw [hx]
    first
      | (erw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl)
      | (show (Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)) 1 * ψF g = G.psi v g
         rw [map_one, one_mul]; rfl)
      | simp [Θ, ψF]
  have hmin : minpoly ℂ (G.psi v g) = minpoly ℂ x := by rw [← hΘx]; exact minpoly.algHom_eq Θ hinj x
  have hgi : IsIntegral G.F g := IsIntegral.of_finite G.F g
  have hdvd : minpoly ℂ (G.psi v g) ∣ (minpoly G.F g).map (algebraMap G.F ℂ) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval (ψF g) (minpoly G.F g) = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmon : ((minpoly G.F g).map (algebraMap G.F ℂ)).Monic := (minpoly.monic hgi).map _
  have heq : (minpoly G.F g).map (algebraMap G.F ℂ) = minpoly ℂ (G.psi v g) := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ?_) hmon hdvd ?_
    · exact IsIntegral.of_finite ℂ _
    · rw [Polynomial.natDegree_map, hmin]; exact hge
  have hroot : (minpoly ℂ (Matrix.toLin' (G.psi v g))).IsRoot z := by
    rw [Matrix.minpoly_toLin', ← heq, Polynomial.IsRoot, Polynomial.eval_map]
    exact hz
  obtain ⟨y, hy⟩ := (Module.End.hasEigenvalue_iff_isRoot.mpr hroot).exists_hasEigenvector
  refine ⟨y, hy.2, ?_⟩
  have := hy.apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

theorem normSq_of_eigenvector {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ) (ha : G.a = 1)
    (hm : P.Mark μ) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) (hx0 : x ≠ 0) (w : ℂ)
    (hx : G.psi v P.γ *ᵥ x = w • x) : ‖w‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  obtain ⟨-, -, hΓ⟩ := GlobalTheory.LKMid.pair_form_laws p G P v
  obtain ⟨Z, hZ⟩ := GlobalTheory.LKMid.Pair.gram_psi_inv_congr p G P v
  set A := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hAdef
  set Γ := G.psi v P.γ with hΓdef
  have hΓ' : Γᴴ * A * Γ = ((((P.c : ℚ) : ℝ)) : ℂ) • A := by rw [hΓ]; push_cast; rfl
  have cong : ∀ a b : Fin G.n → ℂ, star a ⬝ᵥ (A *ᵥ b) =
      star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a) ⬝ᵥ (G.gram v *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b)) := by
    intro a b; rw [star_mulVec_dot, ← hZ]
  have Zne : ∀ a : Fin G.n → ℂ, a ≠ 0 → (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a ≠ 0 := by
    intro a ha h
    apply ha
    have := congrArg (fun y => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) h
    simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, mulVec_zero] using this
  have hc0 : ((((P.c : ℚ) : ℝ)) : ℂ) ≠ 0 := by
    have : ((P.c : ℚ)) ≠ 0 := P.c.ne_zero
    exact_mod_cast this
  rcases G.sig v with ⟨h1, -⟩ | ⟨h0, -⟩
  · obtain ⟨v0, hv0, x0, hx0e, hpos⟩ := hm
    have hv : v = v0 := by
      have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := by
        have := ha; unfold HTGroup.a at this; omega
      haveI := Fintype.card_le_one_iff_subsingleton.mp hcard
      exact congrArg Subtype.val (Subsingleton.elim (⟨v, h1⟩ : {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1})
        ⟨v0, hv0⟩)
    subst hv
    have hS0 : star x0 ⬝ᵥ (A *ᵥ x0) ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hμ : ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := normSq_eq_of_form Γ A _ hΓ' x0 μ hx0e hS0
    by_cases hw : w = μ
    · rw [hw]; exact hμ
    · have hS : star x0 ⬝ᵥ (A *ᵥ x) = 0 := by
        by_contra hne
        have h := star_mulVec_dot Γ A x0 x
        rw [hΓ', hx0e, hx] at h
        simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
          smul_eq_mul] at h
        rw [← mul_assoc] at h
        have h2 := mul_right_cancel₀ hne h
        have hμ2 : μ * star μ = ((((P.c : ℚ) : ℝ)) : ℂ) := by
          rw [← hμ, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hμ0 : star μ ≠ 0 := by
          intro h0; apply hc0; rw [← hμ2, h0, mul_zero]
        apply hw
        apply mul_right_cancel₀ hμ0
        rw [hμ2]
        first | exact h2 | (rw [mul_comm]; exact h2)
      apply normSq_eq_of_form Γ A _ hΓ' x w hx
      intro h
      have hneg := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one (G.gram v) (G.gram_herm v) (G.gram_det v) h1 _ _
        (by rw [← cong]; exact hpos) (by rw [← cong]; exact hS) (Zne x hx0)
      rw [← cong, h] at hneg; simp at hneg
  · apply normSq_eq_of_form Γ A _ hΓ' x w hx
    intro h
    have hneg := GlobalTheory.herm_negDef_of_sigPosH_eq_zero (G.gram v) (G.gram_herm v) (G.gram_det v) h0 _ (Zne x hx0)
    rw [← cong, h] at hneg; simp at hneg

theorem mark_ell : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ (φ : G.F →+* ℂ) (z : ℂ), P.pol.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ ha hm φ z hz
  have hdeg : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) z hdeg (by rw [h]; exact hz)
    exact normSq_of_eigenvector G P μ ha hm _ x hx0 z hx
  · have hz' : (minpoly G.F (P.γ : G.C)).eval₂ (InfinitePlace.mk φ).embedding (star z) = 0 := by
      have e : (InfinitePlace.mk φ).embedding = (starRingEnd ℂ).comp φ := by
        rw [h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
      have := Polynomial.hom_eval₂ P.pol φ (starRingEnd ℂ) z
      rw [hz, map_zero] at this
      rw [e]; exact this.symm
    obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) (star z) hdeg hz'
    have := normSq_of_eigenvector G P μ ha hm _ x hx0 (star z) hx
    rwa [norm_star] at this

end GlobalTheory.LKMid.MarkEll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixAdjoinTensorUnramifiedToMatrixInjective
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolyTensor

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ)
  (γ : Matrix (Fin n) (Fin n) K) (r : ℕ)

def entries : PolyAlg p K n γ →ₗ[ℚ_[p]] (Fin n × Fin n → K) where
  toFun b ij := val p K n γ b ij.1 ij.2
  map_add' a b := by funext ij; simp [map_add (f := _)]
  map_smul' c b := by funext ij; simp [map_smul]

theorem entries_injective : Function.Injective (entries p K n γ) := by
  intro a b h
  apply Subtype.ext
  exact Matrix.ext fun i j => congrFun h (i, j)

theorem eq_zero_of_proj {ι : Type} [Fintype ι] [DecidableEq ι] (y : (ι → K) ⊗[ℚ_[p]] Qr p r)
    (h : ∀ i, (LinearMap.proj i : (ι → K) →ₗ[ℚ_[p]] K).rTensor (Qr p r) y = 0) : y = 0 := by
  have e : ∀ z : (ι → K) ⊗[ℚ_[p]] Qr p r, ∀ i,
      TensorProduct.piRight ℚ_[p] ℚ_[p] (Qr p r) (fun _ : ι => K) (TensorProduct.comm _ _ _ z) i =
        TensorProduct.comm _ _ _ ((LinearMap.proj i : (ι → K) →ₗ[ℚ_[p]] K).rTensor (Qr p r) z) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero =>
      simp only [(TensorProduct.comm ℚ_[p] (ι → K) (Qr p r)).map_zero,
        (TensorProduct.piRight ℚ_[p] ℚ_[p] (Qr p r) (fun _ : ι => K)).map_zero,
        Pi.zero_apply, map_zero (f := (LinearMap.proj i : (ι → K) →ₗ[ℚ_[p]] K).rTensor (Qr p r)),
        (TensorProduct.comm ℚ_[p] K (Qr p r)).map_zero]
    | tmul a q => simp
    | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
  have h0 : TensorProduct.piRight ℚ_[p] ℚ_[p] (Qr p r) (fun _ : ι => K) (TensorProduct.comm _ _ _ y) = 0 := by
    funext i
    rw [e, h i]
    exact (TensorProduct.comm ℚ_[p] K (Qr p r)).map_zero
  exact (LinearEquiv.map_eq_zero_iff _).1 ((LinearEquiv.map_eq_zero_iff _).1 h0)

theorem phi_apply_entry (x : PolyAlg p K n γ ⊗[ℚ_[p]] Qr p r) (j k : Fin n) :
    phi p K n γ r x j k =
      (LinearMap.proj (j, k) ∘ₗ entries p K n γ).rTensor (Qr p r) x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; rfl
  | tmul b q =>
    rw [phi_tmul, Matrix.algebraMap_eq_diagonal, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Pi.algebraMap_apply, LinearMap.rTensor_tmul, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.coe_proj, Function.eval]
    show (inclK p K r (val p K n γ b j k)) * (inclQ p K r q) = _
    show ((val p K n γ b j k) ⊗ₜ[ℚ_[p]] (1 : Qr p r) : K ⊗[ℚ_[p]] Qr p r) * ((1 : K) ⊗ₜ[ℚ_[p]] q) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  | add a b ha hb => rw [map_add (f := _), Matrix.add_apply, ha, hb, map_add (f := _)]; rfl

theorem phi_injective_any : Function.Injective (phi p K n γ r) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hinj : Function.Injective ((entries p K n γ).rTensor (Qr p r)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (entries_injective p K n γ)
  apply hinj
  rw [map_zero]
  apply eq_zero_of_proj
  intro ij
  rw [← LinearMap.rTensor_comp_apply, ← phi_apply_entry, hx]
  rfl

theorem phi_injective : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n r : ℕ)
    (γ : Matrix (Fin n) (Fin n) K), 0 < r → Function.Injective (GlobalTheory.PolyTensor.phi p K n γ r) :=
  fun p _ K n r γ _ => phi_injective_any p K n γ r

end GlobalTheory.PolyTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixTransvectionDiagonalDecomposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus.VecGerm

theorem gs_map_sum {Y X : Scheme.{0}} (φ : Y ⟶ X) (z : Y) (U : X.Opens) (h : φ z ∈ U) {κ : Type} (t : Finset κ)
    (a b : κ → Γ(X, U)) : gs φ z U (∑ k ∈ t, a k * b k) = ∑ k ∈ t, gs φ z U (a k) * gs φ z U (b k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq φ z U h, map_sum, map_mul]

theorem germ_eq_sum_vecOf : ∀ (Rg : Type) [CommRing Rg] (A₀ X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (M : LB A₀) (Q : GlobalTheory.AbLaw.Perf f M) (s : LB.Sec M) (φ : X ⟶ A₀) (z : X) (i : Q.I), φ z ∈ Q.W i → gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) = ∑ k, gs φ z ⊤ (GlobalTheory.FormsLocus.cstT f (GlobalTheory.FormsLocus.vecOf Q s k)) * gs φ z (Q.W i) (Q.u k i) := by
  intro Rg _ A₀ X f M Q s φ z i hz
  have h := vecOf_spec Q s i
  have hz' : φ z ∈ (𝟙 A₀) ⁻¹ᵁ Q.W i := hz
  have h2 := congrArg (gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i)) h
  rw [gs_map_sum φ z _ hz'] at h2
  have hl : gs φ z ((𝟙 A₀) ⁻¹ᵁ Q.W i) (GlobalTheory.AbLaw.rs A₀ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i))
      ((GlobalTheory.AbLaw.finSecPullId s).f (fun _ => Q.ch i))) = gs φ z (M.U (Q.ch i)) (s.f (Q.ch i)) := by
    unfold GlobalTheory.AbLaw.finSecPullId
    dsimp only
    exact (gs_res φ z _ hz' _).trans (gs_res φ z _ (GlobalTheory.AbLaw.le_pull M (𝟙 A₀) (Q.le i) hz') _)
  rw [hl] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  · show gs φ z _ ((A₀.presheaf.map (homOfLE le_top).op).hom (cstT f (vecOf Q s k))) = _
    exact gs_res φ z le_top hz' _

end GlobalTheory.FormsLocus.VecGerm
end

