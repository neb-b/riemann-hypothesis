module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianQuasiFiniteFinitePart
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.FinPolysIrr

theorem eig_norm_sq_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (y : grp G β) (a : PosV G v β) (hfix : FixL G v β y a.1) (w : InfinitePlace G.F) (μ : ℂ)
    (x : Fin G.n → ℂ) (hx : x ≠ 0) (hμ : G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *ᵥ x = μ • x) :
    ‖μ‖ ^ 2 = ((((y : G.Cˣ × ℚˣ).2 : ℚ)) : ℝ) := by
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G w β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G w β y
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hsig := G.sig w
  refine GlobalTheory.eig_norm_sq_of_similitude G.n (G.gram w) (herm G w β) (toV G w β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm w) Z _ ?_ ?_ hZ hs0 ?_ ?_ μ x hx hμ
  · rcases hsig with h | h <;> omega
  · have := G.n_pos
    rcases hsig with h | h <;> omega
  · rw [Complex.ofReal_ratCast]; exact hsim
  · by_cases hw : w = v
    · subst hw
      obtain ⟨c, hc⟩ := hfix
      exact Or.inr ⟨c, a.1, hc, a.2⟩
    · left
      have h1 : sigPosH (G.gram_herm w) ≠ 1 := by
        intro h1
        have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := ha.le
        have := Fintype.card_le_one_iff.1 hcard ⟨w, h1⟩ ⟨v, hv⟩
        exact hw (congrArg Subtype.val this)
      rcases hsig with h | h
      · exact absurd h.1 h1
      · exact h.1

theorem minpoly_coeff_bdd_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (S : ℝ) : ∃ B : ℝ, ∀ (y : grp G β) (a : PosV G v β),
    FixL G v β y a.1 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S → ∀ (φ : G.F →+* ℂ) (k : ℕ),
    ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  refine ⟨max (√(max S 0)) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y a hfix hS φ k
  set γ : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hγ
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly G.F γ).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le γ
  have hbd : ∀ (w : InfinitePlace G.F) (z : ℂ), (minpoly G.F γ).eval₂ w.embedding z = 0 → ‖z‖ ≤ √(max S 0) := by
    intro w z hz
    obtain ⟨x, hx, hzx⟩ := GlobalTheory.LKCx.PolyArch.roots_eig_any p G w γ z hz
    have h2 := eig_norm_sq_of_a_one p G ha v hv β hβ hR y a hfix w z x hx hzx
    have h3 : ‖z‖ ^ 2 ≤ max S 0 := h2 ▸ le_max_of_le_left hS
    simpa using Real.abs_le_sqrt h3
  have hroots : ∀ z ∈ ((minpoly G.F γ).map φ).roots, ‖z‖ ≤ √(max S 0) := by
    intro z hz
    have hr : (minpoly G.F γ).eval₂ φ z = 0 := by
      have := (Polynomial.mem_roots'.1 hz).2
      rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [← h] at hr; exact hbd _ z hr
    · have hr' : (minpoly G.F γ).eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ z) = 0 := by
        rw [h]
        have := congrArg (starRingEnd ℂ) hr
        rw [map_zero, Polynomial.hom_eval₂] at this
        convert this using 2
      simpa using hbd _ _ hr'
  have := Polynomial.coeff_bdd_of_roots_le φ (minpoly.monic hint) (IsAlgClosed.splits _) hdeg hroots k
  rwa [Polynomial.coeff_map] at this

end GlobalTheory.LKCx.FinPolysIrr

namespace GlobalTheory.LKCx


open GlobalTheory.LKCx.FinPolysIrr in
theorem finite_minpoly_fix_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsym hR
  obtain ⟨D, hD, hDy⟩ := GlobalTheory.T.minpoly_bounded_denominators p G L f hf β x t hx
  obtain ⟨Bp, hBp⟩ := GlobalTheory.T.minpoly_padic_bounded p G K' f' hf' β
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.bounded_denominator_integral_power G.F p Bp
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support p G L f hf K' f' hf' β x t hx
  obtain ⟨B, hB⟩ := minpoly_coeff_bdd_of_a_one p G ha v hv β hsym hR S
  have hpD : 0 < p ^ m₀ * D := Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hD
  refine (GlobalTheory.T.finite_monic_bounded_polynomials G.F (G.n ^ 2) (p ^ m₀ * D) B hpD).subset ?_
  rintro P ⟨y, a, rfl, hfix, hne⟩
  have h1 : f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) ≠ 0 := left_ne_zero_of_mul hne
  have h2 : f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0 := right_ne_zero_of_mul hne
  have hint : IsIntegral G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly.monic hint, ?_, fun k => ⟨?_, fun φ => hB y a.2 hfix (hS y a.1.1 a.1.2 h1 h2) φ k⟩⟩
  · rw [← G.rankC]; exact minpoly.natDegree_le _
  · have := hm₀ _ D (hDy y a.1.1 h1 k) (fun φ => hBp y a.1.2 h2 φ k)
    push_cast
    simpa [mul_assoc] using this

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormDetUnitAndTwist
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.GramTwistNorm

open GlobalTheory.UnitLemma

theorem phi_map (a : ℕ) {R : Type} [CommRing R] (c : R →+* R) :
    (GlobalTheory.Tw.Phi a R).map c = GlobalTheory.Tw.Phi a R := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_mul_self (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) :=
  _root_.UpperTheory.Reformulated.B.Yzd3.phi_mul_self a

theorem phi_mul_transpose (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R)ᵀ = 1 :=
  _root_.UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose a

theorem herm_sum_left {K : UQ} (B : InvAlg K) (β : B.A) {ι : Type} (s : Finset ι) (v : ι → K.E)
    (x : ι → B.A) (z : B.A) :
    B.herm β (∑ i ∈ s, v i • x i) z = ∑ i ∈ s, v i * B.herm β (x i) z := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc,
    map_smul, smul_eq_mul]

theorem herm_sum_right {K : UQ} (B : InvAlg K) (β y : B.A) {ι : Type} (s : Finset ι) (r : ι → K.E)
    (x : ι → B.A) :
    B.herm β y (∑ i ∈ s, r i • x i) = ∑ i ∈ s, K.c (r i) * B.herm β y (x i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [InvAlg.herm, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, RingEquiv.map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem gram_det_ne_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (β : B.Aˣ) {a : ℕ}
    (b : Module.Basis (Fin a) K.E B.A) :
    (Matrix.of fun i j => B.herm β (b i) (b j)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set y := ∑ i, v i • b i with hy
  have hy0 : y ≠ 0 := by
    intro hy'
    apply hv0
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v hy' i
  have hyb : ∀ j, B.herm β y (b j) = 0 := by
    intro j
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [hy, herm_sum_left]
    exact this
  have hyz : ∀ z, B.herm β y z = 0 := by
    intro z
    rw [← b.sum_repr z, herm_sum_right]
    simp [hyb]
  have hβy : (β : B.A) * y = 0 := by
    apply GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hsep
    intro w
    have := hyz (B.σ w)
    simp only [InvAlg.herm, B.σ_σ] at this
    exact this
  exact hy0 ((Units.mul_right_eq_zero β).1 hβy)

theorem gram_map_conj {K : UQ} (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (hec : ∀ x, e (K.c x) = c (e x)) (a : ℕ) (β : B.A)
    (hβ : B.σ β = β * ((-1) ^ (a - 1) * B.g)) (b : Module.Basis (Fin a) K.E B.A) :
    ((Matrix.of fun i j => B.herm β (b i) (b j)).map e).map c =
      ((-1 : L) ^ (a - 1)) • (((Matrix.of fun i j => B.herm β (b i) (b j)).map e)ᵀ *
        (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e) :=
  _root_.GlobalTheory.ScalarSigmaBasis.main B L e c hec a β hβ b

theorem gram_twisted_norm_charpoly : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) → ∀ b : Module.Basis (Fin a) K.E B.A, IsUnit (Matrix.of fun i j => e (B.herm β (b i) (b j))).det ∧ ∀ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) → (δ * thetaGL a c δ).val.charpoly = Q := by
  intro K B L _ e c hec hcc a Q hPQ hQs hQd β hβ b
  set S : Matrix (Fin a) (Fin a) K.E := Matrix.of fun i j => B.herm β (b i) (b j) with hS
  have hG : (Matrix.of fun i j => e (B.herm β (b i) (b j))) = S.map e := rfl
  have hsep : B.P.Separable := by rw [hPQ]; exact hQs.map
  rw [hG]
  refine ⟨?_, ?_⟩
  · have hdet : (S.map e).det = e S.det := by
      rw [show S.map e = (e : K.E →+* L).mapMatrix S from rfl, ← RingHom.map_det]
      rfl
    rw [hdet, isUnit_iff_ne_zero]
    exact (map_ne_zero e).2 (gram_det_ne_zero B hsep β b)
  · intro δ hδ
    set G := S.map e with hGdef
    set P := (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e with hP
    set Φ := GlobalTheory.Tw.Phi a L with hΦ
    have hGc : G.map c = ((-1 : L) ^ (a - 1)) • (Gᵀ * P) := gram_map_conj B L e c hec a β hβ b
    have hinv : (δ⁻¹).val = Φ * Gᵀ := by
      have h1 : (δ.val * Φ)⁻¹ = Gᵀ := by rw [← hδ, Matrix.transpose_transpose]
      have hΦinv : Φ⁻¹ = Φᵀ := Matrix.inv_eq_right_inv (phi_mul_transpose a)
      rw [Matrix.mul_inv_rev, hΦinv, ← Matrix.coe_units_inv] at h1
      calc (δ⁻¹).val = Φ * Φᵀ * (δ⁻¹).val := by rw [hΦ, phi_mul_transpose, Matrix.one_mul]
        _ = Φ * Gᵀ := by rw [Matrix.mul_assoc, h1]
    have hθ : (thetaGL a c δ).val = Φ * ((δ⁻¹).val.map c)ᵀ * Φᵀ := rfl
    have hΦΦ : Φᵀ * Φᵀ = ((-1 : L) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) L) := by
      rw [← Matrix.transpose_mul, hΦ, phi_mul_self, Matrix.transpose_smul, Matrix.transpose_one]
    have hδΦ : δ.val * Φ * Gᵀ = 1 := by rw [Matrix.mul_assoc, ← hinv, Units.mul_inv]
    have key : (δ * thetaGL a c δ).val = P := by
      rw [Units.val_mul, hθ, hinv, Matrix.map_mul, hΦ, phi_map, ← hΦ, Matrix.transpose_mul,
        Matrix.transpose_map, Matrix.transpose_transpose, hGc]
      calc δ.val * (Φ * ((-1 : L) ^ (a - 1) • (Gᵀ * P) * Φᵀ) * Φᵀ)
          = ((-1 : L) ^ (a - 1)) • ((δ.val * Φ * Gᵀ) * P * (Φᵀ * Φᵀ)) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = P := by
            rw [hδΦ, hΦΦ, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow,
              neg_one_mul, neg_neg, one_pow, one_smul]
    rw [key, hP, show (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e =
      (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map (e : K.E →+* L) from rfl,
      Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    change B.P.map (e : K.E →+* L) = Q
    rw [hPQ, Polynomial.map_map]
    have : (e : K.E →+* L).comp e.symm.toRingHom = RingHom.id L := by
      ext x; simp
    rw [this, Polynomial.map_id]

end GlobalTheory.GramTwistNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKernelSignEqEtaGramDet
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat

open GlobalTheory.UnitLemma

theorem model_aeval_mulVec {K : UQ} {L : Type} [Field L] (e : K.E ≃+* L) {B : InvAlg K} {n : ℕ}
    (ψ : B.A ≃+ (Fin n → L)) (hs : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (u : B.A)
    (g : Matrix (Fin n) (Fin n) L) (hu : ∀ y, ψ (u * y) = g *ᵥ ψ y) (p : K.E[X]) (y : B.A) :
    ψ (aeval u p * y) = aeval g (p.map (e : K.E →+* L)) *ᵥ ψ y := by
  induction p using Polynomial.induction_on generalizing y with
  | C a =>
    rw [aeval_C, ← Algebra.smul_def, hs, Polynomial.map_C, aeval_C, Algebra.algebraMap_eq_smul_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  | add p q hp hq =>
    rw [map_add (f := _), add_mul, map_add (f := _), hp, hq, Polynomial.map_add (f := _), map_add (f := _), Matrix.add_mulVec]
  | monomial k a h =>
    have h1 : aeval u (C a * X ^ (k + 1)) = aeval u (C a * X ^ k) * u := by
      rw [pow_succ, ← mul_assoc, Polynomial.aeval_mul, aeval_X]
    have h2 : aeval g ((C a * X ^ (k + 1)).map (e : K.E →+* L)) = aeval g ((C a * X ^ k).map (e : K.E →+* L)) * g := by
      rw [pow_succ, ← mul_assoc, Polynomial.map_mul, Polynomial.map_X, Polynomial.aeval_mul, aeval_X]
    rw [h1, h2, mul_assoc, h, hu, Matrix.mulVec_mulVec]

theorem prod_herm_fst {K : UQ} (B₁ B₂ : InvAlg K) (x : (B₁.prod B₂).A) (y z : B₁.A) :
    (B₁.prod B₂).herm x ((y, 0) : B₁.A × B₂.A) ((z, 0) : B₁.A × B₂.A) = B₁.herm x.1 y z := by
  unfold InvAlg.herm
  have hel : x * (show (B₁.prod B₂).A from (y, 0)) * (B₁.prod B₂).σ (show (B₁.prod B₂).A from (z, 0)) =
      (show (B₁.prod B₂).A from (x.1 * y * B₁.σ z, 0)) := by
    refine Prod.ext rfl ?_
    show x.2 * 0 * B₂.σ 0 = 0
    simp
  rw [hel]
  exact (Algebra.trace_prod_apply (R := K.E) ((x.1 * y * B₁.σ z, 0) : B₁.A × B₂.A)).trans (by simp)

theorem neg_one_zpow_val_norm_mul (K : UQ) (d g : K.E) (hd : d ≠ 0) :
    (-1 : ℂ) ^ val K.O (d * g * K.c d) = ((K.eta g : ℚ) : ℂ) := by
  unfold UQ.eta
  by_cases hg : g = 0
  · subst hg; simp
  have hval : ∀ a b : K.E, a ≠ 0 → b ≠ 0 → val K.O (a * b) = val K.O a + val K.O b := by
    intro a b ha hb
    unfold val
    rw [Valuation.map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
    ring
  have hcd : K.c d ≠ 0 := by simpa using hd
  rw [hval _ _ (mul_ne_zero hd hg) hcd, hval _ _ hd hg, UnramNorm.val_c]
  have h2 : (-1 : ℂ) ^ (val K.O d + val K.O g + val K.O d) = (-1 : ℂ) ^ val K.O g := by
    rw [show val K.O d + val K.O g + val K.O d = 2 * val K.O d + val K.O g by ring,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul]
    norm_num
  rw [h2]
  push_cast
  rfl

end GlobalTheory.KapLat

namespace GlobalTheory.KapLat

open GlobalTheory.UnitLemma

theorem kapSign_eq_eta_gramDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K) (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ → ∀ (x : (B₁.prod B₂).A) (γ : GLw n w), IsModel w e (B₁.prod B₂) ((u₁, u₂) : B₁.A × B₂.A) x γ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet x.1) : ℚ) : ℂ) := by
  intro E _ _ _ w hns K e hB n Q₁ Q₂ B₁ B₂ u₁ u₂ hsep hF₁ hF₂ x γ hM
  obtain ⟨ψ, hs, hu, hh⟩ := hM
  obtain ⟨-, -, hval, -⟩ := hB
  set P₁ : K.E[X] := Q₁.map e.symm.toRingHom with hP₁
  have hQ₁ : Q₁ = P₁.map (e : K.E →+* w.adicCompletion E) := by
    rw [hP₁, Polynomial.map_map]
    ext i
    simp
  have hunit : IsUnit (aeval u₂ P₁) := by
    obtain ⟨a, b, hab⟩ := hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
    have h := congrArg (aeval u₂) hab
    simp only [Polynomial.coe_mapRingHom, map_add (f := _), map_mul, map_one] at h
    rw [hF₂.2.1, mul_zero, add_zero] at h
    exact ⟨⟨aeval u₂ P₁, aeval u₂ a, by rw [mul_comm]; exact h, h⟩, rfl⟩
  have hker : ∀ y : (B₁.prod B₂).A, aeval γ.val Q₁ *ᵥ ψ y = 0 ↔ y.2 = 0 := by
    intro y
    rw [hQ₁, ← model_aeval_mulVec e ψ hs _ γ.val hu P₁ y, AddEquiv.map_eq_zero_iff]
    have hp1 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).1 = aeval u₁ P₁ :=
      (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) P₁).symm
    have hp2 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).2 = aeval u₂ P₁ :=
      (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) P₁).symm
    have h1 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁ * y).2 = aeval u₂ P₁ * y.2 := by
      rw [← hp2]; rfl
    have h0 : (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁ * y).1 = 0 := by
      show (aeval (show (B₁.prod B₂).A from (u₁, u₂)) P₁).1 * y.1 = 0
      rw [hp1, hF₁.2.1, zero_mul]
    constructor
    · intro h
      have h2 := congrArg Prod.snd h
      rw [h1] at h2
      exact hunit.mul_right_eq_zero.mp h2
    · intro h
      exact Prod.ext h0 (by rw [h1, h, mul_zero]; rfl)
  unfold kapSign
  rw [if_neg hns]
  dsimp only
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val Q₁)) with hV₁
  set m := Module.finrank (w.adicCompletion E) V₁ with hm
  set v := Module.finBasis (w.adicCompletion E) V₁ with hv
  have hmem : ∀ y : (B₁.prod B₂).A, ψ y ∈ V₁ ↔ y.2 = 0 := fun y => by
    rw [hV₁, LinearMap.mem_ker, Matrix.toLin'_apply, hker]
  let ψ₁ : B₁.A →+ (Fin n → w.adicCompletion E) :=
    AddMonoidHom.mk' (fun z => ψ (show (B₁.prod B₂).A from (z, 0))) (fun z z' => by
      rw [← map_add (f := _)]
      congr 1
      exact Prod.ext rfl (show (0 : B₂.A) = 0 + 0 by simp))
  have hψ₁ : ∀ z, ψ₁ z = ψ (show (B₁.prod B₂).A from (z, 0)) := fun z => rfl
  have hψ₁s : ∀ (c : K.E) z, ψ₁ (c • z) = e c • ψ₁ z := by
    intro c z
    rw [hψ₁, hψ₁, ← hs]
    congr 1
    exact Prod.ext rfl (show (0 : B₂.A) = c • 0 by simp)
  have hψ₁i : Function.Injective ψ₁ := by
    intro z z' hzz
    rw [hψ₁, hψ₁] at hzz
    exact congrArg Prod.fst (ψ.injective hzz)
  let a' : Fin m → B₁.A := fun i => (ψ.symm (v i : Fin n → w.adicCompletion E)).1
  have hva : ∀ i, ψ₁ (a' i) = v i := by
    intro i
    have h2 : (ψ.symm (v i : Fin n → w.adicCompletion E)).2 = 0 :=
      (hmem _).1 (by rw [ψ.apply_symm_apply]; exact (v i).2)
    have h3 : (show (B₁.prod B₂).A from (a' i, 0)) = ψ.symm (v i) := Prod.ext rfl h2.symm
    rw [hψ₁, h3, ψ.apply_symm_apply]
  have hsum : ∀ g : Fin m → K.E, ψ₁ (∑ i, g i • a' i) = ∑ i, e (g i) • (v i : Fin n → w.adicCompletion E) := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hψ₁s, hva]
  have hli : LinearIndependent K.E a' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : ∑ j, e (g j) • v j = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← hsum g, hg, map_zero]
      rfl
    have := Fintype.linearIndependent_iff.mp v.linearIndependent _ h0 i
    simpa using this
  have hsp : ⊤ ≤ Submodule.span K.E (Set.range a') := by
    intro z _
    have hz : ψ₁ z ∈ V₁ := (hmem _).2 rfl
    have hrep := congrArg Subtype.val (v.sum_repr ⟨ψ₁ z, hz⟩)
    rw [Submodule.coe_sum] at hrep
    simp only [Submodule.coe_smul] at hrep
    have hz' : z = ∑ i, e.symm (v.repr ⟨ψ₁ z, hz⟩ i) • a' i := by
      apply hψ₁i
      rw [hsum]
      simp only [RingEquiv.apply_symm_apply]
      exact hrep.symm
    rw [hz']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let hb : Module.Basis (Fin m) K.E B₁.A := Module.Basis.mk hli hsp
  have hbapp : ⇑hb = a' := funext fun i => Module.Basis.mk_apply hli hsp i
  have hdm : Module.finrank K.E B₁.A = m := by
    rw [Module.finrank_eq_card_basis hb, Fintype.card_fin]
  let bm := (Module.finBasis K.E B₁.A).reindex (finCongr hdm)
  have hgram : B₁.gramDet x.1 = (Matrix.of fun i j => B₁.herm x.1 (bm i) (bm j)).det := by
    unfold InvAlg.gramDet
    rw [← Matrix.det_reindex_self (finCongr hdm)]
    congr 1
    ext i j
    simp [bm, Module.Basis.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  have hdetM : IsUnit (bm.toMatrix a').det := by
    have h := bm.isUnit_det hb
    rwa [Module.Basis.det_apply, hbapp] at h
  have hGa := GlobalTheory.GramChange.gram_of_sum K B₁ K.E (RingEquiv.refl K.E) (K.c : K.E →+* K.E) (fun _ => rfl) x.1 bm a'
    (bm.toMatrix a') (fun j => (bm.sum_toMatrix_smul_self a' j).symm)
  have e1 : (bm.toMatrix a').map (RingEquiv.refl K.E) = bm.toMatrix a' := Matrix.ext fun _ _ => rfl
  rw [e1] at hGa
  have e2 : ((bm.toMatrix a').map (K.c : K.E →+* K.E)).det = K.c (bm.toMatrix a').det :=
    (RingHom.map_det (K.c : K.E →+* K.E) (bm.toMatrix a')).symm
  have hdetG : (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det =
      (bm.toMatrix a').det * B₁.gramDet x.1 * K.c (bm.toMatrix a').det := by
    calc (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det
        = (Matrix.of fun i j => (RingEquiv.refl K.E) (B₁.herm x.1 (a' i) (a' j))).det := rfl
      _ = ((bm.toMatrix a')ᵀ * (Matrix.of fun i j => (RingEquiv.refl K.E) (B₁.herm x.1 (bm i) (bm j))) *
            (bm.toMatrix a').map (K.c : K.E →+* K.E)).det := by rw [hGa]
      _ = _ := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e2, hgram]
        rfl
  have hK : (Matrix.of fun i j => ∑ k, cj w ((v i : Fin n → w.adicCompletion E) k) * (v j : Fin n → w.adicCompletion E) k) =
      (Matrix.of fun i j => e (B₁.herm x.1 (a' i) (a' j)))ᵀ := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    calc _ = stdH w (ψ₁ (a' j)) (ψ₁ (a' i)) := by
          rw [hva, hva]
          unfold stdH
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = e ((B₁.prod B₂).herm x (show (B₁.prod B₂).A from (a' j, 0)) (show (B₁.prod B₂).A from (a' i, 0))) :=
          hh _ _
      _ = e (B₁.herm x.1 (a' j) (a' i)) := congrArg e (prod_herm_fst B₁ B₂ x _ _)
  have hdetE : (Matrix.of fun i j => e (B₁.herm x.1 (a' i) (a' j))).det =
      e (Matrix.of fun i j => B₁.herm x.1 (a' i) (a' j)).det := by
    exact (RingHom.map_det (e : K.E →+* w.adicCompletion E) _).symm
  rw [hK, Matrix.det_transpose, hdetE, ← hval, hdetG]
  exact neg_one_zpow_val_norm_mul K _ _ hdetM.ne_zero

end GlobalTheory.KapLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterPolyEqZeroOfIsHomogeneousNeDim
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.ProjVar.Var

theorem interPoly_eq_zero_of_isHomogeneous (F : Type) [Field F] (Y : Var F) (κ : Type) (gr : κ → Y.Dv) (k : ℕ)
    (P : MvPolynomial κ ℝ) (hP : P.IsHomogeneous k) (hk : k ≠ Y.dim) : Y.interPoly gr P = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw : Finsupp.weight 1 d = k := hP (mem_support_iff.mp hd)
  have e : monomial d (AddMonoidAlgebra.coeff P d) = AddMonoidAlgebra.coeff P d • basisMonomials κ ℝ d := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, interPoly, Module.Basis.constr_basis, dite_eq_right, smul_zero]
  rintro ⟨s, hs⟩
  apply hk
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hw, ← hs, map_sum]
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

end GlobalTheory.ProjVar.Var
end

