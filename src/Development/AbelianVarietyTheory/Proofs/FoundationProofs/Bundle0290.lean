module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhase
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSelfDualPairGaloisConjugateHomLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackSecondGroupRationalPointEqDetSmul
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatEqui.Col

variable (D : D7) {N N' : ℕ}

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  have h : ∀ y : D.host.E, D.host.φ₀ (D.host.conj y) = (starRingEnd ℂ) (D.host.φ₀ y) := fun y =>
    D.host.conjE_apply D.host.φ₀ y
  apply (D.host.φ₀ : D.host.E →+* ℂ).injective
  change D.host.φ₀ _ = D.host.φ₀ _
  rw [h, h, Complex.conj_conj]

theorem adj_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (adj D M) = M := by
  ext i j; simp [adj, conj_conj]

theorem adj_one_sub {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (1 - M) = 1 - adj D M := by
  ext i j
  by_cases h : i = j
  · subst h; simp [adj]
  · simp [adj, Matrix.one_apply, h, Ne.symm h]

theorem det_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : (adj D M).det = D.host.conj M.det := by
  unfold adj
  rw [Matrix.det_transpose]
  exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm

theorem adj_diagonal {n : ℕ} (d : Fin n → D.host.E) :
    adj D (Matrix.diagonal d) = Matrix.diagonal fun i => D.host.conj (d i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [adj]
  · simp [adj, Matrix.diagonal_apply, h, Ne.symm h]

theorem sd_of_moves {g : GA D N} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

theorem moves_one (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D N
  rw [← h2]; exact (h1 _).1

theorem isRat_one (N : ℕ) : IsRat D ((1 : GA D N) : GL (Fin N) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

def halfP (N : ℕ) : Matrix (Fin N) (Fin N) D.host.E := Matrix.diagonal fun i => if i < i.rev then 1 else 0

def revS (N : ℕ) : Matrix (Fin N) (Fin N) D.host.E := Matrix.of fun i j => if i = j.rev then 1 else 0

theorem halfP_mul : halfP D N * halfP D N = halfP D N := by
  unfold halfP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem adj_halfP : adj D (halfP D N) = halfP D N := by
  unfold halfP
  rw [adj_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem revS_mul : revS D N * revS D N = 1 := by
  ext i j
  simp only [revS, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem adj_revS : adj D (revS D N) = revS D N := by
  ext i j
  simp only [adj, revS, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  by_cases h : i = j.rev
  · subst h; simp
  · have h' : ¬ j = i.rev := fun e => h (by rw [e, Fin.rev_rev])
    simp [h, h']

theorem halfP_revS (hN : Even N) : halfP D N * revS D N = revS D N - revS D N * halfP D N := by
  ext i j
  simp only [halfP, revS, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.of_apply]
  by_cases h : i = j.rev
  · subst h
    obtain ⟨k, hk⟩ := hN
    have hj := j.2
    simp only [Fin.rev_rev, if_true, Fin.lt_def, Fin.val_rev]
    split_ifs with h1 h2 h2
    · omega
    · simp
    · simp
    · omega
  · simp [h]

theorem int_ite (p : Prop) [Decidable p] {a : D.host.E} (ha : IsIntegral ℤ a) :
    IsIntegral ℤ (if p then a else 0) := by
  split_ifs
  · exact ha
  · exact isIntegral_zero

theorem mulV_scalar_right (M : ℕ) (b : D.host.E) (x : VC D N N') :
    mulV D 1 (Matrix.diagonal fun _ => -1 + (M : D.host.E) * b) x =
      -x + (M : ℂ) • mulV D 1 (Matrix.diagonal fun _ => b) x := by
  funext τ i j
  change mulV D 1 _ x τ i j = -(x τ i j) + (M : ℂ) * (mulV D 1 _ x τ i j)
  rw [mulV_apply, mulV_apply]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul,
    Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal, Matrix.mul_diagonal]
  simp
  ring

theorem hf_neg_add_smul (T : Tor D) (c : ℂ) (x z y : VC D N N') :
    Hf D T (-x + c • z) y = -Hf D T x y + c * Hf D T z y := by
  simp only [Hf, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, add_mul, neg_mul, mul_assoc,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

theorem Hf_mulV' (T : Tor D) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z w : VC D N N') : Hf D T z (mulV D M' M w) = Hf D T (mulV D (adj D M') (adj D M) z) w := by
  rw [Hf_mulV, adj_adj, adj_adj]

theorem norm_div_prod {ι : Type} [Fintype ι] (w g : ι → ℂ) (k : ℕ) (hw : ∀ i, w i ≠ 0)
    (h : ∀ i, (starRingEnd ℂ) (w i) = g i * w i) :
    ((‖∏ i, w i ^ (k + k)‖ : ℝ) : ℂ) / ∏ i, w i ^ (k + k) = ∏ i, g i ^ k := by
  rw [norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : ((‖w i‖ : ℝ) : ℂ) ^ 2 = g i * w i ^ 2 := by
    rw [← Complex.mul_conj', h]; ring
  rw [norm_pow, Complex.ofReal_pow, ← two_mul, pow_mul, pow_mul, h1, mul_pow,
    mul_div_cancel_right₀ _ (pow_ne_zero _ (pow_ne_zero _ (hw i)))]

end GlobalTheory.RatEqui.Col


open GlobalTheory.RatEqui.Col in
theorem GlobalTheory.RatEqui.pull_right_eq_det_smul : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA' : GA D N') (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA' : GL (Fin N') (AE D)) γ' → (1 - γ').det ≠ 0 → Moves D (γA' : GL (Fin N') (AE D)) L₁' → pull D (tor0 D cc δ) 1 γ' th = (∏ τ, embT D τ γ'.det ^ (N / 2)) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) (stdL D N) L₁') th := by
  intro D cc δ hc N N' hN hN' th hth γA γ L₁ hrat hdet hmov
  have h1 : γ * adj D γ = 1 := (mem_ratG_intG D N').2.2.2.1 γA γ hrat
  have h2 : adj D γ * γ = 1 := mul_eq_one_comm.1 h1
  obtain ⟨st1, st2, st3⟩ := _root_.GlobalTheory.ThetaStab.mulV_theta_lattices D cc δ hc N N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, sd_of_moves D (moves_one D N), sd_of_moves D (moves_one D N'), rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) L₁) :=
    Or.inr ⟨_, _, sd_of_moves D (moves_one D N), sd_of_moves D hmov, rfl⟩
  let u : VC D N N' ≃ₗ[ℂ] VC D N N' := LinearEquiv.ofLinear (mulV D γ 1) (mulV D (adj D γ) 1)
    (LinearMap.ext fun x => by simp [mulV_mulV, h1, mulV_one])
    (LinearMap.ext fun x => by simp [mulV_mulV, h2, mulV_one])
  have hu : ∀ x, u x = mulV D γ 1 x := fun x => rfl
  have hu' : ∀ x, u.symm x = mulV D (adj D γ) 1 x := fun x => rfl
  have hsub : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D (1 - adj D γ) 1 :=
    LinearMap.ext fun x => by
      rw [mulV_sub_left, mulV_one]; rfl
  have hd : (1 - adj D γ).det = D.host.conj (1 - γ).det := by rw [← adj_one_sub, det_adj]
  have hd0 : (1 - adj D γ).det ≠ 0 := by
    rw [hd]; exact (map_ne_zero _).2 hdet
  have hdV : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) =
      ∏ τ, embT D τ (1 - adj D γ).det ^ N := by
    rw [hsub, _root_.GlobalTheory.TwoSidedDet.det_mulV]; simp
  have hw : ∀ τ, embT D τ (1 - adj D γ).det ≠ 0 := fun τ => (map_ne_zero _).2 hd0
  have i1 : ∀ i j, IsIntegral ℤ ((1 : Matrix (Fin N') (Fin N') D.host.E) i j) := fun i j => by
    rw [Matrix.one_apply]; exact int_ite D _ isIntegral_one
  have comm : ∀ (M : Matrix (Fin N) (Fin N) D.host.E) x, mulV D 1 M (u x) = u (mulV D 1 M x) := fun M x => by
    simp [hu, mulV_mulV]
  have key := _root_.GlobalTheory.SymConst.const_of_symm D cc δ hc N N' _ _ k0 k1 u
    (fun z w => by rw [hu, hu, Hf_mulV, mulV_mulV, h2, adj_one, mul_one, mulV_one])
    (fun x => by
      rw [st3 1 γA 1 γ _ _ (isRat_one D N) hrat (moves_one D N) hmov x, adj_one, hu])
    (by rw [hdV]; exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hw τ))
    (by
      obtain ⟨m, hm, hm'⟩ := st2 (1 - adj D γ)⁻¹ 1
      have e : ∀ x : VC D N N', m • x = m • mulV D (1 - adj D γ)⁻¹ 1 x - u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) := by
        intro x
        have := LinearMap.congr_fun hsub (m • mulV D (1 - adj D γ)⁻¹ 1 x)
        rw [map_nsmul (mulV D (1 - adj D γ) 1), mulV_mulV, Matrix.mul_nonsing_inv _ (Ne.isUnit hd0), mul_one,
          mulV_one] at this
        exact this.symm
      refine ⟨m, hm, fun x hx => ⟨_, hm' x hx, ?_, e x⟩⟩
      have : u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) = m • mulV D (1 - adj D γ)⁻¹ 1 x - m • x := by
        rw [e x]; abel
      rw [this]
      exact sub_mem (hm' x hx) (nsmul_mem hx m))
    (mulV D 1 (halfP D N)) (mulV D 1 (revS D N))
    (fun x hx => ⟨st1 _ _ i1 (fun i j => by
        rw [halfP, Matrix.diagonal_apply]; exact int_ite D _ (int_ite D _ isIntegral_one)) x hx,
      st1 _ _ i1 (fun i j => int_ite D _ isIntegral_one) x hx⟩)
    (fun x => by rw [mulV_mulV, halfP_mul, mul_one])
    (fun x y => by rw [Hf_mulV, adj_one, adj_halfP])
    (fun x => by rw [mulV_mulV, revS_mul, mul_one, mulV_one])
    (fun x y => by rw [Hf_mulV, adj_one, adj_revS, mulV_mulV, revS_mul, mul_one, mulV_one])
    (fun x => by rw [mulV_mulV, mulV_mulV, mul_one, halfP_revS D hN, mulV_sub_right])
    (comm _) (comm _)
    (fun M hM => by
      obtain ⟨l, b, hl⟩ := GlobalTheory.NegOneNorm.exists_norm_eq_neg_one D M hM
      have hb : D.host.conj (b : D.host.E) = b := by
        have h3 := congrArg D.host.conj hl
        rw [map_mul, conj_conj, mul_comm, hl, map_add (f := _), map_neg, map_one, map_mul, map_natCast] at h3
        exact (mul_left_cancel₀ (Nat.cast_ne_zero.2 hM.ne') (add_left_cancel h3)).symm
      have idg : ∀ a : 𝓞 D.host.E, ∀ i j : Fin N,
          IsIntegral ℤ (Matrix.diagonal (fun _ => (a : D.host.E)) i j) := fun a i j => by
        rw [Matrix.diagonal_apply]; exact int_ite D _ a.2
      refine ⟨mulV D 1 (Matrix.diagonal fun _ => (l : D.host.E)), mulV D 1 (Matrix.diagonal fun _ => (b : D.host.E)),
        fun x hx => ⟨st1 _ _ i1 (idg l) x hx, st1 _ _ i1 (idg b) x hx⟩, comm _, comm _, fun x => ?_,
        fun x y => ?_, fun x y => ?_⟩
      · simp only [mulV_mulV, halfP, Matrix.diagonal_mul_diagonal, mul_comm]
      · rw [Hf_mulV, adj_one, adj_diagonal, hb]
      · rw [Hf_mulV', adj_one, adj_diagonal, mulV_mulV, mul_one, Matrix.diagonal_mul_diagonal, hl,
          mulV_scalar_right, hf_neg_add_smul])
    th hth
  rw [pull_eq]
  refine key.trans ?_
  congr 1
  obtain ⟨k, hk⟩ := hN
  have hk2 : N / 2 = k := by omega
  rw [hdV, hk2]
  have hconj : ∀ τ, (starRingEnd ℂ) (embT D τ (1 - adj D γ).det) =
      embT D τ γ.det * embT D τ (1 - adj D γ).det := fun τ => by
    rw [← embT_conj, ← map_mul, ← Matrix.det_mul, mul_sub, h1, mul_one, hd, conj_conj, ← neg_sub γ 1,
      Matrix.det_neg, Fintype.card_fin, hN'.neg_one_pow, one_mul]
  have := norm_div_prod _ _ k hw hconj
  rwa [← hk] at this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ConjNorm

noncomputable def torTw (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : Tor D :=
  ⟨fun τ x => embT D τ (σ x), lamOf D cc δ⟩

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf]

theorem norm_core (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E)
    (hσ : ∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hL : SD D L) (hL' : SD D L')
    (G : VC D N N' → ℂ) (hG : ThetaVectorUpToUnits D (torTw D σ cc δ) t0 L L' G) :
    G ∈ Th D (torTw D σ cc δ) L L' ∧ ∀ x, normSq D (torTw D σ cc δ) (La D (torTw D σ cc δ) L L')
      (U D (torTw D σ cc δ) x G) = nrm1Sq (lamOf D cc δ) (GL3Theta.th0 (lamOf D cc δ) t0) ^ (fF D * N * N') := by
  have g1 := (_root_.GlobalTheory.InducedType.induced_type D).1
  obtain ⟨b, κ, hb, ⟨hκQ, hκ⟩, rfl⟩ := hG
  have hκ1 : ‖κ‖ = 1 := hκ (algebraMap Qbar ℂ)
  obtain ⟨L₁, L₁', h₁, h₁', hY⟩ := _root_.GlobalTheory.GaloisTwist.exists_conjugate_pair D σ hσ N N' L L' hL hL'
  have hb' := _root_.GlobalTheory.NormSum.onB_map_aut D σ hσ N N' _ b hb
  have eLa : La D (torTw D σ cc δ) L L' = La D (tor0 D cc δ) L₁ L₁' := by
    unfold La
    congr 1
    ext z
    constructor
    · rintro ⟨w, hw, A, hA, rfl⟩
      exact ⟨w, hw, A.map σ, (hY A).1 hA, rfl⟩
    · rintro ⟨w, hw, A, hA, rfl⟩
      have e : (A.map σ.symm).map σ = A := by ext i j; simp
      refine ⟨w, hw, A.map σ.symm, (hY _).2 (by rw [e]; exact hA), ?_⟩
      congr 1
      funext τ i j
      simp [embV, tor0, torTw]
  obtain ⟨hd, hinv⟩ := _root_.GlobalTheory.HalfPeriodTheta.theta_signed_translation D g1 cc δ hc t0 ht
  obtain ⟨o1, o2⟩ := _root_.GlobalTheory.OrthoCoord.orthonormal_coord D g1 cc δ N N' _ _ hb'
  have hth := _root_.GlobalTheory.OrthoProdTheta.pullB_mem_ThSp D (tor0 D cc δ) N N' _ _ o1 _ hd hinv
  have hn := _root_.GlobalTheory.PullNorm.normSq_pullB D (tor0 D cc δ) N N' _ _ (_root_.GlobalTheory.CurveLattice.lattice_of_curve D g1 cc δ hc).1 o1 o2 _ hd.continuous (by
    intro ω hω z
    obtain ⟨m, -, hm⟩ := hinv ω hω
    have := congrArg norm (hm z)
    rwa [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul] at this)
  have kB : KLat D (tor0 D cc δ) (LaB D (tor0 D cc δ) (fun j => (b j).map σ)) := Or.inl ⟨_, _, hb', rfl⟩
  have kL : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') := Or.inr ⟨_, _, h₁, h₁', rfl⟩
  obtain ⟨-, u2, u3, -⟩ := GlobalTheory.ConjNorm.unitary_all D cc δ hc N N' _ _ kB kL _ hth
  have u4 := (GlobalTheory.ConjNorm.unitary_all D cc δ hc N N' _ _ kL kL _ u2).1
  unfold Th
  rw [eLa]
  set F := Iop D (tor0 D cc δ) (LaB D (tor0 D cc δ) (fun j => (b j).map σ)) (La D (tor0 D cc δ) L₁ L₁')
    (pullB D (tor0 D cc δ) (fun j => (b j).map σ) (GL3Theta.th0 (lamOf D cc δ) t0)) with hF
  change (fun z => κ * F z) ∈ ThSp D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') ∧
    ∀ x, normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (U D (tor0 D cc δ) x (fun z => κ * F z)) = _
  refine ⟨⟨u2.1.const_mul κ, fun x hx z => ?_⟩, fun x => ?_⟩
  · have := u2.2 x hx z
    simp only [U] at this ⊢
    linear_combination κ * this
  · refine Eq.trans ?_ hn
    rw [← u3, ← u4 x]
    unfold normSq
    simp only [U, norm_mul, hκ1, one_mul]

theorem exists_aut (D : D7) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hK : FixK D M ρ)
    (hM : ∀ τ x, embT D τ x ∈ M) :
    ∃ σ : D.host.E ≃ₐ[ℚ] D.host.E, (∀ a : D.host.K, σ (a : D.host.E) = (a : D.host.E)) ∧
      ∀ τ x, cj M ρ (embT D τ x) = embT D τ (σ x) := by
  obtain ⟨⟨hPsi, -⟩, hperm⟩ := _root_.GlobalTheory.InducedType.induced_type D
  obtain ⟨π, hπ⟩ := hperm M ρ hK hM
  rcases isEmpty_or_nonempty D.what₂.Tau with h | ⟨⟨τ₀⟩⟩
  · exact ⟨AlgEquiv.refl, fun _ => rfl, fun τ => h.elim τ⟩
  have hmul : ∀ g h : D.R.GG, D.host.sigmaOf (g * h) = D.host.sigmaOf g * D.host.sigmaOf h :=
    fun g h => map_mul _ g h
  have hone : D.host.sigmaOf 1 = 1 := map_one _
  have key : ∀ (τ : D.what₂.Tau) (g : D.R.GG) (x : D.host.E),
      embT D τ (D.host.sigmaOf g x) = D.host.φ₀ (D.host.sigmaOf ((D.eTau τ : D.R.GG) * g) x) := by
    intro τ g x
    rw [hmul]; rfl
  have key1 : ∀ (τ : D.what₂.Tau) (x : D.host.E),
      embT D τ x = D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) x) := fun _ _ => rfl
  have main : ∀ τ x, cj M ρ (embT D τ x) = embT D τ (D.host.sigmaOf
      ((D.eTau τ₀ : D.R.GG)⁻¹ * (D.eTau (π τ₀) : D.R.GG)) x) := by
    intro τ x
    have e1 : embT D τ x = embT D τ₀ (D.host.sigmaOf
        ((D.eTau τ₀ : D.R.GG)⁻¹ * (D.eTau τ : D.R.GG)) x) := by
      rw [key, mul_inv_cancel_left, key1]
    rw [e1, hπ, key, key]
    congr 3
    rw [mul_left_comm, mul_comm (D.eTau (π τ₀) : D.R.GG), mul_left_comm]
  refine ⟨_, fun a => ?_, main⟩
  apply (embT D τ₀).injective
  rw [← main, hPsi, (hK a).2]

theorem exists_ext (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ (M' : IntermediateField ℚ ℂ) (ρ' : M' →ₐ[ℚ] ℂ), M ≤ M' ∧ Qbar ≤ M' ∧
      ∀ x ∈ M, ρ' (TaylorLogMetric.liftM M' x) = ρ (TaylorLogMetric.liftM M x) := by
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := ℚ) (L := M) (M := ℂ) (E := algebraicClosure M ℂ) ρ
  have hle : M ≤ (algebraicClosure M ℂ).restrictScalars ℚ := fun x hx =>
    (algebraicClosure M ℂ).algebraMap_mem ⟨x, hx⟩
  refine ⟨(algebraicClosure M ℂ).restrictScalars ℚ, φ, hle, fun x hx => ?_, fun x hx => ?_⟩
  · rw [IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]
    exact (mem_algebraicClosure_iff.1 hx).extendScalars (algebraMap ℚ M).injective
  · rw [← hφ]
    simp only [TaylorLogMetric.liftM, dif_pos hx, dif_pos (hle hx)]
    rfl

theorem norm_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hL : SD D L) (hL' : SD D L') (hN : Even (N * N'))
    (G : VC D N N' → ℂ) (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hK : FixK D M ρ) (hQ : Qbar ≤ M)
    (hD : DataIn D (tor0 D cc δ) M) (hC : CoefIn D G M)
    (t0' : ℂ) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0')
    (x : VC D N N') (hx : LaQ D (tor0 D cc δ) L L' x) (hCx : CoefIn D (U D (tor0 D cc δ) x G) M) :
    (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamConj M ρ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂}) ∧
    ∃ x', fnConj D M ρ (U D (tor0 D cc δ) x G) = U D (torConj D (tor0 D cc δ) M ρ) x' (fnConj D M ρ G) ∧
      normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
          (U D (torConj D (tor0 D cc δ) M ρ) x' (fnConj D M ρ G)) =
        nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') := by
  have g1 := (_root_.GlobalTheory.InducedType.induced_type D).1
  obtain ⟨cc', δ', hc', -, hlam⟩ := _root_.GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M ρ hK hD.2.1 hD.2.2 1 one_pos
  obtain ⟨σ, hσ, hσ'⟩ := exists_aut D M ρ hK hD.1
  have hT : torConj D (tor0 D cc δ) M ρ = torTw D σ cc' δ' := by
    unfold torConj torTw
    congr 1
    funext τ y
    exact hσ' τ y
  have hGTh : G ∈ Th D (tor0 D cc δ) L L' :=
    (norm_core D AlgEquiv.refl (fun _ => rfl) cc δ hc t0 ht L L' hL hL' G hG).1
  have hE := (_root_.GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht N N' L L' hL hL' hN G hG M ρ hD hC).2.1 t0' ht'
  obtain ⟨m, hm, hmx⟩ := hx
  have htors := ((_root_.GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D g1).2 cc δ hc).2
  obtain ⟨x', hx', -⟩ := _root_.GlobalTheory.GalExist.galEx_all D cc δ hc M ρ hK hD
    (fun t h1 h2 => ⟨hQ (htors t h1 h2).1, hQ (htors t h1 h2).2⟩) N N' L L' hL hL' x (2 * m) ⟨m, hm, hmx⟩ (by omega)
  have hcomb : comb D (tor0 D cc δ) (fun _ : Fin 1 => (1 : ℂ)) (fun _ => 0) G = G := by
    funext z; simp [comb, U_zero]
  have hg := _root_.GlobalTheory.GalTheta.gal_all D cc δ hc M ρ hK hD N N' L L' hL hL' 1 (fun _ => 1) (fun _ => 0) G x x' m hGTh hm hmx
    (fun _ => by rw [smul_zero]; exact zero_mem _) hx'
  rw [hcomb] at hg
  refine ⟨hlam ▸ (_root_.GlobalTheory.CurveLattice.lattice_of_curve D g1 cc' δ' hc').1, x', (hg hC hCx).1, ?_⟩
  rw [hT] at hE ⊢
  rw [hlam] at ht' ⊢
  exact (norm_core D σ hσ cc' δ' hc' t0' ht' L L' hL hL' _ hE).2 x'

theorem norm_big (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (t0 : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0)
    {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hL : SD D L) (hL' : SD D L') (hN : Even (N * N'))
    (G : VC D N N' → ℂ) (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hQ : Qbar ≤ M)
    (hD : DataIn D (tor0 D cc δ) M) (hC : CoefIn D G M)
    (t0' : ℂ) (ht' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0')
    (x : VC D N N') (hx : LaQ D (tor0 D cc δ) L L' x) (hCx : CoefIn D (U D (tor0 D cc δ) x G) M) :
    normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
        (fnConj D M ρ (U D (tor0 D cc δ) x G)) =
      nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') := by
  rcases (_root_.GlobalTheory.ThetaConj.useBar_holds D cc δ hc M ρ hD).1 with hK | hK
  · obtain ⟨-, x', e1, e2⟩ := norm_fix D cc δ hc t0 ht L L' hL hL' hN G hG M ρ hK hQ hD hC t0' ht' x hx hCx
    rw [e1, e2]
  · obtain ⟨-, hT, hb⟩ := _root_.GlobalTheory.ThetaConj.useBar_holds D cc δ hc M (rhoBar M ρ) hD
    have hbb : rhoBar M (rhoBar M ρ) = ρ := by
      ext y; simp [rhoBar]
    rw [hbb] at hT hb
    have hl : lamConj M ρ (lamOf D cc δ) =
        (lamConj M (rhoBar M ρ) (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    have hmem : ∀ z, z ∈ lamConj M ρ (lamOf D cc δ) ↔
        (starRingEnd ℂ) z ∈ lamConj M (rhoBar M ρ) (lamOf D cc δ) := by
      intro z
      rw [hl, AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro h
        exact ⟨_, h, by simp⟩
    have ht'' : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M (rhoBar M ρ) (lamOf D cc δ)) ((starRingEnd ℂ) t0') := by
      obtain ⟨a1, a2, a3⟩ := ht'
      rw [hmem] at a1 a2 a3
      refine ⟨by simpa [map_ofNat] using a1, ?_, ?_⟩
      · simpa [map_ofNat] using a3
      · simpa [map_ofNat, sub_eq_add_neg] using a2
    obtain ⟨hlat, x', e1, e2⟩ :=
      norm_fix D cc δ hc t0 ht L L' hL hL' hN G hG M (rhoBar M ρ) hK hQ hD hC _ ht'' x hx hCx
    have hTh := (_root_.GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht N N' L L' hL hL' hN G hG M (rhoBar M ρ) hD hC).1
    have e3 := ((hb N N' L L' (fnConj D M (rhoBar M ρ) G)).2.2 hTh).2 hL hL' x'
    have e4 := _root_.GlobalTheory.MeanSquareConj.nrm1Sq_th0_map_conj_eq _ hlat ((starRingEnd ℂ) t0')
    rw [Complex.conj_conj, ← hl] at e4
    rw [(hb N N' L L' (U D (tor0 D cc δ) x G)).1, e1, hT, e3, e2, e4]

theorem useNorm_all : ∀ D : D7, useNorm D := by
  intro D cc δ hc t0 ht N N' L L' hL hL' hN G hG M ρ hD hC t0' ht'
  obtain ⟨M', ρ', hle, hQ, he⟩ := exists_ext M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [he (g2 (lamOf D cc δ)) hD.2.1, he (g3 (lamOf D cc δ)) hD.2.2]
  have hT : torConj D (tor0 D cc δ) M ρ = torConj D (tor0 D cc δ) M' ρ' := by
    unfold torConj
    congr 1
    funext τ y
    exact (he _ (hD.1 τ y)).symm
  have hf : ∀ F : VC D N N' → ℂ, CoefIn D F M → fnConj D M ρ F = fnConj D M' ρ' F := by
    intro F hF
    funext z
    unfold fnConj
    exact tsum_congr fun α => by rw [he _ (hF α)]
  have hD' : DataIn D (tor0 D cc δ) M' := ⟨fun τ y => hle (hD.1 τ y), hle hD.2.1, hle hD.2.2⟩
  have main : ∀ x, LaQ D (tor0 D cc δ) L L' x → CoefIn D (U D (tor0 D cc δ) x G) M →
      normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L')
          (fnConj D M ρ (U D (tor0 D cc δ) x G)) =
        nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t0') ^ (fF D * N * N') := by
    intro x hx hCx
    rw [hf _ hCx, hT, hl]
    exact norm_big D cc δ hc t0 ht L L' hL hL' hN G hG M' ρ' hQ hD' (fun α => hle (hC α)) t0' (hl ▸ ht') x hx
      (fun α => hle (hCx α))
  refine ⟨?_, main⟩
  have := main 0 ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩ (by rw [U_zero]; exact hC)
  rwa [U_zero] at this

end GlobalTheory.ConjNorm
end

