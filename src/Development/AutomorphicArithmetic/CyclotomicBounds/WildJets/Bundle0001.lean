module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProduct
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.CmbIop
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

set_option maxHeartbeats 1000000 in
open GlobalTheory.NormSum.KernelAt in
theorem UpperTheory.WildA.cmbIop :
    ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)), cc = ⊤ → ∀ (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
      ∀ (a b : ℕ) (e0 : VC D a b → ℂ), oddE0 D cc δ t0 a b e0 →
      ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
      ∀ (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), EqAt D l Ls (stdL D a) → EqAt D l Lt (stdL D b) → ∀ k : ℕ, 0 < k →
      ∃ (β : Fin (fF D * a * b) → Matrix (Fin b) (Fin a) D.host.E) (M : ℕ), OnB D β ∧ LocBasis D l (YYl D (stdL D a) (stdL D b)) β ∧
        0 < M ∧ Nat.Coprime M l ∧ ∀ s : VC D a b, k • s ∈ La D (tor0 D cc δ) Ls Lt →
          KernelAt.Cmb D (tor0 D cc δ) lam (LaB D (tor0 D cc δ) β) (pullB D (tor0 D cc δ) β (GL3Theta.th0 (lamOf D cc δ) t0)) (M * k) 1
            (U D (tor0 D cc δ) s (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0)) := by
  intro D hI cc hcc δ t0 hC hT a d e0 hvac Ls Lt hLs hLt p _ lam hEs hEt Q hQ
  subst hcc
  have hp : p.Prime := Fact.out
  obtain ⟨s₁, hs₁, -, hs₁a⟩ := hEs
  obtain ⟨s₂, hs₂, hs₂a, -⟩ := hEt
  have hLa := smul_mem_La ⊤ δ (smul_mem_YYl (smul_mem_homL hs₁a hs₂a))
  have hsp : Nat.Coprime (s₂ * s₁) p := Nat.Coprime.mul_left hs₂ hs₁
  obtain ⟨-, -, -, -, hfg, -⟩ := _root_.GlobalTheory.ThetaLine.theta_line D hI.g1 ⊤ δ hC a d _
    (Or.inr ⟨Ls, Lt, hLs, hLt, rfl⟩)
  have hi₁ := coprime_index (La0 D (tor0 D ⊤ δ) a d) _ hfg _ p hp hsp hLa
  obtain ⟨b, ε, hb, hloc, hε, hεn, hi₀, he0⟩ := hvac.2.2.2.2 p lam (by simp)
  obtain ⟨-, -, hB, -⟩ := _root_.GlobalTheory.ThetaLine.theta_line D hI.g1 ⊤ δ hC a d _ (Or.inl ⟨_, b, hb, rfl⟩)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = ((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) a d)).index := ⟨_, rfl⟩
  have hMp : Nat.Coprime (n₀ * (s₂ * s₁)) p := Nat.Coprime.mul_left (hn₀ ▸ hi₀) hsp
  have hM0 : n₀ * (s₂ * s₁) ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at hMp
    exact hp.one_lt.ne' hMp
  have hn : n₀ * (s₂ * s₁) * Q ≠ 0 := mul_ne_zero hM0 hQ.ne'
  have a0 : ∀ x ∈ La0 D (tor0 D ⊤ δ) a d, n₀ • x ∈ LaB D (tor0 D ⊤ δ) b := fun x hx => by
    rw [hn₀]
    exact ((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) a d)).nsmul_index_mem ⟨x, hx⟩
  have a1 : ∀ x ∈ La D (tor0 D ⊤ δ) Ls Lt, (n₀ * (s₂ * s₁)) • x ∈ LaB D (tor0 D ⊤ δ) b := fun x hx => by
    rw [mul_smul]
    exact a0 _ (hLa x hx)
  have c0 : Cmb D (tor0 D ⊤ δ) lam (LaB D (tor0 D ⊤ δ) b) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0))
      (n₀ * (s₂ * s₁) * Q) (1 * 1) e0 := by
    rw [he0]
    refine Cmb.smul ⟨hε, ?_⟩ (Cmb.iop hn hB hi₀ (fun x hx => ?_) Cmb.base)
    · rw [lamC, dite_eq_left hε] at hεn
      exact hεn.le
    · rw [mul_assoc n₀, mul_comm n₀, mul_smul]
      exact AddSubgroup.nsmul_mem _ (a0 x hx) _
  have c1 := Cmb.iop hn hB hi₁ (fun x hx => by
    rw [mul_comm _ Q, mul_smul]
    exact AddSubgroup.nsmul_mem _ (a1 x hx) _) c0
  rw [one_mul] at c1
  refine ⟨b, n₀ * (s₂ * s₁), hb, hloc, Nat.pos_of_ne_zero hM0, hMp, fun s hs => ?_⟩
  refine Cmb.transl hn hB ?_ c1
  rw [mul_smul]
  exact a1 _ hs
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.CmbJet
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

open GlobalTheory.NormSum.Term in
theorem UpperTheory.WildA.cmbJet :
    ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (cc : Ideal (𝓞 D.host.K)), cc = ⊤ → ∀ (δ t0 : ℂ), Crv D cc δ →
      GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a b r : ℕ) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l])
      (β : Fin r → Matrix (Fin b) (Fin a) D.host.E), OnB D β → LocBasis D l (YYl D (stdL D a) (stdL D b)) β →
      ∀ (n : ℕ), 0 < n → (l ∣ n → SplitIn D l) → ∀ (C : ℝ), 0 ≤ C → ∀ G : VC D a b → ℂ,
      KernelAt.Cmb D (tor0 D cc δ) lam (LaB D (tor0 D cc δ) β) (pullB D (tor0 D cc δ) β (GL3Theta.th0 (lamOf D cc δ) t0)) n C G →
      ∀ mon : GL3Theta.Idx D a b →₀ ℕ,
        Term.Bd lam (C * (l : ℝ) ^ ((mon.degree : ℝ) * (dl l + (if l = D.host.d then 1 / 4 else 0) + (padicValNat l n : ℝ))))
          (GL3Theta.applyAt0 D (MvPolynomial.monomial mon 1) G) := by
  intro D hI S dl hL cc hcc δ t0 hC ht a b r l _ lam β hb hloc n hn hsp C hC0 G hG mon
  subst hcc
  obtain ⟨k, c, s, hs, hr, hF⟩ := hG.out
  have hp : l.Prime := Fact.out
  have hp0 : (0 : ℝ) < l := by exact_mod_cast hp.pos
  have hN := norm_natCast_inv l hn.ne'
  have he0 : 0 ≤ (if l = D.host.d then (l : ℝ) ^ (((mon.degree : ℕ) : ℝ) / 4) else 1) := by
    split_ifs <;> positivity
  have hmon : (MvPolynomial.monomial mon 1 : MvPolynomial (GL3Theta.Idx D a b) ℂ) =
      MvPolynomial.map (Int.castRingHom ℂ) (MvPolynomial.monomial mon 1) := by
    rw [MvPolynomial.map_monomial, map_one (Int.castRingHom ℂ)]
  have hcol := rpow_collect hp0 (l = D.host.d) mon.degree 0 (dl l) (padicValNat l n : ℝ)
  rw [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero] at hcol
  rw [← hcol, mul_left_comm, hmon, hF]
  refine bd_applyAt0 (lam := lam) D (by positivity) _ _
    (MvPolynomial.isHomogeneous_monomial _ rfl) fun f => ?_
  refine bd_coord D (by positivity) (by positivity) (tor0 D ⊤ δ) (fun _ _ => rfl)
    (YYl D (stdL D a) (stdL D b)) (hL.2.2.2.2 l lam a b) _ (fun y hy => ?_) f
  rw [iteratedFDeriv_comb _ (fun i => (c i : ℂ))
    (fun i => U D (tor0 D ⊤ δ) (s i) (pullB D (tor0 D ⊤ δ) β (GL3Theta.th0 (lamOf D ⊤ δ) t0))) fun i =>
    contDiff_U_pullB D _ β _ (differentiable_evenTheta D ⊤ δ t0 hC) (s i) _]
  refine Bd.sum (by positivity) _ _ fun i _ => ?_
  refine (Bd.coe (hr i)).mul ?_
  have := _root_.GlobalTheory.ProductJets.jets_translate_product D hI l lam ⊤ δ hC (by simp) t0 ht a b _ β hb hloc (s i) n
    hn (hs i) hsp _ y hy
  rw [hN] at this
  exact this
end

