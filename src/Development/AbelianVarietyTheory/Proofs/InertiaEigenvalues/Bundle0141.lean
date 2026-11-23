module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualSumLe
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory.HermNbr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] {r : ℕ}

theorem good_map (cK : K ≃+* K) {J : Matrix (Fin r) (Fin r) K} {ϖ : O} {N : ℕ}
    {L : Submodule O (Fin r → K)} (hL : Good cK J ϖ N L) (hϖ : Irreducible ϖ)
    (g : GL (Fin r) K) (hU : ((g : Matrix (Fin r) (Fin r) K).map cK).transpose * J *
      (g : Matrix (Fin r) (Fin r) K) = J) :
    Good cK J ϖ N (L.map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)) := by
  set G := ((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hG
  set Gi := (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O with hGi
  have h1 : ∀ x, G (Gi x) = x := by
    intro x
    change (g : Matrix (Fin r) (Fin r) K).mulVec ((((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have h2 : ∀ x, Gi (G x) = x := by
    intro x
    change (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).mulVec ((g : Matrix (Fin r) (Fin r) K).mulVec x) = x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have memG : ∀ x, x ∈ L.map G ↔ Gi x ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩; rw [h2]; exact hy
    · intro h; exact ⟨Gi x, h, h1 x⟩
  have hfG : ∀ x y, hf cK J (G x) (G y) = hf cK J x y := fun x y => hf_mulVec cK J _ hU x y
  obtain ⟨hSD, habs, hidx⟩ := hL
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [memG, hSD (Gi x)]
    constructor
    · intro h y hy
      rw [← h1 x, ← h1 y, hfG]
      exact h _ ((memG y).1 hy)
    · intro h y hy
      have := h (G y) ((memG _).2 (by rw [h2]; exact hy))
      rwa [← h1 x, hfG] at this
  · intro x
    obtain ⟨k, hk⟩ := habs (Gi x)
    refine ⟨k, (memG _).2 ?_⟩
    rw [map_smul]
    exact hk
  · have hinj : Function.Injective G.toAddMonoidHom := fun x y h => by
      have := congrArg Gi h
      simpa [h2] using this
    set f : (Fin r → K) →ₗ[O] (Fin r → K) := ϖ • LinearMap.id with hf'
    have hcomm : (L.map G).map f = (L.map f).map G := by
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext x
      simp [hf', hG]
    have e : ∀ P : Submodule O (Fin r → K),
        (P.map G).toAddSubgroup = P.toAddSubgroup.map G.toAddMonoidHom := fun P => by
      ext x; simp [Submodule.mem_map]
    unfold idx at hidx ⊢
    rw [← hf'] at hidx ⊢
    rw [hcomm, e, e, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hidx]

end GlobalTheory.HermNbr

theorem GlobalTheory.HermNbr.selfDual_sum_le : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (c : O ≃+* O) (cK : K ≃+* K), (∀ x, c (c x) = x) → (∀ x, cK (algebraMap O K x) = algebraMap O K (c x)) → (∃ x, IsUnit (c x - x)) → ∀ (r n : ℕ) (J : Matrix (Fin r) (Fin r) O), IsUnit J.det → J.transpose.map c = J → 2 * r + 5 ≤ n → ∀ C : Finset (GL (Fin r) K), (∀ g ∈ C, ((g : Matrix (Fin r) (Fin r) K).map cK).transpose * J.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = J.map (algebraMap O K)) → (∀ g ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) ≠ Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) → (∀ g ∈ C, ∀ g' ∈ C, (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) → g = g') → ∑ g ∈ C, ((((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ (-(2 : ℝ)) := by
  intro O K _ _ _ _ _ _ _ c cK hc hcK _ r n J hJdet hJh hn C hU hne hinj
  classical
  set J' := J.map (algebraMap O K) with hJ'
  have hc2 : ∀ x : K, cK (cK x) = x := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀, map_div₀, hcK, hcK, hcK, hcK, hc, hc]
  have hJ'h : J'.transpose.map cK = J' := by
    ext i j
    simp only [hJ', Matrix.map_apply, Matrix.transpose_apply, hcK]
    have := congrFun (congrFun hJh i) j
    simp only [Matrix.map_apply, Matrix.transpose_apply] at this
    rw [this]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  set Q := Nat.card (IsLocalRing.ResidueField O) with hQdef
  have hQ2 : 2 ≤ Q := Finite.one_lt_card
  set L0 : Submodule O (Fin r → K) := Submodule.span O (Set.range (Pi.basisFun K (Fin r))) with hL0def
  have hL0 : GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L0 := by
    refine ⟨GlobalTheory.HermNbr.std_sd c cK hcK hc2 J hJdet, ?_, GlobalTheory.HermNbr.idx_std hϖ⟩
    intro x
    choose k hk using fun i => GlobalTheory.HermNbr.exists_pow_mul_mem hϖ (x i)
    exact ⟨_, GlobalTheory.HermNbr.std_pow_mem_of_le hk⟩
  set φ : GL (Fin r) K → Submodule O (Fin r → K) := fun g =>
    L0.map (((g : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) with hφ
  have hgood : ∀ g ∈ C, GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) (φ g) := fun g hg =>
    GlobalTheory.HermNbr.good_map cK hL0 hϖ g (hU g hg)

  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQ1 : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
  set s : ℝ := (n : ℝ) / 2 with hs
  set D : ℝ := (Q : ℝ) ^ r * Q / ((Q : ℝ) - 1) with hD
  set y : ℝ := (Q : ℝ) ^ (-(2 : ℝ)) with hy
  have hs0 : 0 < s := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast (by omega : 5 ≤ n)
    rw [hs]; linarith
  have hD0 : 0 ≤ D := by positivity
  have hy0 : 0 < y := Real.rpow_pos_of_pos hQ0 _
  have hy4 : y ≤ 1 / 4 := by
    rw [hy, Real.rpow_neg hQ0.le]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hρ : D * (Q : ℝ) ^ (-s) ≤ 2 * y := by
    have hsr : (r : ℝ) + 5 / 2 ≤ s := by
      have : ((2 * r + 5 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at this
      rw [hs]; linarith
    have h1 : (Q : ℝ) ^ (-s) ≤ (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) = ((Q : ℝ) ^ r)⁻¹ * ((Q : ℝ) ^ (-(2 : ℝ)) * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [← Real.rpow_add hQ0, show -((r : ℝ) + 5 / 2) = -(r : ℝ) + (-(2 : ℝ) + -(1 / 2 : ℝ)) by ring,
        Real.rpow_add hQ0, Real.rpow_neg hQ0.le, Real.rpow_natCast]
    have h3 : (Q : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h4 : (Q : ℝ) / ((Q : ℝ) - 1) ≤ 2 := by
      rw [div_le_iff₀ hQ1]; linarith
    have hQr0 : (0 : ℝ) < (Q : ℝ) ^ r := by positivity
    calc D * (Q : ℝ) ^ (-s) ≤ D * (Q : ℝ) ^ (-((r : ℝ) + 5 / 2)) := mul_le_mul_of_nonneg_left h1 hD0
      _ = (Q : ℝ) / ((Q : ℝ) - 1) * (y * (Q : ℝ) ^ (-(1 / 2 : ℝ))) := by
          rw [h2, hD, hy]; field_simp
      _ ≤ 2 * (y * 1) := by
          apply mul_le_mul h4 (mul_le_mul_of_nonneg_left h3 hy0.le) (by positivity) (by norm_num)
      _ = 2 * y := by ring
  have hρ1 : D * (Q : ℝ) ^ (-s) < 1 := by linarith

  have key := GlobalTheory.HermNbr.graph_sum {L | GlobalTheory.HermNbr.Good cK J' ϖ (Q ^ r) L}
    (fun L Λ => Λ.toAddSubgroup.relIndex L.toAddSubgroup) (GlobalTheory.HermNbr.Nbrs cK J' ϖ) Q hQ2 s D
    hs0 hD0 hρ1 (fun L _ => AddSubgroup.relIndex_self _)
    (fun L hL Λ hΛ hne hi => by
      obtain ⟨L', h1, h2, h3, h4⟩ :=
        GlobalTheory.HermNbr.step_exists c cK hcK hc2 hJ'h hϖ hL hΛ hne hi
      exact ⟨L', h1, h2, h3, h4⟩)
    (fun L hL t ht => by
      have h := GlobalTheory.HermNbr.card_nbrs c cK hcK hc2 hJ'h hϖ hL (by positivity) t ht
      rw [hD, le_div_iff₀ hQ1]
      have : ((t.card * (Q - 1) : ℕ) : ℝ) ≤ ((Q ^ r * Q : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_sub (by omega : 1 ≤ Q)] at this
      linarith)
    L0 hL0 (C.image φ)
    (by
      intro Λ hΛ
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hΛ)
      exact hgood g hg)
    (by
      intro h
      obtain ⟨g, hg, hg'⟩ := Finset.mem_image.1 h
      exact hne g hg hg')
  rw [Finset.sum_image (fun g hg g' hg' h => hinj g hg g' hg' h)] at key
  have hsum : ∀ g ∈ C, (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) =
      (((φ g).toAddSubgroup.relIndex L0.toAddSubgroup : ℕ) : ℝ) ^ (-s) := by
    intro g _; rw [hs, neg_div]
  rw [← Finset.sum_congr rfl hsum] at key
  refine le_trans key ?_
  set ρ := D * (Q : ℝ) ^ (-s)
  have hρ0 : 0 ≤ ρ := by positivity
  rw [div_le_iff₀ (by linarith)]
  nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearMatrixComm
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

theorem semilinear_matrix_comm {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] {r : ℕ}
    (σ τ : A →+* A) (f g : D →+ D) (hf : ∀ a x, f (a • x) = σ a • f x)
    (hg : ∀ a x, g (a • x) = τ a • g x) (hc : ∀ x, f (g x) = g (f x))
    (b : Fin r → D) (hb : LinearIndependent A b) (e : A) (P Q : Fin r → Fin r → A)
    (hQ : ∀ k, g (b k) = ∑ m, Q m k • b m) (hP : ∀ k, e • f (b k) = ∑ m, P m k • b m)
    (p k : Fin r) :
    e * ∑ m, Q p m * τ (P m k) = τ e * ∑ m, P p m * σ (Q m k) := by
  have h1 : τ e • g (f (b k)) = ∑ p, (∑ m, Q p m * τ (P m k)) • b p := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hg, hP, map_sum]
    simp only [hg, hQ, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h2 : e • f (g (b k)) = ∑ p, (∑ m, P p m * σ (Q m k)) • b p := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hQ, map_sum, Finset.smul_sum]
    simp only [hf, smul_comm e, hP, Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have h3 : ∑ p, (e * ∑ m, Q p m * τ (P m k)) • b p
      = ∑ p, (τ e * ∑ m, P p m * σ (Q m k)) • b p := by
    simp only [mul_smul, ← Finset.smul_sum]
    rw [← h1, ← h2, hc, smul_comm]
  exact (Fintype.linearIndependent_iffₛ.1 hb) _ _ h3 p

theorem matrices_comm : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∀ (M : ℕ) (Φ Gm : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧), (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (Gm i m k) : LetA O n) • (b m : W.DD T)) → (∀ k, (fun _ => j R.E : LetA O n) ^ M • W.φD T (b k : W.DD T) = ∑ m, (fun i => j (Φ i m k) : LetA O n) • (b m : W.DD T)) → ∀ i, R.E ^ M • (Gm i * (Φ i).map R.γ) = R.γ R.E ^ M • (Φ i * (Gm (i - 1)).map R.φ) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF _ _ M Φ Gm hG hΦ i
  obtain ⟨hj, -, hφ, hγ, -⟩ := hF
  have hb : LinearIndependent (LetA O n) (fun k => (b k : W.DD T)) :=
    b.linearIndependent.map' (W.N T).subtype (Submodule.ker_subtype _)
  have key := semilinear_matrix_comm (A := LetA O n) (letφ (n := n) W.φ₀).toRingHom
    (letγ (n := n) (W.γ₀ W.gam)).toRingHom (W.φD T).toAddMonoidHom (W.γD T W.gam).toAddMonoidHom
    (fun a x => by
      change W.φD T (a • x) = letφ W.φ₀ a • W.φD T x
      rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul])
    (fun a x => by
      change W.γD T W.gam (a • x) = letγ (W.γ₀ W.gam) a • W.γD T W.gam x
      rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul])
    (fun x => W.φγ_comm T W.gam x) _ hb ((fun _ => j R.E : LetA O n) ^ M)
    (fun m k i => j (Φ i m k)) (fun m k i => j (Gm i m k)) hG hΦ
  ext1 p k
  apply hj
  have h := congrFun (key p k) i
  simp only [Pi.mul_apply, Finset.sum_apply, Pi.pow_apply, map_pow] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow,
    map_sum, hφ, hγ]
  exact h

end GlobalTheory.WachTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqAsym
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.SesqAsym

theorem trace_σ {K : UQ} (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) a
  rw [h, RingEquiv.apply_symm_apply]

theorem sesq_asym : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → (∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g)) ∧ ∀ (s : B.A → B.A → K.E), (∀ x y z, s (x + y) z = s x z + s y z) → (∀ (c : K.E) x z, s (c • x) z = c * s x z) → (∀ y, (∀ z, s y z = 0) → y = 0) → (∀ y z, K.c (s z y) = s (ε * B.g * y) z) → ∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g) ∧ ∀ y z, s y z = B.herm β y z := by
  intro K B hg hP ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  set u := ε * B.g with hu_def
  have hu : u * B.σ u = 1 := by
    rw [hu_def, map_mul, hσε]
    calc ε * B.g * (ε * B.σ B.g) = (ε * ε) * (B.g * B.σ B.g) := by ring
      _ = 1 := by rw [hεε, hg, one_mul]
  refine ⟨GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg K B u hu, ?_⟩
  intro s hadd hlin hnd hsym
  have hvu : B.σ u * u = 1 := by rw [mul_comm]; exact hu

  have hsym' : ∀ y z, s y z = K.c (s z (B.σ u * y)) := by
    intro y z
    rw [hsym, ← mul_assoc, hu, one_mul]
  have hadd2 : ∀ y z z', s y (z + z') = s y z + s y z' := by
    intro y z z'
    rw [hsym', hadd, map_add (f := _), ← hsym', ← hsym']
  have hlin2 : ∀ (e : K.E) y z, s y (e • z) = K.c e * s y z := by
    intro e y z
    rw [hsym', hlin, map_mul, ← hsym']
  have hsu : ∀ y z, s (u * y) (u * z) = s y z := by
    intro y z
    rw [← hsym, ← hsym, K.c_c]
  have hneg1 : ∀ y z, s (-y) z = - s y z := by
    intro y z
    have := hlin (-1) y z
    simpa using this
  have hneg2 : ∀ y z, s y (-z) = - s y z := by
    intro y z
    have := hlin2 (-1) y z
    simpa using this
  have hsg : ∀ y z, s (B.g * y) (B.g * z) = s y z := by
    intro y z
    rcases hε with rfl | rfl
    · simpa [hu_def] using hsu y z
    · have := hsu y z
      simp only [hu_def, neg_mul, one_mul] at this
      rw [hneg1, hneg2, neg_neg] at this
      exact this
  have hadj_g : ∀ y z, s (B.g * y) z = s y (B.σ B.g * z) := by
    intro y z
    conv_lhs => rw [show z = B.g * (B.σ B.g * z) by rw [← mul_assoc, hg, one_mul]]
    exact hsg _ _
  have hadj : ∀ a y z, s (a * y) z = s y (B.σ a * z) := by
    intro a
    obtain ⟨f, rfl⟩ := _root_.GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable K B hP a
    induction f using Polynomial.induction_on with
    | C e =>
      intro y z
      rw [aeval_C, ← Algebra.smul_def, B.σ_alg, ← Algebra.smul_def, hlin, hlin2, K.c_c]
    | add p q hp hq =>
      intro y z
      rw [map_add (f := _), add_mul, hadd, hp, hq, map_add (f := _), add_mul, hadd2]
    | monomial n e ih =>
      intro y z
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, mul_assoc, ih, hadj_g]
      congr 1
      rw [map_mul B.σ _ B.g]
      ring

  let ℓ : Module.Dual K.E B.A :=
    { toFun := fun y => s y 1
      map_add' := fun x y => hadd x y 1
      map_smul' := fun c x => hlin c x 1 }
  let φ : B.A →ₗ[K.E] Module.Dual K.E B.A := Algebra.traceForm K.E B.A
  have hφi : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine _root_.GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (_root_.GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable K B hP) w fun y => ?_
    have := LinearMap.congr_fun hw y
    simpa [φ, Algebra.traceForm_apply] using this
  have hφs : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hφi
  obtain ⟨β, hβ⟩ := hφs ℓ
  have hβs : ∀ y, s y 1 = Algebra.trace K.E B.A (β * y) := by
    intro y
    have := LinearMap.congr_fun hβ y
    simpa [φ, ℓ, Algebra.traceForm_apply] using this.symm
  have hform : ∀ y z, s y z = B.herm β y z := by
    intro y z
    have h1 := hadj (B.σ z) y 1
    rw [B.σ_σ, mul_one] at h1
    rw [← h1, hβs]
    unfold InvAlg.herm
    congr 1; ring

  have hβinj : Function.Injective (LinearMap.mulLeft K.E β) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : β * y = 0 := hy
    refine hnd y fun z => ?_
    rw [hform]
    unfold InvAlg.herm
    rw [hy', zero_mul, map_zero]
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hβinj) 1
  have hxβ : β * x = 1 := hx
  refine ⟨⟨β, x, hxβ, by rw [mul_comm]; exact hxβ⟩, ?_, hform⟩
  show B.σ β = β * u
  rw [← sub_eq_zero]
  refine _root_.GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP (_root_.GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable K B hP) _ fun y => ?_
  have h3 : Algebra.trace K.E B.A (B.σ β * y) = Algebra.trace K.E B.A (β * u * y) := by
    have h2 := hsym y 1
    rw [hform, hform] at h2
    unfold InvAlg.herm at h2
    rw [← trace_σ] at h2
    simp only [map_mul B.σ, map_one, B.σ_σ, mul_one] at h2
    rw [h2]; congr 1; ring
  rw [sub_mul, map_sub, h3, sub_self]

end GlobalTheory.SesqAsym
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulVecSmul
section
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

theorem sum_mulVec_smul {ι E EE D O : Type} [CommRing O] [CommRing E] [CommRing EE] [Algebra O E]
    [Algebra O EE] [AddCommGroup D] [Module EE D] (jE : (ι → E) →ₐ[O] EE) {r : ℕ} (b : Fin r → D)
    (A : ι → Matrix (Fin r) (Fin r) E) (y : ι → Fin r → E) :
    ∑ m, jE (fun i => (A i).mulVec (y i) m) • b m =
      ∑ k, jE (fun i => y i k) • ∑ m, jE (fun i => A i m k) • b m := by
  have h : ∀ m, (fun i => (A i).mulVec (y i) m) =
      ∑ k, ((fun i => y i k) * (fun i => A i m k) : ι → E) := by
    intro m
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem isUnit_ι_E {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) : IsUnit (R.ι R.E) := by
  have hs : R.s ≠ 0 := by
    intro h
    have h1 := R.es
    have h2 := R.prime.two_le
    rw [h] at h1
    omega
  have h := R.EE_X.map R.φE
  rw [R.φE_ext, R.φ_X, map_mul, map_pow] at h
  exact (isUnit_pow_iff hs).1 (isUnit_of_mul_isUnit_right h)

theorem coord_comm_φ_γ : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → ∀ S : Sys R n r, (∀ k, W.γD T W.gam (b k : W.DD T) = ∑ m, (fun i => j (S.G i m k) : LetA O n) • (b m : W.DD T)) → (∀ k, (fun _ => j R.E : LetA O n) ^ S.M • W.φD T (b k : W.DD T) = ∑ m, (fun i => j (S.Φ i m k) : LetA O n) • (b m : W.DD T)) → (∀ x, coord W R jE T (fun k => (b k : W.DD T)) (S.φD x) = W.φD T (coord W R jE T (fun k => (b k : W.DD T)) x)) ∧ ∀ x, coord W R jE T (fun k => (b k : W.DD T)) (S.γD x) = W.γD T W.gam (coord W R jE T (fun k => (b k : W.DD T)) x) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    _ hE _ S hγ hφ
  obtain ⟨hext, -, -, hφE, hγE⟩ := hE
  refine ⟨fun x => ?_, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [coord_apply, coord_apply, map_sum]
      refine (sum_mulVec_smul jE (fun k => (b k : W.DD T))
        (fun i => Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι)
        (fun i k => R.φE (x (i - 1) k))).trans ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [W.φD_smul, ← hφE]
      congr 1
      have h1 : ∀ m, jE (fun i => (Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι) m k) =
          jE (fun _ => Ring.inverse (R.ι R.E)) ^ S.M *
            algebraMap (LetA O n) W.EE (fun i => j (S.Φ i m k)) := by
        intro m
        rw [← hext, ← map_pow, ← map_mul]
        rfl
      have h2 : jE (fun _ => Ring.inverse (R.ι R.E)) *
          algebraMap (LetA O n) W.EE (fun _ => j R.E) = 1 := by
        rw [← hext (fun _ => R.E), ← map_mul, ← map_one jE]
        congr 1
        funext i
        exact Ring.inverse_mul_cancel _ (isUnit_ι_E R)
      simp only [h1, mul_smul, algebraMap_smul]
      rw [← Finset.smul_sum, ← hφ, ← algebraMap_smul W.EE ((fun _ => j R.E : LetA O n) ^ S.M),
        smul_smul, map_pow, ← mul_pow, h2, one_pow,
        one_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [coord_apply, coord_apply, map_sum]
      refine (sum_mulVec_smul jE (fun k => (b k : W.DD T))
        (fun i => (S.G i).map R.ι) (fun i k => R.γE (x i k))).trans ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [W.γD_smul, ← hγE, hγ]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← algebraMap_smul W.EE (fun i => j (S.G i m k) : LetA O n), ← hext]
      rfl

end GlobalTheory.WachTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerFunctionalWeylVanishOfWeylUnipotentZero
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem wS_nS_wS_eq_unit {k : Type} [CommRing k] (z : kˣ) :
    wS k * nS (z : k) * wS k = nS ((-z⁻¹ : kˣ) : k) * mS (-z⁻¹) * (wS k * nS ((-z⁻¹ : kˣ) : k)) := by
  have h1 : (z : k) * ((z⁻¹ : kˣ) : k) = 1 := z.mul_inv
  have cw : ((wS k : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; -1, 0] := rfl
  have cn : ∀ t : k, ((nS t : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = !![1, t; 0, 1] :=
    fun _ => rfl
  have cm : ∀ s : kˣ, ((mS s : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)] := fun _ => rfl
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, cw, cn, cm]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_fin_two] <;> ring_nf <;> simp [h1]

theorem lam_flip_eq_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ, A.InI Ψ → (∀ z, Ψ (wS A.K * nS z) = 0) → ∀ (a : A.K) (c : F), A.abelian₂ μK ψ a (fun h => Ψ (h * wS A.K)) c = 0 := by
  intro F E _ _ _ _ _ A ψ μK hμ Ψ hΨ h0 a c
  have hnull : μK {t | ¬ IsUnit t} = 0 := (_root_.GlobalTheory.JR.EtFacts.main F E A).2.2.2.2.2.2.2.2.1 μK hμ
  have hae : ∀ᵐ z ∂μK, IsUnit z := ae_iff.2 hnull
  unfold Et.abelian₂
  apply integral_eq_zero_of_ae
  apply ae_restrict_of_ae
  filter_upwards [hae] with z hz
  obtain ⟨u, rfl⟩ := hz
  simp only [Pi.zero_apply]
  rw [wS_nS_wS_eq_unit u, hΨ.2, h0, mul_zero, zero_mul]

end GlobalTheory.JR
end

