module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorOfGaloisRelations
section
open Matrix

theorem GlobalTheory.ht_operator_of_galois_relations : ∀ {k : Type} [Field k] (d N q : ℕ) (p : Fin d → ℕ) (a b z w : k) (y y' v v₀ e r sy sv : Matrix (Fin d) (Fin d) k), a ≠ 0 → b ≠ 0 → z * w = 1 → y * y' = a ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) k) → y * v₀ = a ^ N • v → a ^ N • (r * sy) = b ^ N • (y * e) → r * sv * Matrix.diagonal (fun j => w ^ p j) = w ^ q • v → sy * v₀ = b ^ N • sv → ∃ u : Matrix (Fin d) (Fin d) k, u * y = y * e ∧ u * v = v * Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
  intro k _ d N q p a b z w y y' v v₀ e r sy sv ha hb hzw hy hyv hr hsv hsy
  have hz : z ≠ 0 := left_ne_zero_of_mul_eq_one hzw
  have hw : w = z⁻¹ := eq_inv_of_mul_eq_one_right hzw
  have haN : a ^ N ≠ 0 := pow_ne_zero _ ha
  have hbN : b ^ N ≠ 0 := pow_ne_zero _ hb
  have ha2 : a ^ (2 * N) ≠ 0 := pow_ne_zero _ ha
  have hy' : y' * y = a ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) k) := by
    have h1 : y * ((a ^ (2 * N))⁻¹ • y') = 1 := by
      rw [Matrix.mul_smul, hy, smul_smul, inv_mul_cancel₀ ha2, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h2
    calc y' * y = a ^ (2*N) • ((a ^ (2 * N))⁻¹ • (y' * y)) := by
          rw [smul_smul, mul_inv_cancel₀ ha2, one_smul]
      _ = _ := by rw [h2]
  have hD : r * sv = v * Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
    have hdd : Matrix.diagonal (fun j => w ^ p j) * Matrix.diagonal (fun j => z ^ p j) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext j; rw [← mul_pow, mul_comm, hzw, one_pow]
    have hdiag : w ^ q • Matrix.diagonal (fun j => z ^ p j)
        = Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
        rw [zpow_sub₀ hz, zpow_natCast, zpow_natCast, hw, inv_pow, div_eq_mul_inv, mul_comm]
      · simp [Matrix.diagonal_apply_ne _ hij]
    calc r * sv = r * sv * (Matrix.diagonal (fun j => w ^ p j) * Matrix.diagonal (fun j => z ^ p j)) := by
          rw [hdd, Matrix.mul_one]
      _ = (w ^ q • v) * Matrix.diagonal (fun j => z ^ p j) := by rw [← Matrix.mul_assoc, hsv]
      _ = _ := by rw [Matrix.smul_mul, ← Matrix.mul_smul, hdiag]
  have hyev : y * e * v₀ = a ^ N • (r * sv) := by
    have h1 : b ^ N • (y * e * v₀) = b ^ N • (a ^ N • (r * sv)) := by
      rw [← Matrix.smul_mul, ← hr, Matrix.smul_mul, Matrix.mul_assoc, hsy, Matrix.mul_smul, smul_comm]
    exact smul_right_injective _ hbN h1
  have hy'v : y' * v = a ^ N • v₀ := by
    have h1 : a ^ N • (y' * v) = a ^ N • (a ^ N • v₀) := by
      rw [← Matrix.mul_smul, ← hyv, ← Matrix.mul_assoc, hy', Matrix.smul_mul, Matrix.one_mul, smul_smul,
        ← pow_add, two_mul]
    exact smul_right_injective _ haN h1
  refine ⟨(a ^ (2 * N))⁻¹ • (y * e * y'), ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_assoc, hy', Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ ha2, one_smul]
  · have hc : (a ^ (2 * N))⁻¹ * a ^ N * a ^ N = 1 := by
      rw [mul_assoc, ← pow_add, ← two_mul, inv_mul_cancel₀ ha2]
    rw [Matrix.smul_mul, Matrix.mul_assoc, hy'v, Matrix.mul_smul, hyev, smul_smul, smul_smul, hc, one_smul, hD]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsAlt
section
namespace GlobalTheory.TargetStatementAlt

open Polynomial

theorem main {R F : Type} [CommRing R] [Field F] [Algebra R F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (hM : IsIntegral R M) :
    IsIntegral R (Matrix.trace M) := by
  let f : F →ₐ[R] AlgebraicClosure F := IsScalarTower.toAlgHom R F (AlgebraicClosure F)
  let φ : Matrix n n F →ₐ[R] Matrix n n (AlgebraicClosure F) := f.mapMatrix
  obtain ⟨p, hpm, hp⟩ := hM.map φ
  have key : ∀ μ ∈ (φ M).charpoly.roots, IsIntegral R μ := by
    intro μ hμ
    have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.mp hμ).2
    have hs : μ ∈ spectrum (AlgebraicClosure F) (φ M) :=
      Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
    have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F)))
      ⟨μ, hs, rfl⟩
    have h2 : aeval (φ M) (p.map (algebraMap R (AlgebraicClosure F))) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h2, spectrum.mem_iff, sub_zero] at h1
    refine ⟨p, hpm, ?_⟩
    by_contra hne
    apply h1
    have : eval μ (p.map (algebraMap R (AlgebraicClosure F))) ≠ 0 := by
      rwa [eval_map_algebraMap, aeval_def]
    exact (Ne.isUnit this).map _
  have ht : IsIntegral R (Matrix.trace (φ M)) := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    exact IsIntegral.multiset_sum key
  have he : Matrix.trace (φ M) = f (Matrix.trace M) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [φ, Matrix.trace, map_sum, AlgHom.mapMatrix_apply]
  rw [he] at ht
  exact (isIntegral_algHom_iff f f.toRingHom.injective).mp ht

theorem target : ∀ {R F : Type} [inst : CommRing R] [inst_1 : Field F] [inst_2 : Algebra R F] {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] (M : Matrix n n F), IsIntegral R M → IsIntegral R (Matrix.trace M) :=
  fun M h => main M h

end GlobalTheory.TargetStatementAlt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBis
section
namespace GlobalTheory.IntegralCriterion

theorem main : ∀ (k : Type) [inst : Field k] (n : ℕ) (v : Fin (n + (1 : ℕ)) → k), v ≠ (0 : Fin (n + (1 : ℕ)) → k) → ∃ (P : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k), IsUnit P ∧ ∀ (a : Fin (n + (1 : ℕ))), P a (0 : Fin (n + (1 : ℕ))) = v a := by
  intro k _ n v hv
  set e0 : Fin (n + 1) → k := Pi.single 0 1 with he0def
  have he0 : e0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [e0] at this
  let f : (k ∙ e0) ≃ₗ[k] (k ∙ v) :=
    (LinearEquiv.toSpanNonzeroSingleton k _ e0 he0).symm ≪≫ₗ
      LinearEquiv.toSpanNonzeroSingleton k _ v hv
  have hf : (f ⟨e0, Submodule.mem_span_singleton_self e0⟩ : Fin (n + 1) → k) = v := by
    have h1 : (⟨e0, Submodule.mem_span_singleton_self e0⟩ : k ∙ e0) =
        LinearEquiv.toSpanNonzeroSingleton k _ e0 he0 1 := by
      ext; simp
    simp only [f, LinearEquiv.trans_apply, h1, LinearEquiv.symm_apply_apply]
    simp
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hge : g e0 = v := by
    rw [← hf, hg]
  refine ⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩
  · refine ⟨⟨LinearMap.toMatrix' (g : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)),
      LinearMap.toMatrix' (g.symm : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k)), ?_, ?_⟩, rfl⟩
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
    · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
      congr 1
      ext x : 1
      simp
  · intro a
    rw [LinearMap.toMatrix'_apply]
    change g e0 a = v a
    rw [hge]

end GlobalTheory.IntegralCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisAlt
section
namespace GlobalTheory.ProofStatement

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : AlgebraicClosure (ZMod l)), a ≠ (0 : AlgebraicClosure (ZMod l)) → ∃ (m : ℕ), (0 : ℕ) < m ∧ ¬l ∣ m ∧ a ^ m = (1 : AlgebraicClosure (ZMod l)) := by
  intro l hl a ha
  set K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l))) with hK
  haveI : FiniteDimensional (ZMod l) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K l := charP_of_injective_algebraMap (algebraMap (ZMod l) K).injective l
  obtain ⟨n, _, hcard⟩ := FiniteField.card K l
  have ha' : (⟨a, IntermediateField.mem_adjoin_simple_self (ZMod l) a⟩ : K) ≠ 0 := by
    intro h; apply ha; exact congrArg Subtype.val h
  have hpow := FiniteField.pow_card_sub_one_eq_one _ ha'
  have hl1 : 2 ≤ l := hl.out.two_le
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hq : l ≤ l ^ (n : ℕ) := Nat.le_self_pow (by omega) l
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · rw [hcard]
    intro hd
    have h2 : l ∣ l ^ (n : ℕ) := dvd_pow_self l (by omega)
    have h3 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1) := Nat.dvd_sub h2 hd
    rw [Nat.sub_sub_self (by omega)] at h3
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h3)
  · have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.ProofStatement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisBis
section
namespace GlobalTheory.PowerMembershipInertiaEigenvalues

theorem pow_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (Q : Submodule k U) (hT : ∀ y ∈ Q, (T : U → U) y ∈ Q) (n : ℕ) :
    ∀ y ∈ Q, ((T ^ n : Module.End k U) : U → U) y ∈ Q := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT y hy)

theorem main : ∀ {k U : Type} [inst : Field k] [inst_1 : AddCommGroup U] [inst_2 : Module k U] (T : Module.End k U) (Q : Submodule k U), (∀ y ∈ Q, (T : U → U) y ∈ Q) → ∀ (p : Polynomial k), ∀ y ∈ Q, ((Polynomial.aeval T : Polynomial k → Module.End k U) p : U → U) y ∈ Q := by
  intro k U _ _ _ T Q hT p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y hy
    simp only [map_add (f := _), LinearMap.add_apply]
    exact Q.add_mem (hp y hy) (hq y hy)
  | monomial n a =>
    intro y hy
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Q.smul_mem a (pow_mem T Q hT n y hy)

end GlobalTheory.PowerMembershipInertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisFurther
section
namespace GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues

open Module

theorem exists_common_eigenvector {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (f : ι → Module.End k V)
    (hcomm : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ →
      (∀ i, ∀ w ∈ W, (f i : V → V) w ∈ W) →
        ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ i, ∃ c : k, (f i : V → V) x = c • x := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hW hinv
  by_cases hs : ∀ i, ∃ c : k, ∀ w ∈ W, f i w = c • w
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨x, hx, hx0, fun i => let ⟨c, hc⟩ := hs i; ⟨c, hc x hx⟩⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    let g : Module.End k W := (f i).restrict (fun w hw => hinv i w hw)
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue g
    obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
    have hgv : g v = c • v := hv.apply_eq_smul
    have hv0 : v ≠ 0 := hv.2
    set W' : Submodule k V := W ⊓ Module.End.eigenspace (f i) c with hW'
    have hvW' : (v : V) ∈ W' := by
      refine ⟨v.2, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := congrArg Subtype.val hgv
      simpa [g] using this
    have hW'ne : W' ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hvW'
      exact hv0 (Subtype.ext hvW')
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h
      obtain ⟨w, hw, hne⟩ := hi c
      have : w ∈ W' := h ▸ hw
      exact hne ((Module.End.mem_eigenspace_iff).mp this.2)
    have hdlt : Module.finrank k W' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hinv' : ∀ j, ∀ w ∈ W', (f j : V → V) w ∈ W' := by
      intro j w hw
      refine ⟨hinv j w hw.1, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h1 : f i w = c • w := (Module.End.mem_eigenspace_iff).mp hw.2
      have h2 := congrArg (fun F : Module.End k V => F w) (hcomm i j)
      simp only [Module.End.mul_apply] at h2
      rw [h2, h1, map_smul]
    obtain ⟨x, hx, hx0, hxe⟩ := ih _ hdlt W' rfl hW'ne hinv'
    exact ⟨x, hx.1, hx0, hxe⟩

theorem target : ∀ {k ι V : Type} [inst : Field k] [IsAlgClosed k] [inst_2 : AddCommGroup V] [inst_3 : Module k V] [FiniteDimensional k V] (f : ι → Module.End k V), (∀ (i j : ι), f i * f j = f j * f i) → ∀ (d : ℕ) (W : Submodule k V), Module.finrank k ↥W = d → W ≠ ⊥ → (∀ (i : ι), ∀ w ∈ W, (f i : V → V) w ∈ W) → ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : k), (f i : V → V) x = c • x :=
  fun f hc => exists_common_eigenvector f hc

end GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsExtra
section
namespace GlobalTheory.SimpStatement

open Finset

theorem main {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W] [Module.IsTorsionFree B W]
    (a : G → B → B) (σ : G → W →+ W)
    (hσ : ∀ (g : G) (b : B) (w : W), (σ g : W → W) (b • w) = a g b • (σ g : W → W) w)
    (ha : ∀ (b b' : B), b ≠ (0 : B) → (∀ (g : G), b * a g b' = a g b * b') →
      ∃ (c : K), b' = (Algebra.algebraMap K B : K → B) c * b)
    (v : ι → W) (hv : ∀ (g : G) (i : ι), (σ g : W → W) (v i) = v i)
    (s : Finset ι) (hK : LinearIndepOn K v (↑s : Set ι)) :
    LinearIndepOn B v (↑s : Set ι) := by
  classical

  have key : ∀ T : Finset ι, T ⊆ s → ∀ f : ι → B, ∑ i ∈ T, f i • v i = 0 → ∀ i ∈ T, f i = 0 := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
      intro hTs f hf
      by_contra hne
      push_neg at hne
      obtain ⟨i₀, hi₀, hfi₀⟩ := hne

      have hrel : ∀ j ∈ T, ∀ g : G, f i₀ * a g (f j) = a g (f i₀) * f j := by
        intro j hj g
        set f' : ι → B := fun i => f i₀ * a g (f i) - a g (f i₀) * f i with hf'
        have hsum : ∑ i ∈ T, f' i • v i = 0 := by
          have h1 : ∑ i ∈ T, a g (f i) • v i = 0 := by
            have := congrArg (σ g : W → W) hf
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum, map_zero] at this
            rw [← this]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hσ, hv]
          simp only [hf', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, h1, hf,
            smul_zero, sub_zero]
        have hf'i₀ : f' i₀ = 0 := by simp only [hf']; ring
        have hsum' : ∑ i ∈ T.erase i₀, f' i • v i = 0 := by
          rw [← Finset.add_sum_erase T _ hi₀, hf'i₀, zero_smul, zero_add] at hsum
          exact hsum
        by_cases hj0 : j = i₀
        · subst hj0; ring
        · have := ih (T.erase i₀) (Finset.erase_ssubset hi₀)
            ((Finset.erase_subset _ _).trans hTs) f' hsum' j (Finset.mem_erase.2 ⟨hj0, hj⟩)
          simp only [hf'] at this
          exact sub_eq_zero.1 this
      have hc : ∀ j ∈ T, ∃ c : K, f j = (Algebra.algebraMap K B : K → B) c * f i₀ :=
        fun j hj => ha (f i₀) (f j) hfi₀ (hrel j hj)
      choose! c hc using hc
      have hsumK : ∑ i ∈ T, c i • v i = 0 := by
        have : f i₀ • ∑ i ∈ T, c i • v i = 0 := by
          rw [← hf, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hc i hi, mul_comm, mul_smul, smul_comm]
          rw [algebraMap_smul]
          exact smul_comm (c i) (f i₀) (v i)
        exact (smul_eq_zero_iff_right hfi₀).1 this
      have hKT : LinearIndepOn K v (↑T : Set ι) := hK.mono (by exact_mod_cast hTs)
      have hci₀ := (linearIndepOn_finset_iff.1 hKT) c hsumK i₀ hi₀
      apply hfi₀
      rw [hc i₀ hi₀, hci₀, map_zero, zero_mul]
  exact linearIndepOn_finset_iff.2 (key s subset_rfl)

end GlobalTheory.SimpStatement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsRest
section
universe u_1 u_2

namespace GlobalTheory.PermutationExistence

theorem exists_perm {G : Type u_1} {C : Type u_2} [Group G] [AddCommMonoid C]
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (h : G) (hh : h ∈ H) :
    ∃ σ : G → G, (∀ s ∈ S, σ s ∈ S ∧ (σ s)⁻¹ * (h * s) ∈ V) ∧
      ∀ f : G → C, ∑ s ∈ S, f (σ s) = ∑ s ∈ S, f s := by
  classical
  have key : ∀ s ∈ S, ∃ s' : G, s' ∈ S ∧ s'⁻¹ * (h * s) ∈ V := fun s hs =>
    (hT (h * s) (H.mul_mem hh (hS s hs))).exists
  choose! σ hσS hσV using key
  refine ⟨σ, fun s hs => ⟨hσS s hs, hσV s hs⟩, fun f => ?_⟩

  have hinj : Set.InjOn σ S := by
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 := hσV s₁ hs₁
    rw [heq] at h1
    have h12 : s₁⁻¹ * s₂ ∈ V := by
      have e : ((σ s₂)⁻¹ * (h * s₁))⁻¹ * ((σ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ := by group
      rw [← e]
      exact V.mul_mem (V.inv_mem h1) (hσV s₂ hs₂)
    obtain ⟨u, _, hu⟩ := hT s₂ (hS s₂ hs₂)
    have e1 : s₁ = u := hu s₁ ⟨hs₁, h12⟩
    have e2 : s₂ = u := hu s₂ ⟨hs₂, by rw [inv_mul_cancel]; exact V.one_mem⟩
    rw [e1, e2]
  have himg : S.image σ = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact hσS s hs
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ s ∈ S, f (σ s) = ∑ x ∈ S.image σ, f x := (Finset.sum_image hinj).symm
    _ = ∑ s ∈ S, f s := by rw [himg]

theorem main {G : Type u_1} {C : Type u_2} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* C ≃+* C) (hn : ∀ (g : G) (y : C), ‖act g y‖ = ‖y‖)
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (a b : C) (hb : ‖b‖ ≤ (1 : ℝ))
    (hV : ∀ g ∈ V, act g b = b) (ha : ∑ s ∈ S, act s b = a) (c : G → C)
    (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h)) (t ε : ℝ) (ht : (0 : ℝ) ≤ t)
    (hε : (0 : ℝ) ≤ ε) (hct : ∀ g ∈ H, ‖c g‖ ≤ t) (hcε : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by
  classical
  refine ⟨-∑ s ∈ S, act s b * c s, ?_, ?_⟩
  · rw [norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ht
    intro s hs
    rw [norm_mul, hn]
    calc ‖b‖ * ‖c s‖ ≤ 1 * t := mul_le_mul hb (hct s (hS s hs)) (norm_nonneg _) zero_le_one
      _ = t := one_mul t
  · intro h hh
    obtain ⟨σ, hσ, hsum⟩ := exists_perm (C := C) H V S hS hT h hh
    have hmul : ∀ (g k : G) (y : C), act (g * k) y = act g (act k y) := by
      intro g k y
      rw [map_mul]
      rfl

    have hterm : ∀ s ∈ S, act h (act s b * c s) = act (σ s) b * c (σ s)
        + act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - act (σ s) b * c h := by
      intro s hs
      have hsH := hS s hs
      have hσH := hS (σ s) (hσ s hs).1
      have hvV := (hσ s hs).2
      have hhs : h * s = σ s * ((σ s)⁻¹ * (h * s)) := (mul_inv_cancel_left _ _).symm
      have hvH : (σ s)⁻¹ * (h * s) ∈ H := H.mul_mem (H.inv_mem hσH) (H.mul_mem hh hsH)
      have h1 : act h (act s b) = act (σ s) b := by
        rw [← hmul, hhs, hmul, hV _ hvV]
      have h2 : act h (c s) = c (σ s) + act (σ s) (c ((σ s)⁻¹ * (h * s))) - c h := by
        have e1 := hc h hh s hsH
        have e2 := hc (σ s) hσH _ hvH
        rw [← hhs] at e2
        linear_combination e2 - e1
      rw [map_mul, h1, h2, map_mul (act (σ s)) b (c ((σ s)⁻¹ * (h * s)))]
      ring
    have hsumA : ∑ s ∈ S, act (σ s) b = a := by
      rw [← ha]
      exact hsum (fun g => act g b)
    have hsumT : ∑ s ∈ S, act (σ s) b * c (σ s) = ∑ s ∈ S, act s b * c s :=
      hsum (fun g => act g b * c g)
    have hact : act h (-∑ s ∈ S, act s b * c s) = -(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_neg, map_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hsumT, ← Finset.sum_mul, hsumA]
    rw [hact]
    have hE : a * c h - (-(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h)
        - -∑ s ∈ S, act s b * c s) = ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) := by
      ring
    rw [hE]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε
    intro s hs
    rw [hn, norm_mul]
    have hvH : (σ s)⁻¹ * (h * s) ∈ H :=
      H.mul_mem (H.inv_mem (hS _ (hσ s hs).1)) (H.mul_mem hh (hS s hs))
    calc ‖b‖ * ‖c ((σ s)⁻¹ * (h * s))‖ ≤ 1 * ε :=
          mul_le_mul hb (hcε _ hvH (hσ s hs).2) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

end GlobalTheory.PermutationExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTail
section
namespace GlobalTheory.NonzeroScalarMembership

theorem exists_ne_zero_smul_mem {O LL V : Type} [CommRing O] [IsDomain O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V)
    (hT : Submodule.span LL (↑T : Set V) = ⊤) (x : V) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ T := by
  have hx : x ∈ Submodule.span LL (↑T : Set V) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem b hay
    · rw [mul_smul]
      exact T.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hq : (q : O) ≠ 0 := nonZeroDivisors.coe_ne_zero q
    refine ⟨q * a, mul_ne_zero hq ha, ?_⟩
    have h : ((q : O) * a) • c • y = p • a • y := by
      have h1 : (q : O) • c • y = p • y := by
        rw [← algebraMap_smul LL (q : O), smul_smul, mul_comm, hpq, algebraMap_smul]
      rw [mul_comm, mul_smul, h1, smul_comm]
    rw [h]
    exact T.smul_mem p hay

end GlobalTheory.NonzeroScalarMembership
end

