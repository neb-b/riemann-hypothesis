module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0023
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnique
section
open Module CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUniq

theorem eq_of_unit_smul_combination {K B V M : Type*} [Field K] [CommRing B] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup M] [Module B M]
    (o : K →+* B) (μ : V → M) (c : B) (hc : IsUnit c)
    (hind : ∀ (m : ℕ) (bs : Basis (Fin m) K V) (g : Fin m → B),
      ∑ s, g s • μ (bs s) = 0 → ∀ s, g s = 0)
    (f f' : Dual K V →+ B)
    (hf : ∀ (k : K) (φ : Dual K V), f (k • φ) = o k * f φ)
    (hf' : ∀ (k : K) (φ : Dual K V), f' (k • φ) = o k * f' φ)
    (h : ∀ (m : ℕ) (bs : Basis (Fin m) K V),
      c • ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0) :
    f = f' := by
  classical
  let bs := Module.finBasis K V
  have h0 : ∑ s, (f (bs.coord s) - f' (bs.coord s)) • μ (bs s) = 0 := by
    obtain ⟨u, rfl⟩ := hc
    have := congrArg (fun x => ((u⁻¹ : Bˣ) : B) • x) (h _ bs)
    simpa [smul_smul] using this
  have hco : ∀ s, f (bs.coord s) = f' (bs.coord s) :=
    fun s => sub_eq_zero.mp (hind _ bs _ h0 s)
  have key : ∀ F : Dual K V →+ B, (∀ (k : K) (φ : Dual K V), F (k • φ) = o k * F φ) →
      ∀ φ : Dual K V, F φ = ∑ s, F (bs.coord s) * o (φ (bs s)) := by
    intro F hF φ
    have e : ∑ s, φ (bs s) • bs.coord s = φ := bs.sum_dual_apply_smul_coord φ
    calc F φ = F (∑ s, φ (bs s) • bs.coord s) := by rw [e]
      _ = _ := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_congr rfl fun s _ => by rw [hF, mul_comm]
  ext φ
  rw [key f hf, key f' hf']
  exact Finset.sum_congr rfl fun s _ => by rw [hco]

theorem rho_unique {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j)
    (f f' : Module.Dual K (C.V j) →+ B) : C.Rho x f → C.Rho x f' → f = f' := by
  rintro ⟨hfs, e, z, hz, hzb⟩ ⟨hfs', e', z', hz', hzb'⟩
  haveI := hC.fin j
  have hw : C.b j (((C.ℓ : A) ^ e) • z' - ((C.ℓ : A) ^ e') • z) = 0 := by
    apply hC.sep
    intro n
    rw [map_sub, map_smul, map_smul, hz n, hz' n, smul_smul, smul_smul, mul_comm, sub_self]
  have hb : ∀ (a : A) (y : C.Z j), C.b j (a • y) = C.ι a • C.b j y :=
    fun a y => (C.b j).map_smulₛₗ a y
  refine (eq_of_unit_smul_combination C.o (C.μ j) ((C.ℓ : B) ^ (e + e')) (hC.unit.pow _) ?_
    f' f hfs' hfs ?_).symm
  · intro m bs g hg s
    obtain ⟨g0, _, hu⟩ := hC.basis j bs 0
    have h1 := hu g hg.symm
    have h2 := hu 0 (by simp)
    exact congrFun (h1.trans h2.symm) s
  · intro m bs
    have h := hw
    rw [map_sub, hb, hb, ← hzb bs, ← hzb' bs] at h
    simp only [map_pow, map_natCast, smul_smul] at h
    simp_rw [sub_smul, Finset.sum_sub_distrib, smul_sub]
    rw [← h, pow_add, mul_comm ((C.ℓ : B) ^ e') ((C.ℓ : B) ^ e)]

end GlobalTheory.CompanionTheory.KapUniq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClass
section
open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapUnit

theorem rho_one_eval : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) (P : Cup C), P.Good → ∀ h : Module.Dual K (C.V 0) →+ B, C.Rho P.oneS h → ∀ φ : Module.Dual K (C.V 0), h φ = C.o (φ P.oneV) := by
  intro Λ A B K _ _ _ _ C hC P hP h hR φ
  obtain ⟨hsem, e, z, hz, hb⟩ := hR
  have hw : C.b 0 z = ((C.ℓ : B) ^ e) • C.μ 0 P.oneV := by
    have h0 : C.b 0 (z - ((C.ℓ : A) ^ e) • P.oneZ) = 0 := hC.sep 0 _ (fun n => by
      rw [map_sub, map_smul, hP.one_r, hz, sub_self])
    rw [map_sub, map_smulₛₗ, hP.one_b, sub_eq_zero] at h0
    rw [h0]
    simp
  haveI := hC.fin 0
  let bs := Module.finBasis K (C.V 0)
  have h1 := hb bs
  rw [hw] at h1
  have h2 : ∑ s, h (bs.coord s) • C.μ 0 (bs s) = C.μ 0 P.oneV := by
    obtain ⟨u, hu⟩ := hC.unit.pow e
    rw [← hu] at h1
    have h1' := congrArg (fun w => ((u⁻¹ : Bˣ) : B) • w) h1
    simpa only [smul_smul, Units.inv_mul, one_smul] using h1'
  have h3 : C.μ 0 P.oneV = ∑ s, C.o (bs.coord s P.oneV) • C.μ 0 (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smulₛₗ]
    rfl
  have h4 : (fun s => h (bs.coord s)) = fun s => C.o (bs.coord s P.oneV) :=
    (hC.basis 0 bs (C.μ 0 P.oneV)).unique h2.symm h3
  have h5 : φ = ∑ s, φ (bs s) • bs.coord s := by
    refine bs.ext fun t => ?_
    simp [Finset.sum_apply, Module.Basis.coord_apply, Finsupp.single_apply]
  have h6 : φ P.oneV = ∑ s, bs.coord s P.oneV * φ (bs s) := by
    conv_lhs => rw [← bs.sum_repr P.oneV]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h6, map_sum]
  conv_lhs => rw [h5]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hsem, map_mul, mul_comm]
  exact congrArg (· * C.o (φ (bs s))) (congrFun h4 s)

end GlobalTheory.CompanionTheory.KapUnit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularizedExponentialSum
section
open Filter Topology
open scoped Classical

namespace GlobalTheory.CompanionTheory.ExpSums

theorem tendsto_one_add_pow_mul_pow {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) (N : ℕ) :
    Tendsto (fun n : ℕ => (1 + (n : ℝ)) ^ N * t ^ n) atTop (𝓝 0) := by
  have ht : |t| < 1 := by rw [abs_of_nonneg h0]; exact h1
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n)) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_mul_const_pow_of_abs_lt_one N ht).const_mul ((2 : ℝ) ^ N)
    rwa [mul_zero] at h
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => mul_nonneg (by positivity) (pow_nonneg h0 n)) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : (1 + (n : ℝ)) ^ N ≤ (2 * (n : ℝ)) ^ N := by
    gcongr
    linarith
  calc (1 + (n : ℝ)) ^ N * t ^ n ≤ (2 * (n : ℝ)) ^ N * t ^ n :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg h0 n)
    _ = (2 : ℝ) ^ N * ((n : ℝ) ^ N * t ^ n) := by ring

theorem expSum_holds : PositivityTheory.Rg.BcB.F.ExpSum := by
  intro ι _ c lam ρ C N hρ hbound μ hμ
  obtain ⟨d, hd⟩ : ∃ d : ℂ → ℂ, ∀ ν, d ν = ∑ i with lam i = ν, c i := ⟨_, fun _ => rfl⟩
  rw [← hd]
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, S = Finset.univ.image lam := ⟨_, rfl⟩
  by_cases hμS : μ ∉ S
  · rw [hd]
    refine Finset.sum_eq_zero fun i hi => absurd ?_ hμS
    rw [hS, ← (Finset.mem_filter.mp hi).2]
    exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  push_neg at hμS
  have hmaps : ∀ i ∈ (Finset.univ : Finset ι), lam i ∈ S := fun i _ => by
    rw [hS]; exact Finset.mem_image_of_mem lam (Finset.mem_univ i)
  have hsum : ∀ k : ℕ, ∑ i, c i * lam i ^ k = ∑ ν ∈ S, d ν * ν ^ k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hd, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  obtain ⟨e, -⟩ : ∃ e : Fin S.card ≃ S, e = S.equivFin.symm := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : Fin S.card → ℂ, ∀ k, α k = (e k : ℂ) := ⟨_, fun _ => rfl⟩
  have hinj : Function.Injective α := by
    intro a b hab
    rw [hα, hα] at hab
    exact e.injective (Subtype.val_injective hab)
  have hpow : ∀ n : ℕ, ∑ k, d (α k) * α k ^ n = ∑ i, c i * lam i ^ n := by
    intro n
    rw [hsum n]
    simp only [hα]
    exact (Equiv.sum_comp e (fun x : S => d x * (x : ℂ) ^ n)).trans
      (Finset.sum_coe_sort S (fun ν => d ν * ν ^ n))
  obtain ⟨C', hC'⟩ := GlobalTheory.CompanionTheory.ExpSums.vandermonde_separation S.card α hinj
  obtain ⟨C1, hC1, hC'1⟩ : ∃ C1 : ℝ, 0 ≤ C1 ∧ C' ≤ C1 := ⟨max C' 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨C2, hC2, hCC2⟩ : ∃ C2 : ℝ, 0 ≤ C2 ∧ C ≤ C2 := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ s : Fin S.card, (1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ) := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hbound
  have hK0' : ∀ k : ℕ, K0 ≤ k → ‖∑ i, c i * lam i ^ k‖ ≤ C2 * (1 + (k : ℝ)) ^ N * ρ ^ k := by
    intro k hk
    refine (hK0 k hk).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC2 (pow_nonneg (by positivity) N)) (pow_nonneg hρ k)
  obtain ⟨j, hj⟩ : ∃ j : Fin S.card, α j = μ := ⟨e.symm ⟨μ, hμS⟩, by rw [hα, Equiv.apply_symm_apply]⟩
  have key : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ * ‖μ‖ ^ m ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := by
    intro m hm
    have h1 := hC' (fun k => d (α k) * α k ^ m) j
    have hinner : ∀ s : Fin S.card,
        ∑ k, d (α k) * α k ^ m * α k ^ (s : ℕ) = ∑ i, c i * lam i ^ (m + (s : ℕ)) := by
      intro s
      rw [← hpow (m + (s : ℕ))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_add]
      ring
    simp only [hinner, hj, norm_mul, norm_pow] at h1
    have hT : 0 ≤ ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsb : ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ ≤
        C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B := by
      rw [hB, Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      have hk := hK0' (m + (s : ℕ)) (le_trans hm (Nat.le_add_right m _))
      rw [Nat.cast_add] at hk
      have hbase : 1 + ((m : ℝ) + ((s : ℕ) : ℝ)) ≤ (1 + (m : ℝ)) * (1 + ((s : ℕ) : ℝ)) := by
        have hms : (0 : ℝ) ≤ (m : ℝ) * ((s : ℕ) : ℝ) := by positivity
        nlinarith
      have hle : (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N ≤ (1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) hbase N
      calc ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖
          ≤ C2 * (1 + ((m : ℝ) + ((s : ℕ) : ℝ))) ^ N * ρ ^ (m + (s : ℕ)) := hk
        _ ≤ C2 * ((1 + (m : ℝ)) ^ N * (1 + ((s : ℕ) : ℝ)) ^ N) * ρ ^ (m + (s : ℕ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hC2) (pow_nonneg hρ _)
        _ = C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * ((1 + ((s : ℕ) : ℝ)) ^ N * ρ ^ (s : ℕ)) := by
          rw [pow_add]
          ring
    calc ‖d μ‖ * ‖μ‖ ^ m ≤ C' * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ := h1
      _ ≤ C1 * ∑ s : Fin S.card, ‖∑ i, c i * lam i ^ (m + (s : ℕ))‖ :=
        mul_le_mul_of_nonneg_right hC'1 hT
      _ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) := mul_le_mul_of_nonneg_left hsb hC1
  have hμpos : 0 < ‖μ‖ := lt_of_le_of_lt hρ hμ
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ρ / ‖μ‖ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg hρ (norm_nonneg _)
  have ht1 : t < 1 := by rw [ht, div_lt_one hμpos]; exact hμ
  have hlim := (tendsto_one_add_pow_mul_pow ht0 ht1 N).const_mul (C1 * (C2 * B))
  rw [mul_zero] at hlim
  have hle : ∀ m : ℕ, K0 ≤ m → ‖d μ‖ ≤ C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * t ^ m) := by
    intro m hm
    have h := (le_div_iff₀ (pow_pos hμpos m)).mpr (key m hm)
    rw [ht, div_pow]
    calc ‖d μ‖ ≤ C1 * (C2 * (1 + (m : ℝ)) ^ N * ρ ^ m * B) / ‖μ‖ ^ m := h
      _ = C1 * (C2 * B) * ((1 + (m : ℝ)) ^ N * (ρ ^ m / ‖μ‖ ^ m)) := by ring
  have h0 : ‖d μ‖ ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨K0, hle⟩)
  exact norm_le_zero_iff.mp h0

end GlobalTheory.CompanionTheory.ExpSums
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RemoveNthSuccVecCons
section
open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.KDelFormula

variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]

theorem removeNth_succ_vecCons {n : ℕ} (x : P) (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    t.succ.removeNth (Matrix.vecCons x Y) = Matrix.vecCons x (t.removeNth Y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

theorem map_vecCons_removeNth {n : ℕ} (η : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (x : P)
    (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    η (Matrix.vecCons x (t.removeNth Y)) = (-1 : ℤ) ^ (t : ℕ) • η (Function.update Y t x) := by
  have hW : Matrix.vecCons x (t.removeNth Y) = Function.update Y t x ∘ t.cycleRange.symm := by
    rw [← Fin.cons_removeNth_eq_comp_cycleRange_symm]
    simp only [Function.update_self, Fin.removeNth_update]
    rfl
  rw [hW, η.map_perm, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Units.smul_def]
  push_cast
  rfl

theorem kD_vecCons (T : P →ₗ[ℝ] Module.End ℂ M) {q : ℕ} (η : P [⋀^Fin q]→ₗ[ℝ] M) (x : P)
    (Y : Fin q → P) :
    kD T η (Matrix.vecCons x Y) =
      T x (η Y) - ∑ t, T (Y t) (η (Function.update Y t x)) := by
  have hs : ∀ t : ℕ, ((-1 : ℤ) ^ (t + 1) * (-1) ^ t) = -1 := fun t => by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨t, by ring⟩
  cases q with
  | zero =>
    rw [kD_apply, Fin.sum_univ_succ]
    simp [Fin.removeNth_zero]
  | succ n =>
    rw [kD_apply, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · simp [Fin.removeNth_zero]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fin.val_succ, Matrix.cons_val_succ, removeNth_succ_vecCons, map_vecCons_removeNth,
        map_zsmul, smul_smul, hs, neg_one_zsmul]

theorem kDel_kD {β : Type} [Fintype β] (T T' : P →ₗ[ℝ] Module.End ℂ M) (b : β → P) {q : ℕ}
    (η : P [⋀^Fin q]→ₗ[ℝ] M) (Y : Fin q → P) :
    kDel T' b (kD T η) Y = ∑ i, T' (b i) (T (b i) (η Y)) -
      ∑ t, ∑ i, T' (b i) (T (Y t) (η (Function.update Y t (b i)))) := by
  rw [kDel_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [kD_vecCons, map_sub, map_sum, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.KDelFormula
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
section
open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens

def barσ {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) :
    R ⧸ lev ϖ k →+* R ⧸ lev ϖ k :=
  Ideal.Quotient.lift (lev ϖ k) ((Ideal.Quotient.mk (lev ϖ k)).comp σ) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, h]
    apply Ideal.Quotient.eq_zero_iff_mem.2
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

@[simp] theorem barσ_mk {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) (a : R) :
    barσ σ ϖ h k (Ideal.Quotient.mk (lev ϖ k) a) = Ideal.Quotient.mk (lev ϖ k) (σ a) := rfl

structure ResAlg (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ) : Prop where
  inv : ∀ a, τ (τ a) = a
  fixedUnit : ∀ a, τ a = a → a ≠ 0 → IsUnit a
  basis : ∃ u : E, IsUnit (u - τ u) ∧ ∀ a, ∃ x y, τ x = x ∧ τ y = y ∧ a = x + y * u
  one_lt : 1 < q
  card : Nat.card E = q ^ 2
  eps : (ε = -1 ∧ IsField E) ∨ (ε = 1 ∧ ¬ IsField E)

variable {E : Type} [CommRing E] {τ : E →+* E}

structure HermSp (E : Type) [CommRing E] (τ : E →+* E) (V : Type) [AddCommGroup V] [Module E V] where
  h : V → V → E
  add_left : ∀ u v w, h (u + v) w = h u w + h v w
  smul_left : ∀ (a : E) v w, h (a • v) w = a * h v w
  symm : ∀ v w, h w v = τ (h v w)
  nondeg : ∀ v, (∀ w, h v w = 0) → v = 0

variable {V : Type} [AddCommGroup V] [Module E V]

namespace HermSp

variable (B : HermSp E τ V)

theorem zero_left (w : V) : B.h 0 w = 0 := by
  have h0 := B.smul_left 0 0 w
  rwa [zero_smul, zero_mul] at h0

theorem add_right (v u w : V) : B.h v (u + w) = B.h v u + B.h v w := by
  rw [B.symm (u + w) v, B.add_left, map_add (f := _), ← B.symm, ← B.symm]

theorem smul_right (a : E) (v w : V) : B.h v (a • w) = τ a * B.h v w := by
  rw [B.symm (a • w) v, B.smul_left, map_mul, ← B.symm]

theorem self_fixed (hτ : ∀ a, τ (τ a) = a) (v : V) : τ (B.h v v) = B.h v v := by
  exact (B.symm v v).symm

def perp (w : V) : Submodule E V where
  carrier := {v | B.h v w = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [B.add_left, ha, hb, add_zero]
  zero_mem' := B.zero_left w
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [B.smul_left, hx, mul_zero]

noncomputable def coef {w : V} (hw : IsUnit (B.h w w)) (z : V) : E := B.h z w * (hw.unit⁻¹ : Eˣ)

theorem coef_spec {w : V} (hw : IsUnit (B.h w w)) (z : V) : B.h (z - B.coef hw z • w) w = 0 := by
  have hu : ((hw.unit⁻¹ : Eˣ) : E) * B.h w w = 1 := by
    have h1 := hw.unit.inv_mul
    simpa using h1
  have hc : B.coef hw z * B.h w w = B.h z w := by
    unfold coef
    rw [mul_assoc, hu, mul_one]
  have e : B.h z w = B.h (z - B.coef hw z • w) w + B.h (B.coef hw z • w) w := by
    rw [← B.add_left, sub_add_cancel]
  rw [B.smul_left, hc] at e
  linear_combination -e

noncomputable def perpForm {w : V} (hw : IsUnit (B.h w w)) : HermSp E τ (B.perp w) where
  h a b := B.h a b
  add_left u v x := by simp [B.add_left]
  smul_left a v x := by simp [B.smul_left]
  symm v x := B.symm _ _
  nondeg := by
    intro v hv
    apply Subtype.ext
    apply B.nondeg
    intro z
    have h1 := hv ⟨z - B.coef hw z • w, B.coef_spec hw z⟩
    have hz : z = (z - B.coef hw z • w) + B.coef hw z • w := by abel
    have h0 : B.h (v : V) w = 0 := v.2
    rw [hz, B.add_right, B.smul_right, h0, mul_zero, add_zero]
    exact h1

@[simp] theorem perpForm_h {w : V} (hw : IsUnit (B.h w w)) (a b : B.perp w) :
    (B.perpForm hw).h a b = B.h a b := rfl

noncomputable def perpEquiv {w : V} (hw : IsUnit (B.h w w)) : E × B.perp w ≃ V where
  toFun p := p.1 • w + p.2
  invFun z := (B.coef hw z, ⟨z - B.coef hw z • w, B.coef_spec hw z⟩)
  left_inv := by
    rintro ⟨a, v⟩
    have h0 : B.h (v : V) w = 0 := v.2
    have hc : B.coef hw (a • w + (v : V)) = a := by
      unfold coef
      rw [B.add_left, B.smul_left, h0, add_zero, mul_assoc]
      have : B.h w w * ((hw.unit⁻¹ : Eˣ) : E) = 1 := by
        have := hw.unit.mul_inv
        simpa using this
      rw [this, mul_one]
    ext
    · exact hc
    · simp [hc]
  right_inv := by
    intro z
    simp

theorem perpEquiv_apply {w : V} (hw : IsUnit (B.h w w)) (p : E × B.perp w) :
    B.perpEquiv hw p = p.1 • w + (p.2 : V) := rfl

theorem norm_perp {w v : V} (hv : B.h v w = 0) (a : E) :
    B.h (a • w + v) (a • w + v) = a * τ a * B.h w w + B.h v v := by
  have hwv : B.h w v = 0 := by rw [B.symm v w, hv, map_zero]
  simp only [B.add_left, B.smul_left, B.add_right, B.smul_right, hv, hwv, mul_zero, add_zero]
  ring

end HermSp

def HermSp.ofMatrix (hτ : ∀ a, τ (τ a) = a) {m : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) : HermSp E τ (Fin m → E) where
  h v w := dotProduct (fun i => τ (w i)) (S.mulVec v)
  add_left u v w := by rw [Matrix.mulVec_add, dotProduct_add]
  smul_left a v w := by rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  symm v w := by
    have hij : ∀ i j, τ (S j i) = S i j := fun i j => by
      have := congrFun (congrFun hS i) j
      simpa [cT] using this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hτ, hij]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  nondeg v hv := by
    have h0 : S.mulVec v = 0 := by
      funext i
      have := hv (Pi.single i 1)
      simpa [dotProduct, Pi.single_apply] using this
    have := congrArg (S⁻¹).mulVec h0
    have hu : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul _ hd
    simpa [Matrix.mulVec_mulVec, hu] using this

theorem gram_apply (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) (x : Matrix (Fin m) (Fin n) E) (i j : Fin n) :
    (cT τ x * S * x) i j = (HermSp.ofMatrix hτ S hS hd).h (fun a => x a j) (fun a => x a i) := by
  show (cT τ x * S * x) i j = dotProduct (fun a => τ (x a i)) (S.mulVec (fun a => x a j))
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.CompanionTheory.UnrDens
end

