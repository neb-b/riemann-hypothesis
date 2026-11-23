module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0047
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanSubMemSq
section
namespace GlobalTheory.PowerIdealSurjectivity

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

lemma exists_span_sub_mem_sq (ε : A →ₐ[O] O) {d : ℕ} (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) {c : A}
    (hc : c ∈ RingHom.ker ε) :
    ∃ m ∈ Submodule.span O (Set.range x), m ∈ RingHom.ker ε ∧ c - m ∈ RingHom.ker ε ^ 2 := by
  classical

  let J : Submodule O A := (RingHom.ker ε ^ 2).restrictScalars O
  let D : A →ₗ[O] A ⧸ J := J.mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap O A) ∘ₗ ε.toLinearMap)
  have hDa : ∀ a, D a = Submodule.Quotient.mk (a - algebraMap O A (ε a)) := fun a => rfl
  have hmemI : ∀ a, a - algebraMap O A (ε a) ∈ RingHom.ker ε := fun a =>
    RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)
  have hD : ∀ a b : A, D (a * b) = ε a • D b + ε b • D a := by
    intro a b
    rw [hDa, hDa, hDa, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, Submodule.restrictScalars_mem]
    have key : a * b - algebraMap O A (ε (a * b)) -
        (ε a • (b - algebraMap O A (ε b)) + ε b • (a - algebraMap O A (ε a))) =
        (a - algebraMap O A (ε a)) * (b - algebraMap O A (ε b)) := by
      rw [map_mul, Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    rw [key, pow_two]
    exact Ideal.mul_mem_mul (hmemI a) (hmemI b)
  have hdc : GlobalTheory.AugCot.d ε c ∈ Submodule.span O (Set.range fun i => GlobalTheory.AugCot.d ε (x i)) := by
    rw [hs]
    exact Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp hdc
  have hε0 : ε (∑ i, r i • x i) = 0 := by simp [map_sum, hx]
  refine ⟨∑ i, r i • x i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩),
    RingHom.mem_ker.mpr hε0, ?_⟩
  have hdm : GlobalTheory.AugCot.d ε (∑ i, r i • x i) = GlobalTheory.AugCot.d ε c := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hr, map_sum]
    simp only [map_smul]
  have h := congrArg (GlobalTheory.AugCot.lift ε D hD) hdm
  rw [GlobalTheory.AugCot.lift_d, GlobalTheory.AugCot.lift_d, hDa, hDa, Submodule.Quotient.eq,
    Submodule.restrictScalars_mem] at h
  have hεc : ε c = 0 := RingHom.mem_ker.mp hc
  rw [hε0, hεc, map_zero, sub_zero, sub_zero] at h
  rw [← neg_sub]
  exact (RingHom.ker ε ^ 2).neg_mem h

lemma exists_sub_mem_pow (B : Subalgebra O A) (I : Ideal A)
    (h0 : ∀ a, ∃ b ∈ B, a - b ∈ I) (h1 : ∀ c ∈ I, ∃ m ∈ B, m ∈ I ∧ c - m ∈ I ^ 2) (n : ℕ) (a : A) :
    ∃ b ∈ B, a - b ∈ I ^ (n + 1) := by

  have step : ∀ k : ℕ, ∀ c ∈ I ^ (k + 1), ∃ m ∈ B, m ∈ I ^ (k + 1) ∧ c - m ∈ I ^ (k + 2) := by
    intro k
    induction k with
    | zero =>
      intro c hc
      rw [zero_add, pow_one] at hc
      obtain ⟨m, hmB, hmI, hcm⟩ := h1 c hc
      exact ⟨m, hmB, by rwa [zero_add, pow_one], hcm⟩
    | succ k ih =>
      intro c hc
      have hc' : c ∈ I ^ (k + 1) * I := by rw [← pow_succ]; exact hc
      refine Submodule.mul_induction_on
        (C := fun c => ∃ m ∈ B, m ∈ I ^ (k + 1 + 1) ∧ c - m ∈ I ^ (k + 1 + 2)) hc' ?_ ?_
      · intro y hy z hz
        obtain ⟨my, hmyB, hmyI, hy'⟩ := ih y hy
        obtain ⟨mz, hmzB, hmzI, hz'⟩ := h1 z hz
        refine ⟨my * mz, B.mul_mem hmyB hmzB, ?_, ?_⟩
        · rw [pow_succ]
          exact Ideal.mul_mem_mul hmyI hmzI
        · have e : y * z - my * mz = y * (z - mz) + (y - my) * mz := by ring
          rw [e]
          refine Ideal.add_mem _ ?_ ?_
          · have := Ideal.mul_mem_mul hy hz'
            rwa [← pow_add] at this
          · have := Ideal.mul_mem_mul hy' hmzI
            rwa [← pow_succ] at this
      · rintro y z ⟨my, hmyB, hmyI, hy'⟩ ⟨mz, hmzB, hmzI, hz'⟩
        refine ⟨my + mz, B.add_mem hmyB hmzB, Ideal.add_mem _ hmyI hmzI, ?_⟩
        have e : y + z - (my + mz) = (y - my) + (z - mz) := by ring
        rw [e]
        exact Ideal.add_mem _ hy' hz'
  induction n with
  | zero =>
    obtain ⟨b, hb, hab⟩ := h0 a
    exact ⟨b, hb, by rwa [zero_add, pow_one]⟩
  | succ n ih =>
    obtain ⟨b, hb, hab⟩ := ih
    obtain ⟨m, hmB, -, hm⟩ := step n (a - b) hab
    refine ⟨b + m, B.add_mem hb hmB, ?_⟩
    have e : a - (b + m) = a - b - m := by ring
    rw [e]
    exact hm

theorem aeval_surjective (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Module.Finite O A] [IsLocalRing A] (q : O) (hq : q ∈ IsLocalRing.maximalIdeal O)
    (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hN : ∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) :
    Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O → A) := by
  classical
  let B : Subalgebra O A := Algebra.adjoin O (Set.range x)
  have h0 : ∀ a, ∃ b ∈ B, a - b ∈ RingHom.ker ε := fun a =>
    ⟨algebraMap O A (ε a), B.algebraMap_mem _,
      RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)⟩
  have h1 : ∀ c ∈ RingHom.ker ε, ∃ m ∈ B, m ∈ RingHom.ker ε ∧ c - m ∈ RingHom.ker ε ^ 2 := by
    intro c hc
    obtain ⟨m, hm, hmI, hcm⟩ := exists_span_sub_mem_sq ε x hx hs hc
    exact ⟨m, Algebra.span_le_adjoin O _ hm, hmI, hcm⟩

  let φ : A →ₗ[O] A := LinearMap.id - (Algebra.linearMap O A) ∘ₗ ε.toLinearMap
  have hφ : ∀ a, φ a = a - algebraMap O A (ε a) := fun a => rfl
  have hfg : (RingHom.ker ε).FG := by
    apply Submodule.FG.of_restrictScalars O
    have heq : (RingHom.ker ε).restrictScalars O = LinearMap.range φ := by
      ext c
      rw [Submodule.restrictScalars_mem, LinearMap.mem_range]
      constructor
      · intro hc
        refine ⟨c, ?_⟩
        rw [hφ, show ε c = 0 from RingHom.mem_ker.mp hc, map_zero, sub_zero]
      · rintro ⟨a, rfl⟩
        rw [hφ]
        exact RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)
    rw [heq, ← Submodule.map_top]
    exact (Module.Finite.fg_top (R := O) (M := A)).map φ

  have hker_ne : RingHom.ker ε ≠ ⊤ := RingHom.ker_ne_top ε
  have hle_span : RingHom.ker ε ≤ Ideal.span (Set.range x) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := RingHom.ker ε) hfg ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hker_ne
    · intro c hc
      obtain ⟨m, hm, -, hcm⟩ := exists_span_sub_mem_sq ε x hx hs hc
      have hm' : m ∈ Ideal.span (Set.range x) := Submodule.span_le_restrictScalars O A _ hm
      rw [pow_two, ← smul_eq_mul] at hcm
      rw [show c = m + (c - m) by ring]
      exact Submodule.add_mem_sup hm' hcm

  have hrad : Ideal.span (Set.range x) ≤ (Ideal.span {algebraMap O A q}).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨N, hNi⟩ := hN i
    exact ⟨N, Ideal.mem_span_singleton.mpr hNi⟩
  have hfgx : (Ideal.span (Set.range x)).FG :=
    ⟨Finset.univ.image x, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  obtain ⟨K, hK⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfgx

  have htop : (⊤ : Submodule O A) ≤ Subalgebra.toSubmodule B := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
      Module.Finite.fg_top ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro a _
      obtain ⟨b, hb, hab⟩ := exists_sub_mem_pow B (RingHom.ker ε) h0 h1 K a
      have h2 : a - b ∈ Ideal.span (Set.range x) ^ K :=
        Ideal.pow_right_mono hle_span K (Ideal.pow_le_pow_right (Nat.le_succ K) hab)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hK h2)
      have h3 : a - b ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O A) := by
        rw [← hy, mul_comm, ← Algebra.smul_def]
        exact Submodule.smul_mem_smul hq Submodule.mem_top
      rw [show a = b + (a - b) by ring]
      exact Submodule.add_mem_sup hb h3
  intro a
  have ha : a ∈ B := htop Submodule.mem_top
  rw [show B = (MvPolynomial.aeval x).range from Algebra.adjoin_range_eq_range_aeval O x] at ha
  obtain ⟨p, hp⟩ := ha
  exact ⟨p, hp⟩

end GlobalTheory.PowerIdealSurjectivity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubMemMaximalIdealPointedEtaleNeighbourhoo
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.exists_sub_mem_maximalIdeal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (b : i.B),
      ∃ r : R, b - algebraMap R i.B r ∈ maximalIdeal i.B := by
  intro R _ _ i b
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective i.q.primeCompl b
  obtain ⟨r₁, hr₁⟩ := residue_surjective (i.pt a)
  obtain ⟨r₂, hr₂⟩ := residue_surjective (i.pt (s : i.A))
  have hs : i.pt (s : i.A) ≠ 0 := by
    intro h
    exact s.2 (show (s : i.A) ∈ RingHom.ker i.pt from h)
  have hu : IsUnit r₂ := by
    by_contra hn
    apply hs
    rw [← hr₂]
    exact (residue_eq_zero_iff r₂).2 hn
  obtain ⟨u, rfl⟩ := hu
  refine ⟨r₁ * ((u⁻¹ : Rˣ) : R), ?_⟩
  have key : IsLocalization.mk' i.B a s - algebraMap R i.B (r₁ * ((u⁻¹ : Rˣ) : R)) =
      IsLocalization.mk' i.B (a - (s : i.A) * algebraMap R i.A (r₁ * ((u⁻¹ : Rˣ) : R))) s := by
    rw [IsLocalization.eq_mk'_iff_mul_eq, sub_mul, IsLocalization.mk'_spec,
      (algebraMap i.A i.B).map_sub, (algebraMap i.A i.B).map_mul,
      ← IsScalarTower.algebraMap_apply R i.A i.B]
    ring
  rw [key, IsLocalization.AtPrime.mk'_mem_maximal_iff (S := i.B) (I := i.q)]
  show _ ∈ RingHom.ker i.pt
  rw [RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, ← hr₁, ← hr₂]
  rw [show algebraMap R (ResidueField R) = residue R from rfl, ← map_mul, ← map_sub]
  rw [residue_eq_zero_iff]
  have : r₁ - (u : R) * (r₁ * ((u⁻¹ : Rˣ) : R)) = 0 := by
    rw [mul_left_comm, Units.mul_inv, mul_one, sub_self]
  rw [this]
  exact zero_mem _

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupAddCharDotProductTrivialOnCompact
section
open Matrix

namespace GlobalTheory.CharDotKill

theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.KeyLemmaTwo.main
  | exact _root_.GlobalTheory.KeyLemmaTwo.main
  | (apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.KeyLemmaTwo.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KeyLemmaTwo.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KeyLemmaTwo.main ..)

theorem exists_open_ker {K : Type} [AddCommGroup K] [TopologicalSpace K] [NonarchimedeanAddGroup K]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) : ∃ U : OpenAddSubgroup K, ∀ t ∈ U, ψ t = 1 := by
  have hV : {t : K | ‖ψ t - 1‖ < 1 / 2} ∈ nhds (0 : K) :=
    (isOpen_lt (hψ.sub continuous_const).norm continuous_const).mem_nhds (by simp)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV
  refine ⟨V, fun t ht => pow_near_one fun n => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  exact hV (V.toAddSubgroup.nsmul_mem ht n)

theorem nonarchimedean_pi {κ K : Type} [Finite κ] [AddCommGroup K] [TopologicalSpace K]
    [NonarchimedeanAddGroup K] : NonarchimedeanAddGroup (κ → K) where
  is_nonarchimedean S hS := by
    rw [nhds_pi, Filter.mem_pi] at hS
    obtain ⟨I, -, t, ht, hsub⟩ := hS
    choose M hM using fun i => NonarchimedeanAddGroup.is_nonarchimedean _ (ht i)
    refine ⟨⟨AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup, ?_⟩, ?_⟩
    · change IsOpen ((AddSubgroup.pi Set.univ fun i => (M i).toAddSubgroup : AddSubgroup (κ → K)) : Set (κ → K))
      rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => (M i).isOpen
    · intro x hx
      apply hsub
      intro i _
      exact hM i (hx i (Set.mem_univ i))

theorem charDot_kill : ∀ {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [NonarchimedeanAddGroup K] (χ : AddChar K ℂ), Continuous χ → ∀ (κ : Type) [Fintype κ]
    (C : Set (κ → K)), IsCompact C → ∃ H : OpenAddSubgroup (κ → K),
      ∀ z ∈ C, ∀ a ∈ H, ∀ b ∈ H, χ (z ⬝ᵥ b + a ⬝ᵥ b) = 1 := by
  intro K _ _ _ _ χ hχ κ _ C hC
  obtain ⟨K₀, hK₀⟩ := exists_open_ker χ hχ
  have hdot : Continuous fun p : (κ → K) × (κ → K) => p.1 ⬝ᵥ p.2 :=
    continuous_fst.dotProduct continuous_snd
  have hO : IsOpen {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} :=
    K₀.isOpen.preimage hdot

  have hW : ∀ᶠ b in nhds (0 : κ → K), ∀ z ∈ C, z ⬝ᵥ b ∈ (K₀ : Set K) := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    have hO' : IsOpen {p : (κ → K) × (κ → K) | p.2 ⬝ᵥ p.1 ∈ (K₀ : Set K)} :=
      K₀.isOpen.preimage (continuous_snd.dotProduct continuous_fst)
    filter_upwards [hO'.mem_nhds (x := ((0 : κ → K), z)) (by simp [K₀.zero_mem])] with p hp
    exact hp

  have hP : {p : (κ → K) × (κ → K) | p.1 ⬝ᵥ p.2 ∈ (K₀ : Set K)} ∈ nhds ((0 : κ → K), (0 : κ → K)) :=
    hO.mem_nhds (by simp [K₀.zero_mem])
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hP
  obtain ⟨U, hU, V, hV, hUV⟩ := hP
  haveI : NonarchimedeanAddGroup (κ → K) := nonarchimedean_pi
  obtain ⟨H, hH⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (Filter.inter_mem (Filter.inter_mem hU hV) hW)
  refine ⟨H, fun z hz a ha b hb => hK₀ _ (K₀.add_mem ?_ ?_)⟩
  · exact (hH hb).2 z hz
  · exact hUV (Set.mk_mem_prod (hH ha).1.1 (hH hb).1.2)

end GlobalTheory.CharDotKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularPosDefAdjointAction
section
open Matrix Kronecker

namespace GlobalTheory

section
variable {n q : Type} [Fintype n] [DecidableEq n] [Fintype q] [DecidableEq q]

theorem zarhinBlock_real_posDef_det (B A : Matrix n n ℝ) (x : Matrix q q ℝ) (s : ℝ)
    (hB : B.PosDef) (hA : A = (1 + s) • B⁻¹) (hx : xᵀ * x = s • (1 : Matrix q q ℝ)) :
    (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) ((1 : Matrix n n ℝ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℝ))).PosDef ∧
      (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) ((1 : Matrix n n ℝ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℝ))).det = 1 := by
  have hdet : IsUnit B.det := hB.det_pos.ne'.isUnit
  have hK : (B ⊗ₖ (1 : Matrix q q ℝ)).PosDef := hB.kronecker PosDef.one
  have hKi : (B⁻¹ ⊗ₖ (1 : Matrix q q ℝ)).PosDef := hB.inv.kronecker PosDef.one
  letI := hK.isUnit.invertible
  have hinv : (B ⊗ₖ (1 : Matrix q q ℝ))⁻¹ = B⁻¹ ⊗ₖ (1 : Matrix q q ℝ) := by
    apply Matrix.inv_eq_left_inv
    rw [← mul_kronecker_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, one_kronecker_one]
  have hS : A ⊗ₖ (1 : Matrix q q ℝ) - ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) * (B ⊗ₖ (1 : Matrix q q ℝ))⁻¹ *
      ((1 : Matrix n n ℝ) ⊗ₖ x) = B⁻¹ ⊗ₖ (1 : Matrix q q ℝ) := by
    rw [hinv, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_one, hx, hA, kronecker_smul, smul_kronecker, add_smul, one_smul,
      add_sub_cancel_right]
  have hT : ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)ᴴ = (1 : Matrix n n ℝ) ⊗ₖ x := by
    rw [conjTranspose_eq_transpose_of_trivial, ← kroneckerMap_transpose, transpose_one,
      transpose_transpose]
  have hd : (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)
      ((1 : Matrix n n ℝ) ⊗ₖ x) (B ⊗ₖ (1 : Matrix q q ℝ))).det = 1 := by
    rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv, hS, ← det_mul, ← mul_kronecker_mul,
      Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, one_kronecker_one, det_one]
  refine ⟨?_, hd⟩
  have hps : (fromBlocks (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ)
      ((1 : Matrix n n ℝ) ⊗ₖ x) (B ⊗ₖ (1 : Matrix q q ℝ))).PosSemidef := by
    have := (PosDef.fromBlocks₂₂ (A ⊗ₖ (1 : Matrix q q ℝ)) ((1 : Matrix n n ℝ) ⊗ₖ xᵀ) hK).mpr
      (by rw [hT, hS]; exact hKi.posSemidef)
    rwa [hT] at this
  exact hps.posDef_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (by rw [hd]; exact isUnit_one))

def zarhinAction {R : Type} [CommRing R] (σ : R →+* R) (ρ0 : R →+* Matrix n n ℤ) :
    R →+* Matrix ((n × q) ⊕ (n × q)) ((n × q) ⊕ (n × q)) ℤ where
  toFun a := fromBlocks ((ρ0 (σ a))ᵀ ⊗ₖ (1 : Matrix q q ℤ)) 0 0 (ρ0 a ⊗ₖ (1 : Matrix q q ℤ))
  map_one' := by simp
  map_mul' a b := by
    rw [fromBlocks_multiply, mul_comm a b, map_mul σ, map_mul ρ0, transpose_mul, mul_comm b a,
      map_mul ρ0]
    simp [← mul_kronecker_mul]
  map_zero' := by simp
  map_add' a b := by
    simp [fromBlocks_add, add_kronecker, transpose_add]

theorem zarhinAction_adjoint {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a)
    (ρ0 : R →+* Matrix n n ℤ) (B A : Matrix n n ℤ) (x : Matrix q q ℤ)
    (hB : ∀ a, (ρ0 a)ᵀ * B = B * ρ0 (σ a)) (hA : ∀ a, ρ0 (σ a) * A = A * (ρ0 a)ᵀ) (a : R) :
    (zarhinAction (q := q) σ ρ0 a)ᵀ *
      fromBlocks (A ⊗ₖ (1 : Matrix q q ℤ)) ((1 : Matrix n n ℤ) ⊗ₖ xᵀ) ((1 : Matrix n n ℤ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℤ)) =
      fromBlocks (A ⊗ₖ (1 : Matrix q q ℤ)) ((1 : Matrix n n ℤ) ⊗ₖ xᵀ) ((1 : Matrix n n ℤ) ⊗ₖ x)
        (B ⊗ₖ (1 : Matrix q q ℤ)) * zarhinAction (q := q) σ ρ0 (σ a) := by
  simp only [zarhinAction, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, fromBlocks_transpose,
    fromBlocks_multiply, ← kroneckerMap_transpose, transpose_transpose, transpose_one,
    transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hσ]
  simp only [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hA, hB]

theorem mul_adjugate_eq_adjugate_mul_of_adjoint (B P Q : Matrix n n ℤ) (hd : B.det ≠ 0)
    (h : P * B = B * Q) : Q * B.adjugate = B.adjugate * P := by
  have h1 : B.adjugate * (P * B) * B.adjugate = B.adjugate * (B * Q) * B.adjugate := by rw [h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ B, mul_adjugate, adjugate_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at h1
  exact (smul_right_injective _ hd h1).symm

end

theorem exists_unimodular_posDef_adjoint_action (R : Type) [CommRing R] (σ : R →+* R)
    (hσ : ∀ a, σ (σ a) = a) (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ)
    (ρ0 : R →+* Matrix (Fin m) (Fin m) ℤ) (hm : 1 ≤ m) (hs : B0.transpose = B0)
    (hp : (B0.map (Int.cast : ℤ → ℝ)).PosDef)
    (hadj : ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (σ a)) :
    ∃ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℤ) (ρ : R →+* Matrix (Fin r) (Fin r) ℤ),
      1 ≤ r ∧ b.transpose = b ∧ (b.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit b.det ∧
        ∀ a, (ρ a).transpose * b = b * ρ (σ a) := by
  have hcast : ∀ {k : Type} [Fintype k] [DecidableEq k] (M : Matrix k k ℤ),
      (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := fun M => by
    simpa using ((Int.castRingHom ℝ).map_det M).symm
  have hDR : (0 : ℝ) < (B0.det : ℝ) := hcast B0 ▸ hp.det_pos
  have hD : 0 < B0.det := by exact_mod_cast hDR
  obtain ⟨s, hsD⟩ : ∃ s : ℕ, B0.det = 1 + s := ⟨(B0.det - 1).toNat, by omega⟩
  obtain ⟨x, hx, -⟩ := exists_int_matrix_transpose_mul_eq_smul_one s
  set b := fromBlocks (B0.adjugate ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℤ))
    ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ xᵀ) ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ x)
    (B0 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℤ)) with hb
  have hsym : bᵀ = b := by
    simp only [hb, fromBlocks_transpose, ← kroneckerMap_transpose, transpose_transpose,
      transpose_one, adjugate_transpose, hs]
  have hk : ∀ (M : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin 4) (Fin 4) ℤ),
      (M ⊗ₖ N).map (Int.cast : ℤ → ℝ) = M.map (Int.cast : ℤ → ℝ) ⊗ₖ N.map (Int.cast : ℤ → ℝ) := by
    intro M N
    ext i j
    simp [kroneckerMap_apply]
  have hxR : (x.map (Int.cast : ℤ → ℝ))ᵀ * x.map (Int.cast : ℤ → ℝ) = (s : ℝ) • 1 := by
    have := congrArg (fun M => (Int.castRingHom ℝ).mapMatrix M) hx
    simp only [map_mul, map_zsmul, map_one] at this
    rw [← Int.cast_smul_eq_zsmul ℝ] at this
    simpa [transpose_map] using this
  have hAR : (B0.adjugate).map (Int.cast : ℤ → ℝ) =
      (1 + (s : ℝ)) • (B0.map (Int.cast : ℤ → ℝ))⁻¹ := by
    have h1 : (B0.adjugate).map (Int.cast : ℤ → ℝ) = (B0.map (Int.cast : ℤ → ℝ)).adjugate := by
      simpa using (Int.castRingHom ℝ).map_adjugate B0
    have h2 : (1 + (s : ℝ)) = (B0.det : ℝ) := by rw [hsD]; push_cast; rfl
    rw [h1, h2, Matrix.inv_def, hcast, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hDR.ne',
      one_smul]
  have hreal := zarhinBlock_real_posDef_det _ _ _ _ hp hAR hxR
  have hbR : b.map (Int.cast : ℤ → ℝ) =
      fromBlocks (B0.adjugate.map (Int.cast : ℤ → ℝ) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ))
        ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ (x.map (Int.cast : ℤ → ℝ))ᵀ)
        ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ x.map (Int.cast : ℤ → ℝ))
        (B0.map (Int.cast : ℤ → ℝ) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
    rw [hb, fromBlocks_map, hk, hk, hk, hk, Matrix.map_one _ Int.cast_zero Int.cast_one,
      Matrix.map_one _ Int.cast_zero Int.cast_one, transpose_map]
  rw [← hbR, hcast] at hreal
  have hdet : b.det = 1 := by exact_mod_cast hreal.2
  have hact := zarhinAction_adjoint σ hσ ρ0 B0 B0.adjugate x hadj
    (fun a => mul_adjugate_eq_adjugate_mul_of_adjoint _ _ _ hD.ne' (hadj a))
  rw [← hb] at hact
  let e := Fintype.equivFin ((Fin m × Fin 4) ⊕ (Fin m × Fin 4))
  refine ⟨_, reindex e e b, ((reindexAlgEquiv ℤ ℤ e).toRingEquiv.toRingHom).comp
    (zarhinAction σ ρ0), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; omega
  · rw [transpose_reindex, hsym]
  · exact hreal.1.submatrix e.symm.injective
  · rw [det_reindex_self, hdet]; exact isUnit_one
  · intro a
    change (reindex e e (zarhinAction σ ρ0 a))ᵀ * _ = _ * reindex e e (zarhinAction σ ρ0 (σ a))
    simp only [reindex_apply, transpose_submatrix, submatrix_mul_equiv, hact]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightedHomogenisationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weightedHomogeneous_homogenisation : ∀ {L : Type} [Field L] (Q : Subring L) (r : ℕ) (z : Fin (r + 1) → Q)
    (wt : Fin (r + 1) → ℕ), wt 0 = 1 → (z 0 : L) ≠ 0 → ∀ P : MvPolynomial (Fin r) Q,
    ∃ (N : ℕ) (F : MvPolynomial (Fin (r + 1)) Q), F.IsWeightedHomogeneous wt N ∧
      ((MvPolynomial.eval z F : Q) : L) = (z 0 : L) ^ N *
        MvPolynomial.eval₂ Q.subtype (fun i => (z i.succ : L) / (z 0 : L) ^ wt i.succ) P ∧
      ∀ α, ∃ β, F.coeff β = P.coeff α := by
  first | exact @GlobalTheory.exists_weightedHomogenisation | exact GlobalTheory.exists_weightedHomogenisation | (intros; apply GlobalTheory.exists_weightedHomogenisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePoints
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.factor_closedImmersion_of_affine_points :
    ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X),
      (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) →
      ∃ z : T ⟶ Z, z ≫ i = g := by
  intro X Z T i hi g h
  let 𝒰 := T.affineCover
  have hj : ∀ j, ∃ y : 𝒰.X j ⟶ Z, y ≫ i = 𝒰.f j ≫ g := fun j => h _ (𝒰.f j)
  choose y hy using hj
  have hc : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ y a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ y b := by
    intro a b
    rw [← cancel_mono i, Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms y hc, ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hy]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLocalizationAwaySpanFinsetStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (N : Submodule R' A'), N.FG → ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by
  first | exact @GlobalTheory.fg_localizationAway_span_finset | exact GlobalTheory.fg_localizationAway_span_finset | (intros; apply GlobalTheory.fg_localizationAway_span_finset <;> assumption)
end

