module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealInfSmulTopOfProjective
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem mem_ideal_smul_top_iff_coord {O : Type} [CommRing O] {L : Type} [AddCommGroup L]
    [Module O L] (s : L →ₗ[O] (L →₀ O))
    (hs : Function.LeftInverse (Finsupp.linearCombination O (id : L → L)) s)
    (𝔠 : Ideal O) (x : L) :
    x ∈ 𝔠 • (⊤ : Submodule O L) ↔ ∀ i, s x i ∈ 𝔠 := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _ i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact 𝔠.mul_mem_right _ hr
    · intro a b ha hb i
      rw [map_add (f := _), Finsupp.add_apply]
      exact 𝔠.add_mem (ha i) (hb i)
  · intro h
    rw [← hs x, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem ideal_inf_smul_top_of_projective : ∀ (O : Type) [CommRing O] (L : Type) [AddCommGroup L] [Module O L] [Module.Projective O L] (𝔞 𝔟 : Ideal O), (𝔞 ⊓ 𝔟) • (⊤ : Submodule O L) = 𝔞 • (⊤ : Submodule O L) ⊓ 𝔟 • (⊤ : Submodule O L) := by
  intro O _ L _ _ hP 𝔞 𝔟
  obtain ⟨s, hs⟩ := Module.projective_def.1 hP
  ext x
  rw [Submodule.mem_inf, GlobalTheory.CompanionTheory.Ar.Cmp.mem_ideal_smul_top_iff_coord s hs,
    GlobalTheory.CompanionTheory.Ar.Cmp.mem_ideal_smul_top_iff_coord s hs,
    GlobalTheory.CompanionTheory.Ar.Cmp.mem_ideal_smul_top_iff_coord s hs]
  simp only [Submodule.mem_inf, forall_and]

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IdealSheafComapIdealAffineOpenOfIsAffine
section
open Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

section LocalHom

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Type*} [CommGroup A]
  {ρ : ℝ} {e₀ : V → A}

theorem localHom_nsmul (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w)
    (z : V) (k : ℕ) (hk : (k : ℝ) * ‖z‖ < ρ) : e₀ ((k : ℝ) • z) = e₀ z ^ k := by
  induction k with
  | zero =>
    have h0 := h 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)
    simp only [add_zero] at h0
    simpa using h0
  | succ k ih =>
    have hz := norm_nonneg z
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast at hk ⊢
    have h1 : (k : ℝ) * ‖z‖ < ρ := by nlinarith
    have h2 : ‖z‖ < ρ := by nlinarith
    have h3 : ‖(k : ℝ) • z‖ < ρ := by rwa [norm_smul, Real.norm_of_nonneg hk0]
    have h4 : ‖(k : ℝ) • z + z‖ < ρ := by
      have : (k : ℝ) • z + z = ((k : ℝ) + 1) • z := by rw [add_smul, one_smul]
      rwa [this, norm_smul, Real.norm_of_nonneg (by positivity)]
    rw [add_smul, one_smul, h _ _ h3 h2 h4, ih h1, pow_succ]

theorem localHom_norm_inv_smul_lt (z : V) {N : ℕ} (hN : 0 < N) (hz : ‖z‖ < N * ρ) :
    ‖(N : ℝ)⁻¹ • z‖ < ρ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_lt_iff₀ hN']
  exact hz

theorem localHom_pow_mul (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w)
    (z : V) {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hz : ‖z‖ < N * ρ) :
    e₀ ((N : ℝ)⁻¹ • z) ^ N = e₀ (((N : ℝ) * M)⁻¹ • z) ^ (N * M) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have e1 : (N : ℝ)⁻¹ • z = (M : ℝ) • (((N : ℝ) * M)⁻¹ • z) := by
    rw [smul_smul]; congr 1; field_simp
  have hb := localHom_norm_inv_smul_lt z hN hz
  have hk : (M : ℝ) * ‖((N : ℝ) * M)⁻¹ • z‖ < ρ := by
    rwa [e1, norm_smul, Real.norm_of_nonneg hM'.le] at hb
  rw [e1, localHom_nsmul hρ h _ M hk, ← pow_mul, mul_comm M N]

theorem localHom_pow_indep (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w)
    (z : V) {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (hzN : ‖z‖ < N * ρ) (hzM : ‖z‖ < M * ρ) :
    e₀ ((N : ℝ)⁻¹ • z) ^ N = e₀ ((M : ℝ)⁻¹ • z) ^ M := by
  rw [localHom_pow_mul hρ h z hN hM hzN, localHom_pow_mul hρ h z hM hN hzM, mul_comm N M,
    mul_comm (N : ℝ) M]

theorem localHom_exists_nat (hρ : 0 < ρ) (r : ℝ) : ∃ N : ℕ, 0 < N ∧ r < N * ρ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (r / ρ)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  rw [div_lt_iff₀ hρ] at hn
  push_cast
  nlinarith

theorem localHom_existsUnique_extension (hρ : 0 < ρ)
    (h : ∀ z w : V, ‖z‖ < ρ → ‖w‖ < ρ → ‖z + w‖ < ρ → e₀ (z + w) = e₀ z * e₀ w) :
    ∃! e : V → A, (∀ z w, e (z + w) = e z * e w) ∧ ∀ z, ‖z‖ < ρ → e z = e₀ z := by
  choose N hN hNz using fun z : V => localHom_exists_nat hρ ‖z‖
  refine ⟨fun z => e₀ ((N z : ℝ)⁻¹ • z) ^ N z, ⟨fun z w => ?_, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨M, hM, hMz⟩ := localHom_exists_nat hρ (‖z‖ + ‖w‖)
    have hz : ‖z‖ < M * ρ := by linarith [norm_nonneg w]
    have hw : ‖w‖ < M * ρ := by linarith [norm_nonneg z]
    have hzw : ‖z + w‖ < M * ρ := (norm_add_le z w).trans_lt hMz
    have hb := localHom_norm_inv_smul_lt _ hM hzw
    rw [smul_add] at hb
    simp only
    rw [localHom_pow_indep hρ h z (hN z) hM (hNz z) hz,
      localHom_pow_indep hρ h w (hN w) hM (hNz w) hw,
      localHom_pow_indep hρ h (z + w) (hN _) hM (hNz _) hzw, smul_add,
      h _ _ (localHom_norm_inv_smul_lt z hM hz) (localHom_norm_inv_smul_lt w hM hw) hb, mul_pow]
  · simp only
    rw [localHom_pow_indep hρ h z (hN z) one_pos (hNz z) (by simpa using hz)]
    simp
  · rintro e ⟨he, he₀⟩
    funext z
    have hN' : (0 : ℝ) < N z := by exact_mod_cast hN z
    have hb := localHom_norm_inv_smul_lt z (hN z) (hNz z)
    have key := localHom_nsmul (ρ := ‖z‖ + 1) (e₀ := e) (by positivity)
      (fun a b _ _ _ => he a b) ((N z : ℝ)⁻¹ • z) (N z) (by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_inv_cancel_left₀ hN'.ne']
        linarith)
    rw [smul_inv_smul₀ hN'.ne', he₀ _ hb] at key
    exact key

end LocalHom

theorem existsUnique_extension_of_ball :
    ∀ (g : ℕ) (A : Type) [CommGroup A] (ρ : ℝ), 0 < ρ → ∀ e₀ : (Fin g → ℂ) → A,
      (∀ z ∈ ball (0 : Fin g → ℂ) ρ, ∀ w ∈ ball (0 : Fin g → ℂ) ρ,
        z + w ∈ ball (0 : Fin g → ℂ) ρ → e₀ (z + w) = e₀ z * e₀ w) →
      ∃! e : (Fin g → ℂ) → A, (∀ z w, e (z + w) = e z * e w) ∧
        ∀ z ∈ ball (0 : Fin g → ℂ) ρ, e z = e₀ z := by
  intro g A _ ρ hρ e₀ h
  simp only [mem_ball_zero_iff] at h ⊢
  exact localHom_existsUnique_extension hρ fun z w hz hw hzw => h z hz w hw hzw

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalRingModTEmbedsStrictHenselian
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_basis_split_of_exact_of_fg_valuationRing :
    ∀ (V C A W B : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C]
      [IsFractionRing V C] [AddCommGroup A] [Module C A] [Module V A] [IsScalarTower V C A]
      [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [AddCommGroup B]
      [Module C B] [Module V B] [IsScalarTower V C B] (b : A →ₗ[C] W) (al : W →ₗ[C] B),
      Function.Injective b → Function.Exact b al → ∀ (T : Submodule V W), T.FG →
      ∃ (p q : ℕ) (w : Fin p → A) (t : Fin q → W), LinearIndependent C w ∧
        Submodule.span V (Set.range w) = T.comap (b.restrictScalars V) ∧
        LinearIndependent C (fun j => al (t j)) ∧
        Submodule.span V (Set.range fun j => al (t j)) = T.map (al.restrictScalars V) ∧
        LinearIndependent C (Sum.elim (fun i => b (w i)) t) ∧
        Submodule.span V (Set.range (Sum.elim (fun i => b (w i)) t)) = T := by
  intro V C A W B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b al hb hex T hT
  have : IsBezout V := ValuationRing.instIsBezout

  have hfree : ∀ (X : Type) [AddCommGroup X] [Module C X] [Module V X] [IsScalarTower V C X]
      (N : Submodule V X), N.FG → Module.Free V N := by
    intro X _ _ _ _ N hN
    have : Module.Finite V N := Module.Finite.iff_fg.mpr hN
    have : Module.Flat V N := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
      have h2 : ((a : V) • x : N) = 0 := ha
      have h3 : (a : V) • (x : X) = 0 := by
        have h4 := congrArg Subtype.val h2
        simpa using h4
      have h1 : (algebraMap V C (a : V)) • (x : X) = 0 := by
        rw [algebraMap_smul]; exact h3
      have ha0 : algebraMap V C (a : V) ≠ 0 := by
        intro h
        have h5 : (a : V) = 0 := (IsFractionRing.injective V C) (by rw [h, map_zero])
        exact nonZeroDivisors.coe_ne_zero a h5
      have hx0 : (x : X) = 0 := (smul_eq_zero.mp h1).resolve_left ha0
      exact Subtype.ext (by simp [hx0])
    exact Module.free_of_flat_of_isLocalRing

  have hL : ∀ (X : Type) [AddCommGroup X] [Module C X] [Module V X] [IsScalarTower V C X]
      (N : Submodule V X), N.FG → ∃ (n : ℕ) (v : Fin n → X),
        LinearIndependent C v ∧ Submodule.span V (Set.range v) = N := by
    intro X _ _ _ _ N hN
    have := hfree X N hN
    have : Module.Finite V N := Module.Finite.iff_fg.mpr hN
    let e := (Module.Free.chooseBasis V N).reindex
      (Fintype.equivFin (Module.Free.ChooseBasisIndex V N))
    refine ⟨Fintype.card (Module.Free.ChooseBasisIndex V N), fun i => (e i : X), ?_, ?_⟩
    · rw [← LinearIndependent.iff_fractionRing V C]
      exact e.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    · have hr : Set.range (fun i => (e i : X)) = N.subtype '' Set.range e := by
        rw [← Set.range_comp]; rfl
      rw [hr, Submodule.span_image, e.span_eq, Submodule.map_subtype_top]

  obtain ⟨q, u, hu, hus⟩ := hL B (T.map (al.restrictScalars V)) (hT.map _)
  have hu_mem : ∀ j, u j ∈ T.map (al.restrictScalars V) := by
    intro j
    rw [← hus]
    exact Submodule.subset_span ⟨j, rfl⟩
  choose t ht hta using fun j => Submodule.mem_map.mp (hu_mem j)
  have hta' : ∀ j, al (t j) = u j := fun j => hta j
  have hal : (fun j => al (t j)) = u := funext hta'

  have : Module.Free V (T.map (al.restrictScalars V)) := hfree B _ (hT.map _)
  have : Module.Finite V (T.map (al.restrictScalars V)) := Module.Finite.iff_fg.mpr (hT.map _)
  have : Module.Finite V T := Module.Finite.iff_fg.mpr hT
  have : Module.FinitePresentation V (T.map (al.restrictScalars V)) :=
    Module.finitePresentation_of_projective V _
  have hker : (LinearMap.ker ((al.restrictScalars V).submoduleMap T)).FG :=
    Module.FinitePresentation.fg_ker _ (LinearMap.submoduleMap_surjective _ _)
  have hK : (T.comap (b.restrictScalars V)).FG := by
    apply Submodule.fg_of_fg_map_injective (b.restrictScalars V) hb
    have heq : (T.comap (b.restrictScalars V)).map (b.restrictScalars V)
        = (LinearMap.ker ((al.restrictScalars V).submoduleMap T)).map T.subtype := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨⟨b a, ha⟩, ?_, rfl⟩
        show ((al.restrictScalars V).submoduleMap T) ⟨b a, ha⟩ = 0
        apply Subtype.ext
        show al (b a) = 0
        exact (hex (b a)).mpr ⟨a, rfl⟩
      · rintro ⟨⟨y, hyT⟩, hy0, rfl⟩
        have hy0' : ((al.restrictScalars V).submoduleMap T) ⟨y, hyT⟩ = 0 := hy0
        have hy : al y = 0 := congrArg Subtype.val hy0'
        obtain ⟨a, rfl⟩ := (hex y).mp hy
        exact ⟨a, hyT, rfl⟩
    rw [heq]
    exact hker.map _
  obtain ⟨p, w, hw, hws⟩ := hL A (T.comap (b.restrictScalars V)) hK
  refine ⟨p, q, w, t, hw, hws, ?_, ?_, ?_, ?_⟩
  · rw [hal]; exact hu
  · rw [hal]; exact hus
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have h1 : ∀ i, al (b (w i)) = 0 := fun i => (hex _).mpr ⟨w i, rfl⟩
    have h2 : ∑ j, g (Sum.inr j) • u j = 0 := by
      have h7 := congrArg al hg
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_add (f := _), map_sum, map_smul, h1, hta'] using h7
    have h3 : ∀ j, g (Sum.inr j) = 0 :=
      Fintype.linearIndependent_iff.mp hu (fun j => g (Sum.inr j)) h2
    have h4 : ∑ i, g (Sum.inl i) • b (w i) = 0 := by
      simpa [h3] using hg
    have h5 : ∑ i, g (Sum.inl i) • w i = 0 := by
      apply hb
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_smul] using h4
    have h6 := Fintype.linearIndependent_iff.mp hw (fun i => g (Sum.inl i)) h5
    intro i
    cases i with
    | inl i => exact h6 i
    | inr j => exact h3 j
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl i =>
        have hwi : w i ∈ T.comap (b.restrictScalars V) := by
          rw [← hws]; exact Submodule.subset_span ⟨i, rfl⟩
        exact hwi
      | inr j => exact ht j
    · intro x hx
      have hax : al x ∈ T.map (al.restrictScalars V) := Submodule.mem_map_of_mem hx
      rw [← hus, Submodule.mem_span_range_iff_exists_fun] at hax
      obtain ⟨c, hc⟩ := hax
      have hyal : al (x - ∑ j, c j • t j) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum]
        simp only [LinearMap.map_smul_of_tower, hta']
        rw [hc, sub_self]
      obtain ⟨a, ha⟩ := (hex _).mp hyal
      have haK : a ∈ T.comap (b.restrictScalars V) := by
        show b a ∈ T
        rw [ha]
        exact T.sub_mem hx (T.sum_mem fun j _ => T.smul_mem (c j) (ht j))
      rw [← hws] at haK
      have hx_eq : x = b a + ∑ j, c j • t j := by rw [ha]; abel
      rw [hx_eq, Set.Sum.elim_range, Submodule.span_union]
      apply Submodule.add_mem_sup
      · have hr : Set.range (fun i => b (w i)) = (b.restrictScalars V) '' Set.range w := by
          rw [← Set.range_comp]; rfl
        rw [hr, Submodule.span_image]
        exact Submodule.mem_map_of_mem haK
      · exact Submodule.sum_mem _ fun j _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemIdealSmulTopIffForallDual
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem mem_ideal_smul_top_iff_forall_dual {O : Type*} [CommRing O] {L : Type*} [AddCommGroup L]
    [Module O L] [Module.Finite O L] [Module.Projective O L] (𝔟 : Ideal O) (x : L) :
    x ∈ 𝔟 • (⊤ : Submodule O L) ↔ ∀ φ : L →ₗ[O] O, φ x ∈ 𝔟 := by
  constructor
  · intro hx φ
    have hle : 𝔟 • (⊤ : Submodule O L) ≤ Submodule.comap φ 𝔟 := by
      rw [Submodule.smul_le]
      intro r hr n _
      rw [Submodule.mem_comap, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    obtain ⟨s, hs⟩ := Module.Projective.out (R := O) (P := L)
    rw [← hs x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine sum_mem fun y _ => ?_
    have hy : (s x) y ∈ 𝔟 := by
      simpa using h ((Finsupp.lapply y).comp s)
    exact Submodule.smul_mem_smul hy Submodule.mem_top

theorem mem_of_forall_mul_mem_ideal_mul {O : Type*} [CommRing O] [IsDedekindDomain O]
    {𝔪 𝔞 : Ideal O} (h𝔪 : 𝔪 ≠ ⊥) {c : O} (h : ∀ m ∈ 𝔪, m * c ∈ 𝔪 * 𝔞) : c ∈ 𝔞 := by
  have h0 : 𝔪 ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  have hle : 𝔪 * Ideal.span {c} ≤ 𝔪 * 𝔞 := by
    rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hs
    rw [← mul_assoc]
    exact Ideal.mul_mem_right _ _ (h r hr)
  have hd : 𝔪 * 𝔞 ∣ 𝔪 * Ideal.span {c} := Ideal.dvd_iff_le.mpr hle
  rw [mul_dvd_mul_iff_left h0] at hd
  exact (Ideal.dvd_iff_le.mp hd) (Ideal.mem_span_singleton_self c)

theorem map_ideal_smul_top_iff_cancel : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (L : Type) [AddCommGroup L] [Module O L] [Module.Finite O L] [Module.Projective O L] (𝔪 𝔞 : Ideal O) (T : L →ₗ[O] L), 𝔪 ≠ ⊥ → ((∀ x ∈ 𝔪 • (⊤ : Submodule O L), T x ∈ (𝔪 * 𝔞) • (⊤ : Submodule O L)) ↔ ∀ x, T x ∈ 𝔞 • (⊤ : Submodule O L)) := by
  intro O _ _ L _ _ _ _ 𝔪 𝔞 T h𝔪
  constructor
  · intro hT x
    rw [mem_ideal_smul_top_iff_forall_dual]
    intro φ
    refine mem_of_forall_mul_mem_ideal_mul h𝔪 fun m hm => ?_
    have hmx : m • x ∈ 𝔪 • (⊤ : Submodule O L) := Submodule.smul_mem_smul hm Submodule.mem_top
    have key := (mem_ideal_smul_top_iff_forall_dual (𝔪 * 𝔞) (T (m • x))).mp (hT _ hmx) φ
    rwa [map_smul, map_smul, smul_eq_mul] at key
  · intro hT x hx
    have hle : 𝔪 • (⊤ : Submodule O L) ≤ Submodule.comap T ((𝔪 * 𝔞) • (⊤ : Submodule O L)) := by
      rw [Submodule.smul_le]
      intro r hr n _
      rw [Submodule.mem_comap, map_smul, mem_ideal_smul_top_iff_forall_dual]
      intro φ
      rw [map_smul, smul_eq_mul]
      exact Ideal.mul_mem_mul hr ((mem_ideal_smul_top_iff_forall_dual 𝔞 (T n)).mp (hT n) φ)
    exact hle hx

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemMaxSmulTopIff
section
open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg.SatOfInj

theorem mem_max_smul_top_iff {R M : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] {π : R} (hπ : Irreducible π) (x : M) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔ ∃ z : M, x = π • z := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer π |>.mp hπ,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, trivial, rfl⟩

theorem eq_zero_of_smul {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] {a : R} (ha : a ≠ 0) {z : M} (h : a • z = 0) : z = 0 :=
  (smul_eq_zero.mp h).resolve_left ha

theorem pow_step {R P E : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (f : P →ₗ[R] E) {π : R} (hπ : Irreducible π)
    (hf : ∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P))
    (n : ℕ) : ∀ (y : E), π ^ n • y ∈ LinearMap.range f → y ∈ LinearMap.range f := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    obtain ⟨x, hx⟩ := hy
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [mem_max_smul_top_iff hπ]
      exact ⟨π ^ n • y, by rw [hx, pow_succ', mul_smul]⟩
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    refine ih y ⟨x', ?_⟩
    have h0 : π • (f x' - π ^ n • y) = 0 := by
      rw [smul_sub, ← map_smul, hx, pow_succ', mul_smul, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_smul hπ.ne_zero h0)

theorem sat_of_inj_mod : ∀ (R P E : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [AddCommGroup E] [Module R E]
    [Module.IsTorsionFree R E] [Module.IsTorsionFree R P] (f : P →ₗ[R] E),
    (∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) →
    Function.Injective f ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f := by
  intro R P E _ _ _ _ _ _ _ _ _ _ f hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    have hx0 : f x = 0 := hx
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [hx0]; exact Submodule.zero_mem _
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    have hx' : f x' = 0 := by
      rw [map_smul] at hx0
      exact eq_zero_of_smul hπ.ne_zero hx0
    exact Submodule.smul_mem_smul
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π)
      (LinearMap.mem_ker.mpr hx')
  · intro a y ha hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have h1 : π ^ n • ((u : R) • y) ∈ LinearMap.range f := by
      rw [smul_smul, mul_comm]
      exact hy
    have h2 := pow_step f hπ hf n _ h1
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Rˣ) : R) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3

end GlobalTheory.CompanionTheory.CommAlg.SatOfInj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NatDegreeMinpolyEqOfClosed
section
open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Cmp.RegularTensor

open Polynomial

theorem natDegree_minpoly_eq_of_closed {k F A : Type*} [Field k] [Field F] [Field A] [Algebra k F]
    [Algebra F A] [Algebra k A] [IsScalarTower k F A]
    (h : ∀ x : F, IsAlgebraic k x → x ∈ Set.range (algebraMap k F))
    {θ : A} (hθ : IsIntegral k θ) : (minpoly F θ).natDegree = (minpoly k θ).natDegree := by
  have hF : IsIntegral F θ := hθ.tower_top
  have hd : minpoly F θ ∣ (minpoly k θ).map (algebraMap k F) :=
    minpoly.dvd_map_of_isScalarTower k F θ
  have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F (minpoly.monic hθ)
    (minpoly.monic hF) hd
  have h2 : minpoly F θ ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨y, hy⟩ := h1 n
    rw [← hy]
    exact h _ (IsIntegral.isAlgebraic y.2)
  obtain ⟨q, hq, hdeg, hm⟩ := lifts_and_natDegree_eq_and_monic h2 (minpoly.monic hF)
  apply le_antisymm
  · have := natDegree_le_of_dvd hd ((minpoly.monic hθ).map _).ne_zero
    rwa [natDegree_map] at this
  · rw [← hdeg]
    refine natDegree_le_of_dvd (minpoly.dvd k θ ?_) hm.ne_zero
    rw [← aeval_map_algebraMap F, hq, minpoly.aeval]

end GlobalTheory.CompanionTheory.Ar.Cmp.RegularTensor
end

