module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBasisTraceLogNorm
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0068
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzChowMahlerFibreavg
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0066
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0069
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ConeBallLogGapIntegral
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenLocalBasisLogNorm
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.EigSubLat

namespace LieEigenProjections

section Proj

variable {E K U : Type} [Field E] [NumberField E] [Field K] [AddCommGroup U] [Module K U]

theorem eigProj_rho (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (a : 𝓞 E) (u : U) :
    HT.eigProj ρ σ (ρ a u) = σ (a : E) • HT.eigProj ρ σ u := by
  have h1 : HT.eigProj ρ σ (ρ a u) = ρ a (HT.eigProj ρ σ u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  rw [h1]
  exact HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ σ u) a

theorem eigProj_eq_zero (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (r : 𝓞 E) (s : K)
    (hs : s ≠ σ (r : E)) {u : U} (hu : ρ r u = s • u) : HT.eigProj ρ σ u = 0 := by
  have h1 := eigProj_rho ρ σ r u
  rw [hu, map_smul] at h1
  have h2 : (s - σ (r : E)) • HT.eigProj ρ σ u = 0 := by rw [sub_smul, h1, sub_self]
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hs)

theorem eigProj_eq_sum [CharZero K] (hcard : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (r : 𝓞 E) {f : ℕ} (b : Fin f → 𝓞 E) (b' : Fin f → E)
    (hb : ∀ σ' : E →+* K, σ (r : E) = σ' (r : E) →
      (σ = σ' → ∑ k, σ (b' k) * σ' (b k : E) = 1) ∧ (σ ≠ σ' → ∑ k, σ (b' k) * σ' (b k : E) = 0))
    {u : U} (hu : ρ r u = σ (r : E) • u) :
    HT.eigProj ρ σ u = ∑ k, σ (b' k) • ρ (b k) u := by
  classical
  haveI : Finite (E →+* K) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact Module.finrank_pos.ne')
  haveI : Fintype (E →+* K) := Fintype.ofFinite _
  have hsum : ∑ τ : E →+* K, HT.eigProj ρ τ = 1 :=
    HT.sum_eigProj_eq_one K U E ρ (by rw [← Nat.card_eq_fintype_card, hcard])
  have hexp : u = ∑ τ : E →+* K, HT.eigProj ρ τ u := by
    have := congrArg (fun T : Module.End K U => T u) hsum
    simpa [LinearMap.sum_apply] using this.symm
  have hterm : ∀ τ : E →+* K,
      ∑ k, σ (b' k) • ρ (b k) (HT.eigProj ρ τ u) = if τ = σ then HT.eigProj ρ σ u else 0 := by
    intro τ
    have hact : ∀ k, ρ (b k) (HT.eigProj ρ τ u) = τ (b k : E) • HT.eigProj ρ τ u := fun k =>
      HT.LatBasic.mem_eigSp.1 (HT.LatBasic.eigProj_mem ρ τ u) (b k)
    simp only [hact, smul_smul]
    rw [← Finset.sum_smul]
    by_cases h : τ = σ
    · subst h
      rw [(hb τ rfl).1 rfl, one_smul, if_pos rfl]
    · rw [if_neg h]
      by_cases hr : σ (r : E) = τ (r : E)
      · rw [(hb τ hr).2 (Ne.symm h), zero_smul]
      · rw [eigProj_eq_zero ρ τ r (σ (r : E)) hr hu, smul_zero]
  conv_rhs => rw [hexp]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [hterm]
  simp

end Proj

end LieEigenProjections

section Core

variable {E K U : Type} [Field E] [NumberField E] [Field K] [CharZero K] [AddCommGroup U] [Module K U]

theorem core (V : Subring K) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (r : 𝓞 E)
    (hr : σ (r : E) ≠ 0) {I J : Type} [Fintype I] [Fintype J] (u : I → U) (u' : J → U) {f : ℕ}
    (b : Fin f → 𝓞 E) (m : Fin f → K) (δ : K) (k₀ : Fin f)
    (hm : ∀ a, HT.eigProj ρ σ (u a) = ∑ k, m k • ρ (b k) (u a))
    (hu' : ∀ a, ρ r (u' a) = -σ (r : E) • u' a)
    (hlin : LinearIndependent K (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
      (fun q : J × Fin f => ρ (b q.2) (u' q.1))))
    (hδ0 : δ ≠ 0) (hk₀ : m k₀ ≠ 0) (hVm : ∀ k, δ * m k ∈ V)
    (hVx : ∀ x : K, x * m k₀ ∈ V → x * δ⁻¹ ∈ V) :
    LinearIndependent K (fun a => δ • HT.eigProj ρ σ (u a)) ∧
      Submodule.span V (Set.range (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
        (fun q : J × Fin f => ρ (b q.2) (u' q.1)))) ⊓ (HT.eigSp ρ σ).restrictScalars V =
      Submodule.span V (Set.range fun a => δ • HT.eigProj ρ σ (u a)) := by
  classical
  have hneg : -σ (r : E) ≠ σ (r : E) := by
    intro h
    have h2 : (2 : K) * σ (r : E) = 0 := by linear_combination -h
    exact hr ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
  have hker : ∀ a k, HT.eigProj ρ σ (ρ (b k) (u' a)) = 0 := by
    intro a k
    refine LieEigenProjections.eigProj_eq_zero ρ σ r (-σ (r : E)) hneg ?_
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hu', map_smul]
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg a
    have hs : ∑ q : I × Fin f, (g q.1 * δ * m q.2) •
        (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
          (fun q : J × Fin f => ρ (b q.2) (u' q.1)) ∘ Sum.inl) q = 0 := by
      rw [Fintype.sum_prod_type, ← hg]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hm, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change (g a * δ * m k) • ρ (b k) (u a) = g a • δ • m k • ρ (b k) (u a)
      rw [smul_smul, smul_smul]
    have hl := Fintype.linearIndependent_iff.1 (hlin.comp Sum.inl Sum.inl_injective) _ hs (a, k₀)
    simpa [hδ0, hk₀] using hl
  · rintro z ⟨hz1, hz2⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hz1
    have hz3 : z ∈ HT.eigSp ρ σ := hz2
    have heig := HT.LatBasic.eigProj_of_mem hz3
    rw [Fintype.sum_sum_type] at hc
    simp only [Sum.elim_inl, Sum.elim_inr, Subring.smul_def] at hc
    set x : I → K := fun a => ∑ k, (c (Sum.inl (a, k)) : K) * σ (b k : E) with hx
    have hez : z = ∑ a, x a • HT.eigProj ρ σ (u a) := by
      conv_lhs => rw [← heig, ← hc]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, map_sum]
      have h0 : ∑ q : J × Fin f, HT.eigProj ρ σ ((c (Sum.inr q) : K) • ρ (b q.2) (u' q.1)) = 0 :=
        Finset.sum_eq_zero fun q _ => by rw [map_smul, hker, smul_zero]
      rw [h0, add_zero, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hx, Finset.sum_smul, map_smul, LieEigenProjections.eigProj_rho, smul_smul]
    have hcoef : ∀ a k, (c (Sum.inl (a, k)) : K) = x a * m k := by
      have hz0 : ∑ i, ((c i : K) - Sum.elim (fun q : I × Fin f => x q.1 * m q.2)
          (fun _ : J × Fin f => (0 : K)) i) • (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
            (fun q : J × Fin f => ρ (b q.2) (u' q.1))) i = 0 := by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, sub_zero, sub_smul, Finset.sum_sub_distrib]
        have h1 : ∑ q : I × Fin f, (x q.1 * m q.2) • ρ (b q.2) (u q.1) = z := by
          rw [hez, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hm, Finset.smul_sum]
          simp only [smul_smul]
        rw [h1, sub_add_eq_add_sub, hc, sub_self]
      intro a k
      have := Fintype.linearIndependent_iff.1 hlin _ hz0 (Sum.inl (a, k))
      simpa [sub_eq_zero] using this
    have hy : ∀ a, x a * δ⁻¹ ∈ V := fun a => hVx _ (by
      rw [← hcoef a k₀]; exact (c (Sum.inl (a, k₀))).2)
    rw [hez]
    refine Submodule.sum_mem _ fun a _ => ?_
    have h1 : x a • HT.eigProj ρ σ (u a) =
        (⟨x a * δ⁻¹, hy a⟩ : V) • (δ • HT.eigProj ρ σ (u a)) := by
      rw [Subring.smul_def, smul_smul]
      simp [hδ0]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · change δ • HT.eigProj ρ σ (u a) ∈ Submodule.span V _
      rw [hm, Finset.smul_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      have h1 : δ • m k • ρ (b k) (u a) = (⟨δ * m k, hVm k⟩ : V) •
          (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1))
            (fun q : J × Fin f => ρ (b q.2) (u' q.1))) (Sum.inl (a, k)) := by
        rw [Subring.smul_def, smul_smul]
        rfl
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · exact (HT.eigSp ρ σ).smul_mem δ (HT.LatBasic.eigProj_mem ρ σ _)

end Core

theorem eigSub_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) (K : Type) [Field K] [CharZero K] (j : K →+* ℂ_[ℓ]) (V : Subring K) (U : Type) [AddCommGroup U] [Module K U] (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I J : Type) [Fintype I] [Fintype J] (u : I → U) (u' : J → U) (f : ℕ) (b : Fin f → 𝓞 E) (δ : K), (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V) → Nat.card (E →+* K) = Module.finrank ℚ E → IsLocBasis (Algebra.adjoin ℤ {H.w0}) ℓ b → (∀ a, ρ H.rt (u a) = σ (H.rt : E) • u a) → (∀ a, ρ H.rt (u' a) = -σ (H.rt : E) • u' a) → LinearIndependent K (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1)) (fun q : J × Fin f => ρ (b q.2) (u' q.1))) → δ ≠ 0 → Real.log ‖j δ‖ = logIdeal ((j.comp σ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (σ (H.rt : E))‖ → LinearIndependent K (fun a => δ • HT.eigProj ρ σ (u a)) ∧ Submodule.span V (Set.range (Sum.elim (fun q : I × Fin f => ρ (b q.2) (u q.1)) (fun q : J × Fin f => ρ (b q.2) (u' q.1)))) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range fun a => δ • HT.eigProj ρ σ (u a)) := by
  intro E _ _ _ H ℓ K _ _ j V U _ _ ρ σ I J _ _ u u' f b δ hV hcard hloc hu hu' hlin hδ0 hδ
  obtain ⟨b', hb', hj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.RelDual.relative_dual E H ℓ f b hloc
  obtain ⟨hpos, hlog⟩ := hj (j.comp σ)
  simp only [RingHom.comp_apply] at hpos hlog
  have hδp : 0 < ‖j δ‖ := norm_pos_iff.2 ((map_ne_zero j).2 hδ0)
  have hprod : (⨆ k, ‖j (σ (b' k))‖) * ‖j δ‖ = 1 := by
    refine Real.eq_one_of_pos_of_log_eq_zero (mul_pos hpos hδp) ?_
    rw [Real.log_mul hpos.ne' hδp.ne', hlog, hδ]
    ring
  haveI : Nonempty (Fin f) := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Real.iSup_of_isEmpty] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨k₀, hk₀⟩ := exists_eq_ciSup_of_finite (f := fun k => ‖j (σ (b' k))‖)
  have hle : ∀ k, ‖j (σ (b' k))‖ ≤ ⨆ k, ‖j (σ (b' k))‖ := fun k =>
    le_ciSup (Set.finite_range fun k => ‖j (σ (b' k))‖).bddAbove k
  have hr : σ (H.rt : E) ≠ 0 := by
    intro h
    have h1 := congrArg (fun y : 𝓞 E => σ (y : E)) H.rt_sq
    simp only [map_pow, map_neg, h, map_natCast] at h1
    have h2 : (H.rt : E) = 0 := by simpa using h
    have h3 : (H.d : K) = 0 := by
      have : σ (((H.rt ^ 2 : 𝓞 E)) : E) = 0 := by simp [h2]
      rw [H.rt_sq] at this
      simpa using this
    exact H.d_prime.ne_zero (by exact_mod_cast h3)
  refine core V ρ σ H.rt hr u u' b (fun k => σ (b' k)) δ k₀ ?_ hu' hlin hδ0 ?_ ?_ ?_
  · exact fun a => LieEigenProjections.eigProj_eq_sum hcard ρ σ H.rt b b' (fun σ' h => hb' K σ σ' h) (hu a)
  · intro h0
    have h0' : σ (b' k₀) = 0 := h0
    have : ‖j (σ (b' k₀))‖ = 0 := by rw [h0', map_zero, norm_zero]
    rw [← hk₀, this] at hpos
    exact lt_irrefl _ hpos
  · intro k
    refine (hV _).1 ?_
    rw [map_mul, norm_mul, mul_comm]
    calc ‖j (σ (b' k))‖ * ‖j δ‖ ≤ (⨆ k, ‖j (σ (b' k))‖) * ‖j δ‖ :=
          mul_le_mul_of_nonneg_right (hle k) hδp.le
      _ = 1 := hprod
  · intro x hx
    have h1 := (hV _).2 hx
    rw [map_mul, norm_mul, hk₀] at h1
    refine (hV _).1 ?_
    rw [map_mul, norm_mul, map_inv₀, norm_inv]
    have h2 : ‖j δ‖⁻¹ = ⨆ k, ‖j (σ (b' k))‖ := by
      field_simp
      linarith
    rw [h2]
    exact h1

end GlobalTheory.CompanionTheory.Ar.Fl.EigSubLat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralFubiniStudySumCone
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem fubini_study_sum_crofton {n e δ : ℕ} (h : HermNorm n) (u : Fin n → ℂ)
    (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (hc : (fibrePts S π).encard = δ)
    (hs : ∑' y : fibrePts S π, logGap h u y < ⊤) :
    (∑' y : fibrePts S π, logGap h u y).toReal = δ * Real.log (h.norm u) - fsSum h u S π := by
  have hfin : (fibrePts S π).Finite := Set.finite_of_encard_eq_coe hc
  have hcard : hfin.toFinset.card = δ := by
    have h1 := hfin.encard_eq_coe_toFinset_card
    rw [hc] at h1
    exact_mod_cast h1.symm
  have hne0 : ∀ y ∈ fibrePts S π, y ≠ 0 := by
    rintro y ⟨-, hy⟩ rfl
    have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) hy
    simp [linProj, firstCoordVec] at h2
  have hsum : ∀ y ∈ fibrePts S π, ∑ j, u j * h.pointOf y j ≠ 0 := by
    intro y hy h0
    have htop : logGap h u y = ⊤ := by simp [logGap, hne0 y hy, h0]
    have hle : logGap h u y ≤ ∑' z : fibrePts S π, logGap h u z :=
      ENNReal.le_tsum (f := fun z : fibrePts S π => logGap h u z) ⟨y, hy⟩
    rw [htop] at hle
    exact absurd hs (not_lt.2 hle)
  have hval : ∀ y ∈ fibrePts S π,
      logGap h u y = ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y)) := by
    intro y hy
    simp [logGap, hne0 y hy, hsum y hy]
  have hnn : ∀ y ∈ fibrePts S π, 0 ≤ Real.log (h.norm u) - fsLog h u (h.pointOf y) := fun y hy =>
    sub_nonneg.2 (_root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsLog_pointOf_le_log_norm n h u y (hne0 y hy) (hsum y hy))
  haveI : Fintype (fibrePts S π) := hfin.fintype
  have htsum : ∑' z : fibrePts S π, logGap h u z = ∑ y ∈ hfin.toFinset, logGap h u y := by
    rw [tsum_fintype]
    exact (Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) (logGap h u)).symm
  rw [htsum, ENNReal.toReal_sum (fun y hy => by
      rw [hval y (hfin.mem_toFinset.1 hy)]
      exact ENNReal.ofReal_ne_top)]
  rw [Finset.sum_congr rfl (fun y hy => by
      rw [hval y (hfin.mem_toFinset.1 hy), ENNReal.toReal_ofReal (hnn y (hfin.mem_toFinset.1 hy))])]
  rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, fsSum,
    finsum_mem_eq_finite_toFinset_sum _ hfin]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton

private theorem tsum_fibre_pts_eq_sum {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (hfin : (fibrePts S π).Finite) (g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    ∑' y : fibrePts S π, g y = ∑ y ∈ hfin.toFinset, g y := by
  haveI : Fintype (fibrePts S π) := hfin.fintype
  rw [tsum_fintype]
  exact (Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) g).symm

private theorem ne_zero_of_mem_fibre_pts {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ fibrePts S π) : y ≠ 0 := by
  rintro rfl
  obtain ⟨-, h0⟩ := hy
  have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) h0
  simp [linProj, firstCoordVec] at h2

theorem GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f → linForm u ∉ W →
    Integrable (fsSum h u (coneSet h W)) (gaussM (e + 1) n) ∧
      ∫ π, fsSum h u (coneSet h W) π ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * coneIntegral h W e (fsLog h u) := by
  intro n e δ h W f u hW hf hδ hu
  obtain ⟨hLGm, hLGo⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic n h u
  obtain ⟨hGm, hGeq⟩ := _root_.GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum n e δ h W f hW hf hδ (logGap h u) hLGm hLGo
  obtain ⟨hL, hLr⟩ := _root_.ModelDimension.integral_coneBall_log_gap_eq n e h W f u hW hf hu
  obtain ⟨hμ0, hμt⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top (e + 1) n
  obtain ⟨hpm0, hpmt⟩ : 0 < planeMass n e ∧ planeMass n e < ⊤ :=
    GroundTheory.Heights₂.Heights.coordBall_mass (chowGroups_le hW hf hδ)
  have hac : gaussM (e + 1) n ≪ (volume : Measure (Fin (e + 1) → Fin n → ℂ)) :=
    withDensity_absolutelyContinuous _ _
  have hcnt : ∀ᵐ π ∂(gaussM (e + 1) n), (fibrePts (coneSet h W) π).encard = δ :=
    hac.ae_le (_root_.GlobalTheory.CompanionTheory.Relay.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ)
  have hd : (0 : ℝ) < ((2 * (e + 1) : ℕ) : ℝ) := by positivity
  haveI := MeasureTheory.Measure.nullSingletonClass_hausdorff (EuclideanSpace ℂ (Fin n)) hd
  have hφm : Measurable (({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_singleton 0).compl
  have hφo : ∀ s : ℝ≥0∞,
      IsOpen {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} ∧
      IsScaleStable {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} := by
    intro s
    by_cases hs1 : s < 1
    · have hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} =
          {0}ᶜ := by
        ext y
        by_cases hy : y = 0
        · simp [Set.indicator_apply, hy]
        · simp [Set.indicator_apply, hy, hs1]
      rw [hset]
      exact ⟨isOpen_compl_singleton, fun y hy t ht => by simpa [ht] using hy⟩
    · have hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} =
          ∅ := by
        ext y
        by_cases hy : y = 0
        · simp [Set.indicator_apply, hy]
        · simp [Set.indicator_apply, hy, hs1]
      rw [hset]
      exact ⟨isOpen_empty, fun y hy => hy.elim⟩
  obtain ⟨-, hCeq⟩ := _root_.GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum n e δ h W f hW hf hδ _ hφm hφo
  have hae1 : ∀ᵐ π ∂(gaussM (e + 1) n), ∑' y : fibrePts (coneSet h W) π,
      ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = δ := by
    filter_upwards [hcnt] with π hπ
    have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hπ
    have hcard : hfin.toFinset.card = δ := by
      have h1 := hfin.encard_eq_coe_toFinset_card
      rw [hπ] at h1
      exact_mod_cast h1.symm
    have h1 : ∀ y ∈ hfin.toFinset,
        ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = 1 := fun y hy =>
      Set.indicator_of_mem (ne_zero_of_mem_fibre_pts _ π y (hfin.mem_toFinset.1 hy)) _
    rw [tsum_fibre_pts_eq_sum _ π hfin, Finset.sum_congr rfl h1, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  have hball : ∫⁻ y in coneBall h W, ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) := by
    rw [lintegral_indicator_const (measurableSet_singleton 0).compl, one_mul,
      Measure.restrict_apply (measurableSet_singleton 0).compl, Set.inter_comm, ← Set.sdiff_eq,
      measure_sdiff_null (measure_singleton 0)]
  rw [lintegral_congr_ae hae1, lintegral_const, hball] at hCeq
  have hHc : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) = δ * planeMass n e := by
    have h2 : gaussM (e + 1) n Set.univ * (δ * planeMass n e) =
        gaussM (e + 1) n Set.univ * Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) := by
      rw [← hCeq]
      ring
    exact ((ENNReal.mul_right_inj hμ0.ne' hμt.ne).1 h2).symm
  have hGfin : ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, logGap h u y ∂(gaussM (e + 1) n) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hpm0.ne'] at hGeq
    exact ENNReal.mul_ne_top hμt.ne hL.ne hGeq.symm
  have hGae := ae_lt_top hGm hGfin
  have hfs : ∀ᵐ π ∂(gaussM (e + 1) n), fsSum h u (coneSet h W) π =
      δ * Real.log (h.norm u) - (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal := by
    filter_upwards [hcnt, hGae] with π h1 h2
    rw [fubini_study_sum_crofton h u _ π h1 h2]
    ring
  haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hμt⟩
  have hGint := integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hGfin
  have hint : Integrable (fun π => (δ : ℝ) * Real.log (h.norm u) -
      (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal) (gaussM (e + 1) n) :=
    (integrable_const _).sub hGint
  refine ⟨hint.congr (hfs.mono fun π hπ => hπ.symm), ?_⟩
  rw [integral_congr_ae hfs, integral_sub (integrable_const _) hGint, integral_const,
    integral_toReal hGm.aemeasurable hGae, measureReal_def, smul_eq_mul]
  have hX := congrArg ENNReal.toReal hGeq
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hLr, hHc, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hX
  have hpmr : 0 < (planeMass n e).toReal := ENNReal.toReal_pos hpm0.ne' hpmt.ne
  have hci : coneIntegral h W e (fsLog h u) = (∫ y in coneBall h W, fsLog h u (h.pointOf y)
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / (planeMass n e).toReal := rfl
  rw [hci]
  have alg : ∀ a p X lg d I : ℝ, p ≠ 0 → p * X = a * (lg * (d * p) - I) →
      a * (d * lg) - X = a * (I / p) := by
    intro a p X lg d I hp hX'
    have hX'' : X = a * (lg * (d * p) - I) / p := by
      rw [eq_div_iff hp, mul_comm]
      exact hX'
    rw [hX'']
    field_simp
    ring
  exact alg _ _ _ _ _ _ hpmr.ne' hX
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifferenceStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_generic_flag_difference : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K ⊕ K' → ℤ) (f g : Fin N → MRing (Sum.elim ι ι') O), IsFlagPair ϖ (joinCoord x z) EB E'B w w' b b' f g → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O (joinCoord x z)) b b' f g (psumExpansion N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N E G L Q a = ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum b G (classList (fun j => pullDeg (K' := K') (L j)) μ) W) (divCycle (pointIdeal O (joinCoord x z)) (C a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_eq_pairNum_on_flagPair | exact GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_eq_pairNum_on_flagPair | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_eq_pairNum_on_flagPair <;> assumption)
end

