module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.SchwartzDecay

open NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem norm_le_mixed (x : InfiniteAdeleRing F) (v : InfinitePlace F) :
    ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  rcases v.isReal_or_isComplex with hv | hv
  · calc ‖x v‖ = ‖(e x).1 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).1 ⟨v, hv⟩).trans (norm_fst_le (e x))
  · calc ‖x v‖ = ‖(e x).2 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).2 ⟨v, hv⟩).trans (norm_snd_le (e x))

theorem abs_re_le (x : Ainf F) (v : InfinitePlace F) :
    |re x v| ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [(isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)]
  exact norm_le_mixed x v

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sz_le (u : Fin N → AF F) :
    sz u ≤ (N * Fintype.card (InfinitePlace F) : ℝ) *
      ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1‖ := by
  set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
  calc sz u ≤ ∑ _l : Fin N, ∑ _w : InfinitePlace F, ‖t‖ :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun w _ =>
          (abs_re_le (inf u l) w).trans (norm_le_pi_norm t l)
    _ = _ := by simp [mul_assoc]

theorem decay_add {Φ Ψ : (Fin N → AF F) → ℂ} (h : Decay Φ) (h' : Decay Ψ) : Decay (Φ + Ψ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  obtain ⟨hc', ⟨K', hK', hK0'⟩, hd'⟩ := h'
  refine ⟨hc.add hc', ⟨K ∪ K', hK.union hK', fun u hu => ?_⟩, fun k => ?_⟩
  · rw [Set.mem_union, not_or] at hu
    simp [hK0 u hu.1, hK0' u hu.2]
  · obtain ⟨C, hC⟩ := hd k
    obtain ⟨C', hC'⟩ := hd' k
    refine ⟨C + C', fun u => ?_⟩
    have h0 : 0 ≤ (1 + sz u) ^ k := pow_nonneg (by linarith [sz_nonneg u]) k
    calc ‖(Φ + Ψ) u‖ * (1 + sz u) ^ k ≤ (‖Φ u‖ + ‖Ψ u‖) * (1 + sz u) ^ k :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) h0
      _ ≤ C + C' := by rw [add_mul]; exact add_le_add (hC u) (hC' u)

theorem decay_smul (a : ℂ) {Φ : (Fin N → AF F) → ℂ} (h : Decay Φ) : Decay (a • Φ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  refine ⟨hc.const_smul a, ⟨K, hK, fun u hu => by simp [hK0 u hu]⟩, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hd k
  refine ⟨‖a‖ * C, fun u => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg a)

theorem schwartz_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ t, (1 + ‖t‖) ^ k * ‖f t‖ ≤ C := by
  have := fun t => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f t
  simp only [norm_iteratedFDeriv_zero] at this
  exact ⟨_, this⟩

theorem decay_pure (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) : Decay (GlobalTheory.WeilM.pureA F f g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ⟨tsupport g, hg2, fun u hu => ?_⟩, fun k => ?_⟩
  · refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_))
      (hg1.continuous.comp (continuous_pi fun i => ?_))
    · exact continuous_mixed.comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_snd.comp (continuous_apply i)
  · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hu)
  · obtain ⟨B, hB⟩ := hg1.continuous.bounded_above_of_compact_support hg2
    obtain ⟨C, hC⟩ := schwartz_bound f k
    set c : ℝ := N * Fintype.card (InfinitePlace F)
    have hc : 0 ≤ c := by positivity
    refine ⟨(1 + c) ^ k * C * B, fun u => ?_⟩
    set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
    have h1 : 1 + sz u ≤ (1 + c) * (1 + ‖t‖) := by
      have : sz u ≤ c * ‖t‖ := sz_le u
      nlinarith [norm_nonneg t]
    have h2 : (1 + sz u) ^ k ≤ (1 + c) ^ k * (1 + ‖t‖) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [sz_nonneg u]) h1 k
    have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
    calc ‖GlobalTheory.WeilM.pureA F f g u‖ * (1 + sz u) ^ k
        = ‖f t‖ * ‖g fun i => (u i).2‖ * (1 + sz u) ^ k := by rw [← norm_mul]; rfl
      _ ≤ ‖f t‖ * ‖g fun i => (u i).2‖ * ((1 + c) ^ k * (1 + ‖t‖) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 + c) ^ k * ((1 + ‖t‖) ^ k * ‖f t‖) * ‖g fun i => (u i).2‖ := by ring
      _ ≤ (1 + c) ^ k * C * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hC t) (by positivity)) (hB _) (norm_nonneg _) (by positivity)

theorem decay_of_mem_schA (F : Type) [Field F] [NumberField F] (N : ℕ) :
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact decay_pure f g hg
  | zero => exact decay_zero
  | add x y _ _ hx hy => exact decay_add hx hy
  | smul a x _ hx => exact decay_smul a hx

end GlobalTheory.SchwartzDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticFormRealOneParamLineEqZero
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform

theorem symV_realLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  intro F _ _ N hF M hM t s

  let φ : InfinitePlace F → AF F →+* ℝ := fun w =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).comp
      ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)
  have hφ : ∀ w (x : AF F), φ w x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)
      (x.1 w) := fun _ _ => rfl
  have hcont : ∀ w (g : ℝ → AF F), Continuous g → Continuous fun r => φ w (g r) := by
    intro w g hg
    simp only [hφ]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal w)).continuous.comp
      ((continuous_apply w).comp (continuous_fst.comp hg))
  have lin : ∀ (p : VA F N →+ AF F), Continuous p → ∀ w r, φ w (p (M r)) = r * φ w (p (M 1)) := by
    intro p hp w r
    let f : ℝ →+ ℝ := ((φ w).toAddMonoidHom.comp p).comp M
    have hc : Continuous f := hcont w (fun r => p (M r)) (hp.comp hM.1)
    have := map_real_smul f hc r 1
    simpa [f] using this
  have p1 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_fst
  have p2 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.snd _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_snd
  have k1 : ∀ l w r, φ w ((M r).1 l) = r * φ w ((M 1).1 l) := fun l w r => lin _ (p1 l) w r
  have k2 : ∀ l w r, φ w ((M r).2 l) = r * φ w ((M 1).2 l) := fun l w r => lin _ (p2 l) w r
  have hfst : fstA F (symV (M t) (M s)) = 0 := by
    funext w
    apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).injective
    have h : φ w (symV (M t) (M s)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [symV, dotProduct, map_sub, map_sum, map_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [k1 l w t, k1 l w s, k2 l w t, k2 l w s]
      ring
    exact h.trans (map_zero _).symm
  have h0 : ∀ r l, sndA F ((M r).1 l) = 0 ∧ sndA F ((M r).2 l) = 0 := fun r l =>
    ⟨congrFun (hM.2 r).1 l, congrFun (hM.2 r).2 l⟩
  have hsnd : sndA F (symV (M t) (M s)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [symV, dotProduct, map_sub, map_sum, map_mul, (h0 _ _).1, (h0 _ _).2, zero_mul,
      Finset.sum_const_zero, sub_zero]
  exact Prod.ext hfst hsnd

end GlobalTheory.ThetaTransform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLatticeEqComapBlockwiseLattice
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem baseLattice_eq_comap_blockwise_lattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) =
      (blkLat (ι := Fin n' × Fin n) (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 B.lamM))).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  intro D cc δ B n n'
  have h0 : TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) = powLat B.lamM (n * 2) (n' * 2) :=
    Lat0 D cc δ
  rw [h0]

  have himg : ∀ x : Fin 4 × D.what₂.Tau → ℂ,
      B.gC x ∈ imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM) ↔
        x ∈ pow4 B.lamM := by
    intro x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : y = x := B.gC.injective hxy
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  ext z
  simp only [AddSubgroup.mem_comap]
  show (∀ i j, (fun τ => z τ i j) ∈ B.lamM) ↔ ∀ k, (fun w => phi B n n' z (k, w)) ∈ _
  have e : ∀ k, (fun w => phi B n n' z (k, w)) = B.gC (blk D k z) := fun k => rfl
  simp only [e, himg]
  constructor
  · intro h k a
    exact h (posE n n' (k, a)).1 (posE n n' (k, a)).2
  · intro h i j
    have := h ((posE n n').symm (i, j)).1 ((posE n n').symm (i, j)).2
    have e2 : slice ((posE n n').symm (i, j)).2 (blk D ((posE n n').symm (i, j)).1 z) = fun τ => z τ i j := by
      funext τ
      show z τ (posE n n' (((posE n n').symm (i, j)).1, ((posE n n').symm (i, j)).2)).1
        (posE n n' (((posE n n').symm (i, j)).1, ((posE n n').symm (i, j)).2)).2 = z τ i j
      simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    rw [← e2]; exact this

end GlobalTheory.BaseVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumCoordinateEquivIsometry
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

open scoped BigOperators ComplexConjugate

namespace GlobalTheory.BaseVacuum

theorem gC_sum_conj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (x y : Fin 4 × D.what₂.Tau → ℂ) :
    ∑ w, B.gC x w * conj (B.gC y w) = ∑ w, x w * conj (y w) := by
  have hA : ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos_thm B.L).ne'
  have h := B.isomOK x y
  rw [blockFourfold_hOne_eq_hOne] at h
  have e : Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau) = matH (hOne B.L (Fin 4 × D.what₂.Tau)) := rfl
  rw [e] at h
  have h' := h
  simp only [LinearEquiv.coe_coe] at h'
  rw [matH_hOne, matH_hOne] at h'
  exact (div_left_inj' hA).1 h'

theorem phi_isom : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ)
    (z z' : TaylorLogMetric.VC D (n * 2) (n' * 2)),
    TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z' = stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z') := by
  intro D cc δ B n n' z z'
  have eR : Formalism.L2.Th1.H.stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z')
      = (∑ p, phi B n n' z p * conj (phi B n n' z' p)) / ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) := by
    show matH (hOne B.L (Ix D n n')) _ _ = _
    exact matH_hOne _ _ _
  rw [eR]
  have eL : TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z'
      = (∑ τ, ∑ i, ∑ j, z τ i j * conj (z' τ i j)) / ((TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) : ℝ) : ℂ) := rfl
  rw [eL, show TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L from B.areaOK]
  congr 1
  symm
  calc (∑ p, phi B n n' z p * conj (phi B n n' z' p))
      = ∑ k : Fin n' × Fin n, ∑ w, B.gC (blk D k z) w * conj (B.gC (blk D k z') w) := by
        rw [Fintype.sum_prod_type]; rfl
    _ = ∑ k : Fin n' × Fin n, ∑ w, blk D k z w * conj (blk D k z' w) :=
        Finset.sum_congr rfl (fun k _ => gC_sum_conj B (blk D k z) (blk D k z'))
    _ = ∑ p : Ix D n n', blk D p.1 z p.2 * conj (blk D p.1 z' p.2) := (Fintype.sum_prod_type' _).symm
    _ = ∑ τ, ∑ i, ∑ j, z τ i j * conj (z' τ i j) := ?_
  let e : Ix D n n' ≃ D.what₂.Tau × (Fin (n' * 2) × Fin (n * 2)) :=
    ((Equiv.prodAssoc _ _ _).symm.trans ((posE n n').prodCongr (Equiv.refl _))).trans (Equiv.prodComm _ _)
  rw [Fintype.sum_equiv e (fun p => blk D p.1 z p.2 * conj (blk D p.1 z' p.2))
    (fun q => z q.1 q.2.1 q.2.2 * conj (z' q.1 q.2.1 q.2.2)) (fun p => rfl)]
  simp only [Fintype.sum_prod_type]

end GlobalTheory.BaseVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeBasisCoordinateEqCoordinateEqu
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

noncomputable section
namespace GlobalTheory.BaseVacuum
open scoped BigOperators

theorem sum_putB_embT (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E) (τ : D.what₂.Tau)
    (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) :
    (∑ a, ∑ c, z τ a c * (starRingEnd ℂ) (TaylorLogMetric.embT D τ (putB D k x a c)))
      = ∑ b : Fin 4, blk D k z (b, τ) * (starRingEnd ℂ) (emb4 D x (b, τ)) := by
  rw [← Fintype.sum_prod_type' (f := fun a c => z τ a c * (starRingEnd ℂ) (TaylorLogMetric.embT D τ (putB D k x a c)))]
  rw [← (posE n n').sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp [putB, blk, emb4]
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [putB, hk']
  · simp

theorem blockVacuum_coordinate_eq_coordinateEquiv_numbering (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ)
    (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) :
    StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = phi B n n' z (ixE D n n' j) := by
  set k := (ixE D n n' j).1
  set w := (ixE D n n' j).2
  have h1 : StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z
      = ∑ w', blk D k z w' * (starRingEnd ℂ) (emb4 D (xv B w) w') := by
    unfold StandardLatticesGL3.coordB
    rw [Fintype.sum_prod_type_right (f := fun w' : Fin 4 × D.what₂.Tau => blk D k z w' * (starRingEnd ℂ) (emb4 D (xv B w) w'))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact sum_putB_embT D k (xv B w) τ z
  have hg : B.gC (emb4 D (xv B w)) = Pi.single w 1 := by
    rw [show B.gC (emb4 D (xv B w)) = _ from B.gC_spec (xv B w)]
    funext w'
    simp only [xv, LinearEquiv.apply_symm_apply]
    by_cases h : w' = w
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hA : ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos_thm B.L).ne'
  have hI := B.isomOK (blk D k z) (emb4 D (xv B w))
  rw [blockFourfold_hOne_eq_hOne] at hI
  change (matH (hOne B.L (Fin 4 × D.what₂.Tau))) (B.gC (blk D k z)) (B.gC (emb4 D (xv B w))) = _ at hI
  rw [matH_hOne, matH_hOne, div_left_inj' hA, hg] at hI
  rw [h1, ← hI, phi_apply]
  simp [Pi.single_apply]
  rfl

theorem coordB_bas_eq_phi : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = phi B n n' z (ixE D n n' j) :=
  blockVacuum_coordinate_eq_coordinateEquiv_numbering

end GlobalTheory.BaseVacuum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVacuumLatticeEqComapStandardLattice
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem gC_xv {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) :
    B.gC (fun w' => TaylorLogMetric.embT D w'.2 (xv B w w'.1)) = Pi.single w 1 := by
  rw [B.gC_spec]
  funext w'
  simp only [xv, LinearEquiv.apply_symm_apply]
  by_cases h : w' = w
  · subst h; simp
  · simp [h]

theorem blk_embV_putB (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {n n' : ℕ} (k k' : Fin n' × Fin n)
    (x : Fin 4 → D.host.E) :
    blk D k' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (putB D k x) : TaylorLogMetric.VC D (n * 2) (n' * 2)) =
      if k' = k then (fun w => TaylorLogMetric.embT D w.2 (x w.1)) else (0 : Fin 4 × D.what₂.Tau → ℂ) := by
  funext w
  simp only [blk, TaylorLogMetric.embV, TaylorLogMetric.tor0, putB, Prod.mk.eta, Equiv.symm_apply_apply]
  by_cases h : k' = k
  · simp [h]
  · simp [h]

theorem phi_embV_bas {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ)
    (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) :
    phi B n n' (TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' j)) = Pi.single (ixE D n n' j) 1 := by
  funext p
  rw [phi_apply, bas, blk_embV_putB]
  by_cases h : p.1 = (ixE D n n' j).1
  · rw [if_pos h, gC_xv]
    by_cases h2 : p.2 = (ixE D n n' j).2
    · have : p = ixE D n n' j := Prod.ext h h2
      subst this; simp
    · have : p ≠ ixE D n n' j := fun e => h2 (by rw [e])
      simp [h2, this]
  · rw [if_neg h, B.gC.map_zero]
    have : p ≠ ixE D n n' j := fun e => h (by rw [e])
    simp [this]

theorem laB_eq_comap : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ),
    StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') =
      (stdLat B.L (Ix D n n')).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  intro D cc δ B n n'
  apply le_antisymm
  · unfold StandardLatticesGL3.LaB
    rw [AddSubgroup.closure_le]
    rintro z ⟨w, hw, j, rfl⟩
    show phi B n n' (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' j)) ∈ stdLat B.L (Ix D n n')
    rw [map_smul, phi_embV_bas]
    have hw' : w ∈ B.L.lattice.toAddSubgroup := by rw [B.lat]; exact hw
    simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies]
    intro p
    by_cases h : p = ixE D n n' j
    · subst h; simpa using hw'
    · simp [h]
  · intro x hx
    have hx' : phi B n n' x ∈ stdLat B.L (Ix D n n') := hx
    simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies] at hx'
    have hsum : phi B n n' x = ∑ p, phi B n n' x p • (Pi.single p 1 : Ix D n n' → ℂ) := by
      funext q
      simp [Finset.sum_apply, Pi.single_apply]
    have hsing : ∀ p, (phi B n n').symm (Pi.single p 1) =
        TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p)) := by
      intro p
      rw [LinearEquiv.symm_apply_eq, phi_embV_bas, Equiv.apply_symm_apply]
    have hxe : x = ∑ p, phi B n n' x p • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (bas B n n' ((ixE D n n').symm p)) := by
      conv_lhs => rw [← (phi B n n').symm_apply_apply x, hsum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smul, hsing]
    rw [hxe]
    refine AddSubgroup.sum_mem _ fun p _ => AddSubgroup.subset_closure ?_
    refine ⟨phi B n n' x p, ?_, (ixE D n n').symm p, rfl⟩
    have := hx' p
    rw [B.lat] at this
    exact this

end GlobalTheory.BaseVacuum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumPrincipalLevelEqCardMulClassSum
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem change_of_level_classSum : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (v : InfinitePlace X.K) (F' : (mtildeKGSD W Ch sel mu).EqFun), F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun → (mtildeKGSD W Ch sel mu).ipAt (mtildeKOk W Ch sel mu hX) v F'.1 F'.1 = (Nat.card P.grp : ℂ) * (mtildeGSD W Ch sel mu P).ipAt (mtildeOk W Ch sel mu hX P) v F'.1 F'.1 := by
  intro X Pr R W Ch sel S mu P hX v F' hF
  obtain ⟨ι, hinj, hact, hidx⟩ := _root_.GlobalTheory.RowLevIndex.index_eq W Ch sel mu P
  have hK := mtildeKOk W Ch sel mu hX
  have hP := mtildeOk W Ch sel mu hX P
  have hf : ∀ (g : (mtildeGSD W Ch sel mu P).G) (d : (mtildeGSD W Ch sel mu P).D),
      (mtildeGSD W Ch sel mu P).pairAt v (F'.1 (g • d)) (F'.1 (g • d)) =
      (mtildeGSD W Ch sel mu P).pairAt v (F'.1 d) (F'.1 d) := by
    intro g d
    rw [hF g d]
    exact GlobalTheory.PeriodOnStep.pairAt_rho v _ hP (GlobalTheory.PeriodOnStep.row_act_rat W Ch sel mu P hX) g _
  have hfi : ι.range.FiniteIndex := ⟨by rw [hidx]; exact Nat.card_pos.ne'⟩
  have key := @_root_.GlobalTheory.OrbitMass.mass_formula (mtildeGSD W Ch sel mu P).G (mtildeKGSD W Ch sel mu).G (mtildeGSD W Ch sel mu P).D _ _ _ _ ι hinj hact hfi
    hP.fin_stab (mtildeOk W Ch sel mu hX P).fintypeCl (mtildeKOk W Ch sel mu hX).fintypeCl
    (fun d => (mtildeGSD W Ch sel mu P).pairAt v (F'.1 d) (F'.1 d)) hf
  rw [hidx] at key
  unfold GSD.ipAt
  refine Eq.trans ?_ (key.trans ?_)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [@Nat.card_eq_fintype_card _ ((mtildeKOk W Ch sel mu hX).fintypeStab _)]
    rfl
  · congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [@Nat.card_eq_fintype_card _ ((mtildeOk W Ch sel mu hX P).fintypeStab _)]
    rfl

end GlobalTheory
end

