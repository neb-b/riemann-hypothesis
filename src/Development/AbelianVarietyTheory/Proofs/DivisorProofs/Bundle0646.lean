module

public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Mathlib
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0626
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtWeightAddNsmulLargeOnCompact
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.LeviLarge

theorem contDiffAt_ph {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (la : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) :
    ContDiffAt ℝ 2 (A.ph la i ∘ (A.chart i).symm) (A.chart i y) :=
  ((A.smooth_ph la i).contDiffAt
    ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hy))).of_le (WithTop.coe_le_coe.2 le_top)

theorem leviAt_ph_nsmul {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (G H : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source)
    (ξ : Fin n → ℂ) : ∀ k : ℕ,
    A.leviAt i (A.ph (G + k • H) i) y ξ = A.leviAt i (A.ph G i) y ξ + k * A.leviAt i (A.ph H i) y ξ
  | 0 => by simp
  | k + 1 => by
    have e : A.ph (G + (k + 1) • H) i =ᶠ[𝓝 y] fun x => A.ph (G + k • H) i x + A.ph H i x := by
      filter_upwards [(A.chart i).open_source.mem_nhds hy] with x hx
      rw [succ_nsmul, ← add_assoc, A.ph_add _ _ i x hx]
    rw [leviAt_congr A i _ _ y hy e ξ,
      leviAt_add A i _ _ y (contDiffAt_ph A _ i hy) (contDiffAt_ph A _ i hy) ξ,
      leviAt_ph_nsmul A G H i hy ξ k]
    push_cast; ring

theorem re_leviV_lower {n : ℕ} (g : V n → ℂ) (u : V n) (B : ℝ)
    (hFu : ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ ≤ B) (ξ : Fin n → ℂ) :
    -(2 * B) * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n g u ξ).re := by
  have hS0 : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : ∀ j k, ‖ξ j‖ * ‖ξ k‖ ≤ 2 * ∑ j, ‖ξ j‖ ^ 2 := by
    intro j k
    have h1 : ‖ξ j‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : ‖ξ k‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    nlinarith [sq_nonneg (‖ξ j‖ - ‖ξ k‖), norm_nonneg (ξ j), norm_nonneg (ξ k)]
  have hnorm : ‖leviV n g u ξ‖ ≤ ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ * (2 * ∑ j, ‖ξ j‖ ^ 2) := by
    unfold leviV
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
    rw [norm_mul, norm_mul, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hS j k) (norm_nonneg _)
  have h3 : ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ * (2 * ∑ j, ‖ξ j‖ ^ 2) =
      (∑ j, ∑ k, ‖wd n j (wdb n k g) u‖) * (2 * ∑ j, ‖ξ j‖ ^ 2) := by
    rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]
  have h4 := Complex.abs_re_le_norm (leviV n g u ξ)
  have h5 := neg_abs_le (leviV n g u ξ).re
  have h6 := mul_le_mul_of_nonneg_right hFu (by positivity : (0:ℝ) ≤ 2 * ∑ j, ‖ξ j‖ ^ 2)
  linarith

theorem curv_large : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (i : ι) (K : Set (V n)) (t : ℝ), IsCompact K → K ⊆ (A.chart i).target → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ v ∈ K, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt i (A.ph (G + k • H) i) ((A.chart i).symm v) ξ := by
  intro n Y _ _ _ _ _ ι La _ A H G hH i K t hK hKU
  have hU : IsOpen (A.chart i).target := (A.chart i).open_target
  have hsm : ∀ la : La, ContDiffOn ℝ ∞ (fun v => ((A.ph la i ((A.chart i).symm v) : ℝ) : ℂ))
      (A.chart i).target :=
    fun la => Complex.ofRealCLM.contDiff.comp_contDiffOn (A.smooth_ph la i)
  obtain ⟨c, hc, hcK⟩ := levi_pos_compact hU (hsm H) hK hKU (fun u hu ζ hζ => by
    have hyu := (A.chart i).map_target (hKU hu)
    have hne : ζ.ofLp ≠ 0 := by simpa using hζ
    have := hH i _ hyu ζ.ofLp hne
    simpa [WeightedAtlas.leviAt, (A.chart i).right_inv (hKU hu)] using this)
  have hF : ContinuousOn (fun u => ∑ j, ∑ k,
      ‖wd n j (wdb n k (fun v => ((A.ph G i ((A.chart i).symm v) : ℝ) : ℂ))) u‖) K :=
    continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
      ((continuousOn_wd_wdb hU (hsm G) j k).mono hKU).norm
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨⌈(t + 2 * B) / c⌉₊, fun k hk v hv ξ => ?_⟩
  have hy := (A.chart i).map_target (hKU hv)
  rw [leviAt_ph_nsmul A G H i hy ξ k]
  simp only [WeightedAtlas.leviAt, (A.chart i).right_inv (hKU hv)]
  have hFu := (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hB v hv)
  have hG := re_leviV_lower _ v B hFu ξ
  have hc' := hcK v hv (WithLp.toLp 2 ξ)
  rw [EuclideanSpace.norm_sq_eq] at hc'
  simp only [PiLp.toLp_apply, WithLp.ofLp_toLp] at hc'
  have hk' : (t + 2 * B) / c ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hkc : t + 2 * B ≤ k * c := by rwa [div_le_iff₀ hc] at hk'
  have hS0 : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg (α := ℝ) k)
  have h2 := mul_le_mul_of_nonneg_right hkc hS0
  nlinarith

end GlobalTheory.OTY.LeviLarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormTwistedWeightLowerBound
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.LeviTwistLower

theorem main : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (z : M → V n) (φ ψ : M → ℝ) (δ : ℝ) (κ : ℝ → ℝ), IsLocalHomeomorph z → SmoothR n z φ → SmoothR n z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → ContDiff ℝ ∞ κ → (∀ t, t ≤ 0 → 0 ≤ deriv κ t ∧ deriv κ t ≤ 1) → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n z (fun x => φ x + α * ψ x)) → SmoothR n z (fun x => κ (δ * ψ x)) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n z (fun y => ((κ (δ * ψ y) : ℝ) : ℂ)) x ξ = ((deriv κ (δ * ψ x) * δ : ℝ) : ℂ) * dbarDot n z (fun y => (ψ y : ℂ)) x ξ ∧ deriv (deriv κ) (δ * ψ x) * (δ ^ 2 * ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤ (Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
  intro n M _ _ _ _ _ z φ ψ δ κ hz hφ hψ hψ0 hδ hκ hκ' hL
  obtain ⟨hκd, hκ1⟩ := contDiff_infty_iff_deriv.1 hκ
  have hκdd : Differentiable ℝ (deriv κ) := (contDiff_infty_iff_deriv.1 hκ1).1
  set k : ℝ → ℝ := fun t => κ (δ * t) with hkdef
  have hk : ContDiff ℝ ∞ k := hκ.comp (contDiff_const.mul contDiff_id)
  have hD : ∀ t, HasDerivAt k (deriv κ (δ * t) * δ) t := by
    intro t
    have h := (hκd (δ * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul δ)
    simpa [hkdef, Function.comp_def] using h
  have hDk : deriv k = fun t => deriv κ (δ * t) * δ := funext fun t => (hD t).deriv
  have hDD : ∀ t, deriv (deriv k) t = deriv (deriv κ) (δ * t) * δ ^ 2 := by
    intro t
    rw [hDk]
    have h := ((hκdd (δ * t)).hasDerivAt.comp t ((hasDerivAt_id t).const_mul δ)).mul_const δ
    exact h.deriv.trans (by ring)
  have hks : SmoothR n z (fun x => κ (δ * ψ x)) := SmoothR.comp n z k hk ψ hψ
  refine ⟨hks, fun x ξ => ⟨?_, ?_⟩⟩
  · unfold dbarDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := db_comp_real n z k hk ψ (SmoothR.ckR n z 1 _ hψ) j x
    rw [(hD (ψ x)).deriv] at this
    change db n z j (fun y => ((k (ψ y) : ℝ) : ℂ)) x * _ = _
    rw [this]; ring
  · have hC := chain n M z hz k ψ (contDiff_infty.1 hk 2) hψ x ξ
    rw [(hD (ψ x)).deriv, hDD (ψ x)] at hC
    have hnorm : ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ = ‖dDot n z (fun y => (ψ y : ℂ)) x ξ‖ := by
      have : dbarDot n z (fun y => (ψ y : ℂ)) x ξ = (starRingEnd ℂ) (dDot n z (fun y => (ψ y : ℂ)) x ξ) := by
        unfold dbarDot dDot
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [db_ofReal n z ψ j x, map_mul]
      rw [this, Complex.norm_conj]
    have hsum : Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ =
        Levi n z φ x ξ + Levi n z ψ x ξ + Levi n z (fun y => k (ψ y)) x ξ := by
      rw [levi_add n z (fun y => φ y + ψ y) (fun y => κ (δ * ψ y))
        (SmoothR.ckR n z 2 _ (SmoothR.add n z _ _ hφ hψ)) (SmoothR.ckR n z 2 _ hks) x ξ,
        levi_add n z φ ψ (SmoothR.ckR n z 2 _ hφ) (SmoothR.ckR n z 2 _ hψ) x ξ]
    set α : ℝ := 1 + δ * deriv κ (δ * ψ x) with hα
    have hmem : α ∈ Set.Icc (1 : ℝ) (1 + δ) := by
      obtain ⟨h0, h1⟩ := hκ' (δ * ψ x) (mul_nonpos_of_nonneg_of_nonpos hδ.le (hψ0 x))
      constructor
      · nlinarith
      · nlinarith
    have hnn := hL α hmem x ξ
    rw [levi_add n z φ (fun y => α * ψ y) (SmoothR.ckR n z 2 _ hφ)
      (SmoothR.ckR n z 2 _ (SmoothR.mul n z _ _ (smoothR_const n z α) hψ)) x ξ,
      levi_const_mul n z α ψ (SmoothR.ckR n z 2 _ hψ) x ξ] at hnn
    rw [hsum, hC, hnorm]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hnn ⊢
    rw [hα] at hnn
    nlinarith

end GlobalTheory.LeviTwistLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviPiTensorRepresentationIsIrreducible
section
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV GlobalTheory.HcIrr

namespace GlobalTheory.HcIrr

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
  [∀ i, Module ℂ (V i)]

theorem map_mem_of_position_stable (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ (c : ι) (f : V c →ₗ[ℂ] V c), ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W)
    (f : ∀ i, V i →ₗ[ℂ] V i) : ∀ x ∈ W, PiTensorProduct.map f x ∈ W := by
  suffices H : ∀ S : Finset ι, ∀ x ∈ W,
      PiTensorProduct.map (fun c => if c ∈ S then f c else LinearMap.id) x ∈ W by
    intro x hx
    simpa using H Finset.univ x hx
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro x hx
    simpa [PiTensorProduct.map_id] using hx
  | insert a S ha ih =>
    intro x hx
    have e : (fun c => if c ∈ insert a S then f c else (LinearMap.id : V c →ₗ[ℂ] V c)) = fun c =>
        (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) a (f a)) c ∘ₗ
          (if c ∈ S then f c else LinearMap.id) := by
      funext c
      by_cases hc : c = a
      · subst hc
        simp [ha]
      · simp [hc, Function.update_of_ne]
    rw [e, PiTensorProduct.map_comp]
    exact h a (f a) _ (ih x hx)

theorem position_stable_of_span {c : ι} {G : Type} [Group G] (ρ : Representation ℂ G (V c))
    (hs : Submodule.span ℂ (Set.range ρ) = ⊤) (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ g : G, ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (ρ g)) x ∈ W)
    (f : V c →ₗ[ℂ] V c) : ∀ x ∈ W, PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c f) x ∈ W := by
  have hf : f ∈ Submodule.span ℂ (Set.range ρ) := hs ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g, rfl⟩ := hf
    exact h g
  | zero =>
    intro x _
    have := PiTensorProduct.map_update_smul (fun c' => (LinearMap.id : V c' →ₗ[ℂ] V c')) c (0 : ℂ)
      LinearMap.id
    rw [zero_smul, zero_smul] at this
    rw [this]
    simp
  | add u v _ _ hu hv =>
    intro x hx
    rw [PiTensorProduct.map_update_add, LinearMap.add_apply]
    exact add_mem (hu x hx) (hv x hx)
  | smul a u _ hu =>
    intro x hx
    rw [PiTensorProduct.map_update_smul, LinearMap.smul_apply]
    exact W.smul_mem _ (hu x hx)

theorem eq_bot_or_top_of_map_stable [∀ i, FiniteDimensional ℂ (V i)]
    (W : Submodule ℂ (PiTensorProduct ℂ V))
    (h : ∀ f : ∀ i, V i →ₗ[ℂ] V i, ∀ x ∈ W, PiTensorProduct.map f x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  let e := fun c => Module.finBasis ℂ (V c)
  let B := Basis.piTensorProduct e
  obtain ⟨I, hI⟩ : ∃ I, B.repr x I ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (B.repr.map_eq_zero_iff.1 (Finsupp.ext hc))
  have hJ : ∀ J, B J ∈ W := by
    intro J
    let f : ∀ c, V c →ₗ[ℂ] V c := fun c => ((e c).coord (I c)).smulRight (e c (J c))
    have hf : PiTensorProduct.map f = (B.coord I).smulRight (B J) := by
      refine B.ext fun p => ?_
      have hc : ∀ c, f c (e c (p c)) = (if p c = I c then (1 : ℂ) else 0) • e c (J c) := by
        intro c
        simp [f, Finsupp.single_apply]
      have hq : (∏ c, if p c = I c then (1 : ℂ) else 0) = if p = I then 1 else 0 := by
        rw [Finset.prod_ite_zero]
        simp [funext_iff]
      rw [LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [B, Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, hc,
        MultilinearMap.map_smul_univ, RingHom.id_apply, hq]
    have hm := h f x hx
    rw [hf, LinearMap.smulRight_apply, Module.Basis.coord_apply] at hm
    exact (W.smul_mem_iff hI).1 hm
  refine eq_top_iff.2 ?_
  rw [← B.span_eq]
  exact Submodule.span_le.2 (by rintro _ ⟨J, rfl⟩; exact hJ J)

theorem nontrivial_piTensorProduct [∀ i, FiniteDimensional ℂ (V i)] [∀ i, Nontrivial (V i)] :
    Nontrivial (PiTensorProduct ℂ V) := by
  let B := Basis.piTensorProduct fun c => Module.finBasis ℂ (V c)
  exact ⟨B fun c => ⟨0, Module.finrank_pos⟩, 0, B.ne_zero _⟩

end General

theorem leviTensor_isIrreducible : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ)
    (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)),
    (∀ c, Simple (lam c)) → (leviTensor b lam).IsIrreducible := by
  intro K _ _ _ r s b lam hs
  have hirr := fun c => GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple (lam c) (hs c)
  have hspan := fun c => GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ (lam c).ρ (hirr c)
  haveI : ∀ c, Nontrivial (lam c : Type) := fun c =>
    GlobalTheory.OuterTensor.nontrivial_of_isIrreducible _ (hirr c)
  haveI : Nontrivial (PiTensorProduct ℂ (fun c => (lam c : Type))) := nontrivial_piTensorProduct
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h :
      (⊥ : Submodule ℂ (PiTensorProduct ℂ (fun c => (lam c : Type)))) = ⊤)
  have hstable : ∀ (c : Fin s) (f : (lam c : Type) →ₗ[ℂ] (lam c : Type)), ∀ x ∈ S.toSubmodule,
      PiTensorProduct.map (Function.update
        (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c f) x ∈ S.toSubmodule := by
    intro c
    refine position_stable_of_span (lam c).ρ (hspan c) S.toSubmodule fun g x hx => ?_
    rw [← leviTensor_blockExt b lam c g]
    exact S.apply_mem_toSubmodule _ hx
  rcases eq_bot_or_top_of_map_stable S.toSubmodule (map_mem_of_position_stable _ hstable) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end GlobalTheory.HcIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerEqOneOfCuspidal
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module Matrix

variable {F : Type} [Field F] {r : ℕ}

section Nonvanishing

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

end Nonvanishing

section Embedding

variable {d d' : ℕ}

variable (b : Fin r → ℕ) (c : ℕ)

end Embedding

section Main

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

theorem leviWh_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → leviWh ψ b σ = 1 := by
  first
  | exact @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | (apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one ..)

end Main

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPart
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem lintegral_nsq_chart_part : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (i : ι) (W : Set (V n)) (D : ι → Y → ℂ), MeasurableSet W → W ⊆ (A.chart i).target → (∀ y ∈ (A.chart i).source, A.chart i y ∈ W → D (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D i y) → AEMeasurable (D i ∘ (A.chart i).symm) (volume.restrict W) → ∫⁻ y in (A.chart i).source ∩ A.chart i ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu = ∫⁻ v in W, ENNReal.ofReal (‖D i ((A.chart i).symm v)‖ ^ 2 * Real.exp (-A.ph la i ((A.chart i).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A la i W D hW hWt hD hae
  classical
  set e := A.chart i with he
  have hS : MeasurableSet e.source := e.open_source.measurableSet
  have hT : MeasurableSet e.target := e.open_target.measurableSet

  set c : Y → V n := e.source.piecewise e (fun _ => 0) with hc
  have hcm : Measurable c :=
    ContinuousOn.measurable_piecewise e.continuousOn continuousOn_const hS
  set P : V n → ℝ := e.target.piecewise (fun v => A.ph (A.kap + la) i (e.symm v)) (fun _ => 0) with hP
  have hPm : Measurable P :=
    ContinuousOn.measurable_piecewise (A.smooth_ph (A.kap + la) i).continuousOn continuousOn_const hT
  set D' : V n → ℂ := hae.mk _ with hD'
  have hD'm : Measurable D' := hae.measurable_mk
  have hDD' : (D i ∘ e.symm) =ᵐ[volume.restrict W] D' := hae.ae_eq_mk
  have hcs : ∀ y ∈ e.source, c y = e y := fun y hy => by simp [hc, hy]
  have hPt : ∀ v ∈ e.target, P v = A.ph (A.kap + la) i (e.symm v) := fun v hv => by simp [hP, hv]
  set S : Set Y := e.source ∩ c ⁻¹' W with hSdef
  have hSm : MeasurableSet S := hS.inter (hcm hW)
  have hSeq : e.source ∩ e ⁻¹' W = S := by
    ext y; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa [hcs y h1] using h2⟩
  set G : Y → ℝ≥0∞ := S.indicator (fun y => ENNReal.ofReal (‖D' (c y)‖ ^ 2 * Real.exp (-P (c y))))
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hSm
    exact ENNReal.measurable_ofReal.comp
      (((hD'm.comp hcm).norm.pow_const 2).mul ((hPm.comp hcm).neg.exp))

  set T : Set (V n) := toMeasurable (volume.restrict W) {v | ¬ (D i ∘ e.symm) v = D' v}
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : volume.restrict W T = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hDD'
  set E : Set Y := e.source ∩ c ⁻¹' (T ∩ W)
  have hEm : MeasurableSet E := hS.inter (hcm (hTm.inter hW))
  have hE0 : A.mu E = 0 := by
    rw [A.mu_chart i E hEm Set.inter_subset_left]
    apply setLIntegral_measure_zero
    refine measure_mono_null ?_ (show volume (T ∩ W) = 0 by
      rwa [Measure.restrict_apply hTm] at hT0)
    rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    simpa [hcs y hy1] using hy2

  have hL : ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
      ∫⁻ y in e.source, G y ∂A.mu := by
    rw [hSeq]
    have h1 : ∫⁻ y in S, ENNReal.ofReal (A.nsq (A.kap + la) D y) ∂A.mu =
        ∫⁻ y in e.source, S.indicator (fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y)) y ∂A.mu := by
      rw [lintegral_indicator hSm, Measure.restrict_restrict hSm,
        Set.inter_eq_left.mpr Set.inter_subset_left]
    rw [h1]
    apply lintegral_congr_ae
    have hnE : ∀ᵐ y ∂A.mu, y ∉ E := measure_eq_zero_iff_ae_notMem.mp hE0
    filter_upwards [ae_restrict_of_ae hnE, ae_restrict_mem hS] with y hyE hys
    by_cases hyS : y ∈ S
    · simp only [G, Set.indicator_of_mem hyS]
      congr 1
      have hyW : e y ∈ W := by simpa [hcs y hys] using hyS.2
      have hyT : e y ∉ T := fun h => hyE ⟨hys, by simp [hcs y hys, h, hyW]⟩
      have hDy : D i y = D' (c y) := by
        rw [hcs y hys]
        have : (D i ∘ e.symm) (e y) = D' (e y) := by
          by_contra hne
          exact hyT (subset_toMeasurable _ _ hne)
        simpa [e.left_inv hys] using this
      have hPy : P (c y) = A.ph (A.kap + la) i y := by
        rw [hcs y hys, hPt _ (e.map_source hys), e.left_inv hys]
      rw [← hDy, hPy]

      unfold WeightedAtlas.nsq
      have hp := A.mem_pick y
      have hg := A.g_ne (A.kap + la) (A.pick y) i y hp hys
      have hg2 : 0 < ‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2 := by positivity
      have ht := A.ph_trans (A.kap + la) (A.pick y) i y hp hys
      rw [hD y hys hyW, norm_mul, mul_pow]
      have : A.ph (A.kap + la) (A.pick y) y =
          A.ph (A.kap + la) i y + Real.log (‖A.g (A.kap + la) (A.pick y) i y‖ ^ 2) := by linarith
      rw [this, neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hg2]
      field_simp
    · simp [G, Set.indicator_of_notMem hyS]

  rw [hL, ap_lintegral_chart A i G hGm]
  have h2 : ∫⁻ v in e.target, G (e.symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v))) =
      ∫⁻ v in e.target, W.indicator (fun v => ENNReal.ofReal (‖D' v‖ ^ 2 * Real.exp (-P v)) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i (e.symm v)))) v := by
    refine setLIntegral_congr_fun hT fun v hv => ?_
    have hs := e.map_target hv
    have hcv : c (e.symm v) = v := by rw [hcs _ hs, e.right_inv hv]
    by_cases hvW : v ∈ W
    · have : e.symm v ∈ S := ⟨hs, by simpa [hcv] using hvW⟩
      simp only [G, Set.indicator_of_mem this, Set.indicator_of_mem hvW, hcv]
    · have : e.symm v ∉ S := fun h => hvW (by simpa [hcv] using h.2)
      simp [G, Set.indicator_of_notMem this, Set.indicator_of_notMem hvW]
  rw [h2, lintegral_indicator hW, Measure.restrict_restrict hW, Set.inter_eq_left.mpr hWt]
  apply lintegral_congr_ae
  filter_upwards [hDD', ae_restrict_mem hW] with v hv hvW
  have hvt := hWt hvW
  have hs := e.map_target hvt
  simp only [Function.comp_apply] at hv
  rw [← hv, hPt v hvt, A.ph_add A.kap la i _ hs, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [neg_add, Real.exp_add]
  have := Real.exp_pos (A.ph A.kap i (e.symm v))
  rw [Real.exp_neg (A.ph A.kap i _)]
  field_simp

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjOfStrictHenselisationPolynomialStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surj_of_strictHenselisation_polynomial_alt : ∀ (T : Type) [CommRing T] (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → (∀ a : A, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] A), a ∈ φ.range) → ∃ (O : Type) (_ : CommRing O) (_ : Algebra T O) (_ : Algebra (Polynomial T) O) (_ : IsScalarTower T (Polynomial T) O) (_ : HenselianLocalRing O) (_ : IsSepClosed (IsLocalRing.ResidueField O)) (π : O →ₐ[Polynomial T] A), Function.Surjective π ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) := by
  first | (exact @GlobalTheory.surj_of_strictHenselisation_polynomial) | (exact GlobalTheory.surj_of_strictHenselisation_polynomial) | (intros; apply GlobalTheory.surj_of_strictHenselisation_polynomial  <;> assumption)
end

