module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRStarDepthLeOfCentreBound
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

namespace StarUpper

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m m' : ℕ}

theorem inCone_cell {n : ℕ} {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hγ' : IsCell bar φ γ')
    {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X) (hβp : ∀ i y, 0 ≤ β i y y)
    {a : Fin n → ℝ} {b : Fin m' → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hlin : evalR φ (∑ i, a i • toReal (β i)) = ∑ i, a i * φ.evalZ (β i))
    (hrel : ∑ i, a i • toReal (β i) = ∑ j, b j • toReal (γ' j)) :
    ∀ i, a i ≠ 0 → ∃ (k : ℕ) (d : Fin m' → ℕ), 0 < k ∧ k • β i = ∑ j, d j • γ' j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have hsum : ∑ i, a i * (ℓ (β i) : ℝ) = ∑ j, b j * (ℓ (γ' j) : ℝ) := by
    have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim β γ') (c := Sum.elim a (-b)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hrel,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
    linarith
  have hφ : ∑ i, a i * φ.evalZ (β i) = ∑ j, b j * φ.evalZ (γ' j) := by
    rw [← hlin, hrel]; exact (linearOn_iff φ γ').1 hγ'.linear b hb
  have hterm : ∑ i, a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hsum, show ∑ i, a i * (N * φ.evalZ (β i)) = N * ∑ i, a i * φ.evalZ (β i) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, hφ, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by rw [h1]; ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * ((ℓ (β i) : ℝ) - N * φ.evalZ (β i)) := fun i _ =>
    mul_nonneg (ha i) (sub_nonneg.2 (h2 _ (hβ i) (hβp i)))
  intro i hi
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hterm i (Finset.mem_univ _)
  have he : (N : ℝ) * φ.evalZ (β i) = ℓ (β i) := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hi
    · linarith
  exact h3 _ (hβ i) (hβp i) he


omit [Module O X] [Module.Finite O X] in
theorem sum_mem_rcone {p : ℕ} {δ : Fin p → LinearMap.BilinForm ℤ X} {γ : Fin m → LinearMap.BilinForm ℤ X}
    (x : Fin p → ℝ) (hx : ∀ i, 0 ≤ x i)
    (h : ∀ i, x i ≠ 0 → ∃ (k : ℕ) (d : Fin m → ℕ), 0 < k ∧ k • δ i = ∑ j, d j • γ j) :
    ∑ i, x i • toReal (δ i) ∈ rcone γ := by
  classical
  have hi : ∀ i, ∃ g : Fin m → ℝ, (∀ j, 0 ≤ g j) ∧ x i • toReal (δ i) = ∑ j, g j • toReal (γ j) := by
    intro i
    by_cases h0 : x i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    obtain ⟨k, d, hk, hkd⟩ := h i h0
    have hxi := hx i
    refine ⟨fun j => x i / k * d j, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
    have e := LinearMap.congr_fun₂ hkd a b
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul, smul_eq_mul] at e
    have e' : (k : ℝ) * (δ i a b : ℝ) = ∑ j, (d j : ℝ) * (γ j a b : ℝ) := by exact_mod_cast e
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    calc x i * (δ i a b : ℝ) = x i / k * ((k : ℝ) * (δ i a b : ℝ)) := by field_simp
      _ = _ := by rw [e', Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  choose g hg hgs using hi
  refine ⟨fun j => ∑ i, g i j, fun j => Finset.sum_nonneg fun i _ => hg i j, ?_⟩
  rw [Finset.sum_congr rfl fun i _ => hgs i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

end StarUpper


open StarUpper in
theorem evalR_starDepth_le : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (s : ℝ),
    IsCell bar ψ γ → B ∈ rcone γ → 0 ≤ s → (∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v →
      ∀ t : ℝ, 0 < t → B - t • toReal v ∈ rcone γ → t ≤ s) → evalR (starDepth bar ψ w) B ≤ s := by
  intro O _ bar ψ w X _ _ _ m γ B s hγ hB hs H
  obtain ⟨c, hc, hBc⟩ := hB
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' O X
  show (starDepth bar ψ w).eval X (fun a b => B a b) ≤ s
  rw [InvFun.eval_eq _ hq]
  refine Real.sSup_le (fun t ht => ?_) hs
  obtain ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB₁, ht0, m₁, γ₁, v₁, hγ₁, hv₁, hv₁p, hwv₁, ⟨e, he, hev⟩, -,
    ⟨d, hd, hdv⟩⟩ := ht
  rcases ht0.eq_or_lt with rfl | htpos
  · exact hs

  have hker : LinearMap.ker q ≤ LinearMap.ker ρ := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    refine hrad _ fun y => ?_
    obtain ⟨y', rfl⟩ := hρ y
    have h1 := hB₁ x y'
    simp only [hx, map_zero, LinearMap.zero_apply] at h1
    exact h1.symm
  let ρ' : X →ₗ[O] X₁ := (LinearMap.ker q).liftQ ρ hker ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hρ' : ∀ a, ρ' (q a) = ρ a := fun a => by
    have : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hρs : Function.Surjective ρ' := fun x => by
    obtain ⟨a, rfl⟩ := hρ x
    exact ⟨q a, hρ' a⟩
  have hBB : ∀ x y, B x y = B₁ (ρ' x) (ρ' y) := fun x y => by
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [hρ', hρ']
    exact hB₁ a b

  set δ : Fin m₁ → LinearMap.BilinForm ℤ X := fun i => pull ρ' (γ₁ i) with hδ
  set v : LinearMap.BilinForm ℤ X := pull ρ' v₁ with hv
  have hv_eq : toReal v = ∑ i, e i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hev (ρ' a) (ρ' b)
    simpa [hδ, hv, LinearMap.sum_apply] using this
  have hd_eq : B - t • toReal v = ∑ i, d i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ hdv (ρ' a) (ρ' b)
    simpa [hδ, hv, hBB, LinearMap.sum_apply] using this
  have hrel : ∑ i, (d i + t * e i) • toReal (δ i) = ∑ j, c j • toReal (γ j) := by
    rw [← hBc]
    refine LinearMap.ext₂ fun a b => ?_
    have h1 := LinearMap.congr_fun₂ hd_eq a b
    have h2 := LinearMap.congr_fun₂ hv_eq a b
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at h1 h2 ⊢
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← h1, ← h2]
    ring
  have hnn : ∀ i, 0 ≤ d i + t * e i := fun i => add_nonneg (hd i) (mul_nonneg ht0 (he i))
  have hlin : evalR ψ (∑ i, (d i + t * e i) • toReal (δ i)) = ∑ i, (d i + t * e i) * ψ.evalZ (δ i) :=
    (linearOn_iff ψ δ).1 ((linearOn_pull_iff hρs).2 hγ₁.linear) _ hnn
  have hcone := inCone_cell hγ (fun i => pull_mem ρ' (hγ₁.mem i)) (fun i y => hγ₁.nonneg i _) hnn hc hlin hrel
  have hInR : InRCone γ v := by
    obtain ⟨c', hc', h'⟩ := sum_mem_rcone e he fun i hi => hcone i
      (add_pos_of_nonneg_of_pos (hd i) (mul_pos htpos (lt_of_le_of_ne (he i) (Ne.symm hi)))).ne'
    exact ⟨c', hc', hv_eq.trans h'⟩
  have hBt : B - t • toReal v ∈ rcone γ := by
    rw [hd_eq]
    exact sum_mem_rcone d hd fun i hi => hcone i
      (add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hd i) (Ne.symm hi)) (mul_nonneg ht0 (he i))).ne'
  exact H v (pull_mem ρ' hv₁) (fun y => hv₁p _) (by rw [hv, evalZ_pull w hρs]; exact hwv₁) hInR t htpos hBt

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellOfContactSetIntInequalities
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

section Contact

variable {X : Type} [AddCommGroup X] {m : ℕ}

theorem sum_smul_toReal_apply' (t : Fin m → ℝ) (u : Fin m → LinearMap.BilinForm ℤ X) (y z : X) :
    (∑ i, t i • toReal (u i)) y z = ∑ i, t i * (u i y z : ℝ) := by
  simp [LinearMap.sum_apply]

theorem toReal_sum_nsmul (n : Fin m → ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) :
    toReal (∑ i, n i • u i) = ∑ i, (n i : ℝ) • toReal (u i) := by
  ext y z
  rw [sum_smul_toReal_apply']
  simp [LinearMap.sum_apply]

theorem sum_smul_toReal_comb {r : ℕ} (v : Fin r → Fin m → ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (c : Fin r → ℝ) :
    ∑ k, c k • toReal (∑ i, v k i • u i) = ∑ i, (∑ k, c k • fun i => (v k i : ℝ)) i • toReal (u i) := by
  ext y z
  rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    toReal_apply, Int.cast_sum, Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

variable {O : Type} [CommRing O] [Module O X]

theorem sum_mem_realForms_iff (bar : O → O) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i y z, u i y z = u i z y)
    (t : Fin m → ℝ) : ∑ i, t i • toReal (u i) ∈ realForms bar X ↔
      ∀ b ∈ {b : Fin m → ℤ | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)},
        ∑ i, (b i : ℝ) * t i = 0 := by
  rw [mem_realForms]
  constructor
  · rintro ⟨-, h⟩ b ⟨a, y, z, rfl⟩
    have := h a y z
    rw [sum_smul_toReal_apply', sum_smul_toReal_apply'] at this
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using this
  · intro h
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
      exact Finset.sum_congr rfl fun i _ => by rw [hu i y z]
    · have := h _ ⟨a, y, z, rfl⟩
      rw [sum_smul_toReal_apply', sum_smul_toReal_apply']
      simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at this
      simpa only [mul_comm] using this

end Contact

theorem exists_isCell_of_contact (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ψ : InvFun O) (K : ℕ) (Λ : (X × X) →₀ ℤ) (m : ℕ)
    (u : Fin m → LinearMap.BilinForm ℤ X) (A : Set (Fin m → ℤ)) (hA : A.Finite) (hK : 0 < K)
    (hsym : ∀ i y z, u i y z = u i z y) (hnn : ∀ i y, 0 ≤ u i y y)
    (hint : ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z)
    (hle : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (K : ℝ) * ψ.evalZ β ≤ evalW Λ (toReal β))
    (hcon : ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧
      (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) ∧ B = ∑ i, t i • toReal (u i))
    (hlin : ∀ t : Fin m → ℝ, (∀ i, 0 ≤ t i) → (∀ v ∈ A, ∑ i, (v i : ℝ) * t i ≤ 0) →
      ∑ i, t i • toReal (u i) ∈ realForms bar X →
      (K : ℝ) * evalR ψ (∑ i, t i • toReal (u i)) = evalW Λ (∑ i, t i • toReal (u i))) :
    ∃ (s : ℕ) (γ : Fin s → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
      ∀ B ∈ psdCone (bar := bar) (X := X), (K : ℝ) * evalR ψ B = evalW Λ B → B ∈ rcone γ := by
  obtain ⟨r, v, hiff, hZ⟩ := _root_.GlobalTheory.MinkWeylReal.cone_orthant_fg m A
    {b | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)} hA
  have hbal := sum_mem_realForms_iff bar u hsym
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hvk : ∀ k, (∀ i, (0 : ℝ) ≤ (v k i : ℝ)) ∧ (∀ a ∈ A, ∑ i, (a i : ℝ) * (v k i : ℝ) ≤ 0) ∧
      (∀ b ∈ {b : Fin m → ℤ | ∃ (a : O) (y z : X), b = fun i => u i (a • y) z - u i y (bar a • z)},
        ∑ i, (b i : ℝ) * (v k i : ℝ) = 0) := by
    intro k
    refine (hiff _).2 ⟨Pi.single k 1, fun j => ?_, ?_⟩
    · by_cases h : j = k
      · subst h; simp
      · simp [h]
    · funext i
      rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
      simp
  have hγR : ∀ k, toReal (∑ i, v k i • u i) = ∑ i, (v k i : ℝ) • toReal (u i) := fun k => toReal_sum_nsmul _ _
  have hγbal : ∀ k, (∑ i, v k i • u i) ∈ balForms bar X := by
    intro k
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hsym i y z]
    · have h := ((hbal _).2 (hvk k).2.2).2 a y z
      rw [← hγR] at h
      simp only [toReal_apply] at h
      exact_mod_cast h
  have hγval : ∀ k, ((linW Λ (∑ i, v k i • u i) : ℤ) : ℝ) = K * ψ.evalZ (∑ i, v k i • u i) := by
    intro k
    have h := hlin _ (hvk k).1 (hvk k).2.1 ((hbal _).2 (hvk k).2.2)
    rw [← hγR, evalR_toReal, evalW_toReal] at h
    exact h.symm
  have hcomb := sum_smul_toReal_comb v u
  refine ⟨r, fun k => ∑ i, v k i • u i, ⟨hγbal, fun k y => ?_, ?_, ?_⟩, ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_nonneg fun i _ => nsmul_nonneg (hnn i y) _
  · rw [linearOn_iff]
    intro c hc
    obtain ⟨hnt, hAt, hVt⟩ := (hiff _).2 ⟨c, hc, rfl⟩
    have h := hlin _ hnt hAt ((hbal _).2 hVt)
    rw [← hcomb, evalW_sum] at h
    have : (K : ℝ) * evalR ψ (∑ k, c k • toReal (∑ i, v k i • u i)) = K * ∑ k, c k * ψ.evalZ (∑ i, v k i • u i) := by
      rw [h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hγval]; ring
    exact mul_left_cancel₀ hKr.ne' this
  · refine ⟨K, linW Λ, hK, hγval, fun β hβ hp => ?_, fun β hβ hp heq => ?_⟩
    · rw [← evalW_toReal]; exact hle β hβ hp
    · have hpsd : toReal β ∈ psdCone (bar := bar) (X := X) := by
        have := GlobalTheory.T.nonneg_sum_smul_intBilinFormToReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
          (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
        simpa using this
      obtain ⟨t, ht0, htA, htB⟩ := hcon _ hpsd (by rw [evalR_toReal, evalW_toReal]; exact heq)
      have hVt := (hbal t).1 (htB ▸ toReal_mem hβ)
      choose z hz using hint β t htB
      have hz0 : ∀ i, 0 ≤ z i := fun i => by
        have := ht0 i; rw [hz i] at this; exact_mod_cast this
      have htn : ∀ i, (((z i).toNat : ℤ) : ℝ) = t i := fun i => by
        rw [Int.toNat_of_nonneg (hz0 i), hz i]
      obtain ⟨k, c, hk, hkc⟩ := hZ (fun i => (z i).toNat)
        (fun a ha => by
          have := htA a ha
          simp only [← htn] at this
          exact_mod_cast this)
        (fun b hb => by
          have := hVt b hb
          simp only [← htn] at this
          exact_mod_cast this)
      refine ⟨k, c, hk, LinearMap.ext₂ fun y w => ?_⟩
      have hβz : β y w = ∑ i, ((z i).toNat : ℤ) * u i y w := by
        have h1 : (β y w : ℝ) = ∑ i, t i * (u i y w : ℝ) := by
          rw [← toReal_apply, htB, sum_smul_toReal_apply']
        have h2 : (β y w : ℝ) = ((∑ i, ((z i).toNat : ℤ) * u i y w : ℤ) : ℝ) := by
          rw [h1]; push_cast
          exact Finset.sum_congr rfl fun i _ => by rw [← htn i]; push_cast; ring
        exact_mod_cast h2
      have hcoord : ∀ i, (k : ℤ) * ((z i).toNat : ℤ) = ∑ j, (c j : ℤ) * (v j i : ℤ) := fun i => by
        have := congrFun hkc i
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at this
        exact_mod_cast this
      calc (k • β) y w = (k : ℤ) * β y w := by simp
        _ = ∑ i, ((k : ℤ) * ((z i).toNat : ℤ)) * u i y w := by
          rw [hβz, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i, ∑ j, (c j : ℤ) * ((v j i : ℤ) * u i y w) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoord, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, (c j : ℤ) * ∑ i, (v j i : ℤ) * u i y w := by
          rw [Finset.sum_comm]; simp only [Finset.mul_sum]
        _ = (∑ j, c j • ∑ i, v j i • u i) y w := by
          simp [LinearMap.sum_apply, nsmul_eq_mul]
  · intro B hB hBe
    obtain ⟨t, ht0, htA, rfl⟩ := hcon B hB hBe
    obtain ⟨c, hc, rfl⟩ := (hiff _).1 ⟨ht0, htA, (hbal _).1 (mem_realForms_of_mem_psdCone hB)⟩
    exact ⟨c, hc, (hcomb c).symm⟩

end GlobalTheory.PolCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCellQuotientByRadicalOfMemCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.CarDim

section Descend

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem exists_pull_mkQ_eq_of_vanish (K : Submodule O X) (f : LinearMap.BilinForm ℤ X)
    (h1 : ∀ x ∈ K, ∀ y, f x y = 0) (h2 : ∀ x, ∀ y ∈ K, f x y = 0) :
    ∃ δ : LinearMap.BilinForm ℤ (X ⧸ K), pull K.mkQ δ = f := by
  let e := Submodule.Quotient.restrictScalarsEquiv ℤ K
  let g := LinearMap.liftQ₂ (K.restrictScalars ℤ) (K.restrictScalars ℤ) f
    (fun x hx => LinearMap.ext fun y => h1 x hx y) (fun y hy => LinearMap.ext fun x => h2 x y hy)
  refine ⟨g.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, LinearMap.ext₂ fun a b => ?_⟩
  simp [pull_apply, e, g]
  rfl

end Descend

theorem exists_cell_quot_orad_of_inRCone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ : InvFun (𝓞 E))
    (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X],
    (∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
      IsCell H.bar ψ γ → IsFaceCut γ s h → IsCell H.bar ψ (fun i => γ (s i))) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
      InRCone γ β → ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ (X ⧸ (orad β : Submodule (𝓞 E) X))),
        IsCell H.bar ψ δ ∧ InRCone (fun i => pull (orad β : Submodule (𝓞 E) X).mkQ (δ i)) β ∧ genRank δ ≤ genRank γ := by
  intro E _ _ _ H ψ X _ _ _ hface β hβ hβp m γ hγ hβγ
  classical
  set K : Submodule (𝓞 E) X := orad β with hK
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (K.restrictScalars ℤ) : (K.restrictScalars ℤ).FG)
  have hTK : ∀ k ∈ T, k ∈ K := fun k hk => by
    have : k ∈ K.restrictScalars ℤ := hT ▸ Submodule.subset_span hk
    exact this
  let hl : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := ∑ k ∈ T, LinearMap.applyₗ k ∘ₗ LinearMap.applyₗ k
  have hl_apply : ∀ β', hl β' = ∑ k ∈ T, β' k k := fun β' => by simp [hl]
  have hsym : ∀ i y z, γ i y z = γ i z y := fun i => (hγ.mem i).1
  have hvan : ∀ i, hl (γ i) = 0 ↔ ∀ x ∈ K, ∀ y, γ i x y = 0 := by
    intro i
    rw [hl_apply]
    constructor
    · intro h0
      have hkk : ∀ k ∈ T, γ i k k = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => hγ.nonneg i k).1 h0
      have hle : K.restrictScalars ℤ ≤ LinearMap.ker (γ i) := by
        rw [← hT, Submodule.span_le]
        intro k hk
        exact LinearMap.ext fun w => ConeSub.eq_zero_of_self_eq_zero (γ i) (hsym i) (hγ.nonneg i) (hkk k hk) w
      intro x hx y
      have := hle hx
      rw [LinearMap.mem_ker] at this
      rw [this]; rfl
    · intro h0
      exact Finset.sum_eq_zero fun k hk => h0 k (hTK k hk) k
  have hnn : ∀ i, 0 ≤ hl (γ i) := fun i => by
    rw [hl_apply]; exact Finset.sum_nonneg fun k _ => hγ.nonneg i k
  set S : Finset (Fin m) := Finset.univ.filter fun i => hl (γ i) = 0 with hS
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Set.range s = ↑S := Finset.range_orderEmbOfFin S rfl
  have hcut : IsFaceCut γ s hl := ⟨hnn, fun j => by
    rw [hs]; simp [hS]⟩
  have hcell := hface m S.card γ s hl hγ hcut
  have hdesc : ∀ i : Fin S.card, ∃ δ : LinearMap.BilinForm ℤ (X ⧸ K), pull K.mkQ δ = γ (s i) := by
    intro i
    have hi : hl (γ (s i)) = 0 := by
      have : s i ∈ (S : Set (Fin m)) := hs ▸ Set.mem_range_self i
      simpa [hS] using this
    have h1 := (hvan (s i)).1 hi
    exact exists_pull_mkQ_eq_of_vanish K _ h1 fun x y hy => by rw [hsym]; exact h1 y hy x
  choose δ hδ using hdesc
  have hδ' : (fun i => pull K.mkQ (δ i)) = fun i => γ (s i) := funext hδ
  have hsurj : Function.Surjective K.mkQ := K.mkQ_surjective
  refine ⟨S.card, δ, ?_, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun i y => ?_, ?_, ?_⟩
    · have hm := hcell.mem i
      rw [← hδ i] at hm
      refine ⟨fun y z => ?_, fun a y z => ?_⟩
      · obtain ⟨y, rfl⟩ := hsurj y
        obtain ⟨z, rfl⟩ := hsurj z
        exact hm.1 y z
      · obtain ⟨y, rfl⟩ := hsurj y
        obtain ⟨z, rfl⟩ := hsurj z
        have := hm.2 a y z
        simpa [pull_apply, map_smul] using this
    · obtain ⟨y, rfl⟩ := hsurj y
      have := hcell.nonneg i y
      rw [← hδ i] at this
      exact this
    · rw [← linearOn_pull_iff hsurj, hδ']
      exact hcell.linear
    · apply IsStrict.of_pull hsurj
      rw [hδ']
      exact hcell.strict
  · rw [hδ']
    obtain ⟨c, hc0, hc⟩ := hβγ
    have hzero : ∀ j, j ∉ S → c j = 0 := by
      intro j hj
      have hj' : hl (γ j) ≠ 0 := by simpa [hS] using hj
      rw [hl_apply] at hj'
      obtain ⟨k, hkT, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj'
      have hk := LinearMap.congr_fun₂ hc k k
      simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hk
      have hb : β k k = 0 := by
        have := (mem_orad.1 (hTK k hkT)) 1 k
        simpa using this
      rw [hb, Int.cast_zero] at hk
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hc0 i) (Int.cast_nonneg (hγ.nonneg i k))).1 hk.symm j (Finset.mem_univ _)
      rcases mul_eq_zero.1 hall with h | h
      · exact h
      · exact absurd (Int.cast_eq_zero.1 h) hk0
    refine ⟨fun i => c (s i), fun i => hc0 _, ?_⟩
    rw [hc]
    exact (Fintype.sum_of_injective s s.injective (fun i => c (s i) • toReal (γ (s i))) (fun j => c j • toReal (γ j))
      (fun j hj => by
        rw [hzero j (by rw [hs] at hj; simpa using hj), zero_smul]) (fun i => rfl)).symm
  · rw [← genRank_pull hsurj δ, hδ']
    unfold genRank
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
    exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range s γ))

end GlobalTheory.PolFan.CarDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystemsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteTypes_via_full_heckeAlgebra_eigensystems : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Lam3 Z := by
  first | exact @GlobalTheory.Mem.R3.finiteTypes_of_full_heckeAlgebra_eigensystems | exact GlobalTheory.Mem.R3.finiteTypes_of_full_heckeAlgebra_eigensystems | (intros; apply GlobalTheory.Mem.R3.finiteTypes_of_full_heckeAlgebra_eigensystems <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricGStatement
section
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDeriv_chernConnection_inverseSymmetricGram : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E), GlobalTheory.HermFrame.MContDiffAt 2 H z → IsUnit (H z).det → (∀ᶠ x in 𝓝 z, (H x).IsSymm) → ∀ ξ η, GlobalTheory.HermFrame.mdel (fun x => GlobalTheory.HermFrame.conn (fun y => (H y)⁻¹) x η) z ξ - GlobalTheory.HermFrame.mdel (fun x => GlobalTheory.HermFrame.conn (fun y => (H y)⁻¹) x ξ) z η = -(GlobalTheory.HermFrame.conn H z η * GlobalTheory.HermFrame.conn H z ξ - GlobalTheory.HermFrame.conn H z ξ * GlobalTheory.HermFrame.conn H z η)ᵀ := by
  first | exact @GlobalTheory.HermFrame.mdel_conn_inv_sub | exact GlobalTheory.HermFrame.mdel_conn_inv_sub | (intros; apply GlobalTheory.HermFrame.mdel_conn_inv_sub <;> assumption)
end

