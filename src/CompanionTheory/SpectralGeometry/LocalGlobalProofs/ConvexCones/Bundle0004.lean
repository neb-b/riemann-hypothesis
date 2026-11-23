module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierDimInvFunHostFixingAutInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.BalancedNonnegFormInPsdConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balanced_nonneg_form_in_psd_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (β : LinearMap.BilinForm ℤ X), β ∈ balForms bar X → (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := bar) (X := X) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg | exact GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.PsdConeMembership.toReal_mem_psdCone_of_nonneg <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierFunctionTwistedGalois
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction

theorem twEval_of_isTwG {O : Type} [CommRing O] {w0 : O} {ψ : InvFun O}
    (htw : IsTwG w0 ψ) {σ : O ≃+* O} (hσ : σ w0 = w0) : Tw.TwEval σ ψ := by
  intro Y Y' _ _ _ _ _ _ τ hτ B
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin' O Y
  have hsy : ∀ (a : O) (y : Y), τ.symm (σ a • y) = a • τ.symm y := fun a y => by
    apply τ.injective
    rw [hτ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let s' : (Fin n → O) →ₗ[O] Y' :=
    { toFun := fun x => τ.symm (s fun i => σ (x i))
      map_add' := fun x x' => by
        have : (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + fun i => σ (x' i) := by ext i; simp
        rw [this, map_add (f := _), map_add (f := _)]
      map_smul' := fun c x => by
        have : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i) := by ext i; simp
        rw [this, map_smul, hsy]
        rfl }
  have hs' : Function.Surjective s' := fun y => by
    obtain ⟨x, hx⟩ := hs (τ y)
    refine ⟨fun i => σ.symm (x i), ?_⟩
    show τ.symm (s fun i => σ (σ.symm (x i))) = y
    simp only [RingEquiv.apply_symm_apply]
    rw [hx, AddEquiv.symm_apply_apply]
  rw [ψ.eval_eq hs', ψ.eval_eq hs]
  have := htw σ hσ n fun a b => B (s a) (s b)
  simpa [s'] using this

theorem isTwG_carFun : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (w0 : O), CMOrd O bar → ∀ (ψ : InvFun O), IsTwG w0 ψ → IsTwG w0 (carFun bar ψ) := by
  intro O _ _ _ _ bar w0 hb ψ htw σ hσ n B
  have hc : ∀ a, σ (bar a) = bar (σ a) := hb.comm σ
  have hev : Tw.TwEval σ ψ := twEval_of_isTwG htw hσ
  let τ : (Fin n → O) ≃+ (Fin n → O) := AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  have hτ : ∀ (a : O) (y : Fin n → O), τ (a • y) = σ a • τ y := fun a y => by ext i; simp [τ]
  have hτs := Tw.symm_smul hτ
  have hcs := Tw.symm_comm hc
  show (carFun bar ψ).toFun n (fun a b => B (τ a) (τ b)) = (carFun bar ψ).toFun n B
  dsimp only [carFun]
  by_cases h : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
      ∀ a b, B a b = β a b
  · have h' : ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b :=
      ⟨Tw.pullA τ h.choose, Tw.pullA_mem hc hτ h.choose_spec.1, fun y => h.choose_spec.2.1 _,
        fun a b => h.choose_spec.2.2 _ _⟩
    rw [dite_eq_left h, dite_eq_left h']
    have e : h'.choose = Tw.pullA τ h.choose := LinearMap.ext₂ fun a b => by
      have h1 := h'.choose_spec.2.2 a b
      have h2 := h.choose_spec.2.2 (τ a) (τ b)
      rw [Tw.pullA_apply]
      exact_mod_cast h1.symm.trans h2
    rw [e]
    unfold cdimQ
    congr 2
    refine (Set.Subset.antisymm ?_ (Tw.cdimSet_subset hc hev hτ _))
    have := Tw.cdimSet_subset (bar := bar) (ψ := ψ) hcs hev.symm hτs (Tw.pullA τ h.choose)
    rwa [Tw.pullA_symm_pullA] at this
  · have h' : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → O), β ∈ balForms bar (Fin n → O) ∧ (∀ y, 0 ≤ β y y) ∧
        ∀ a b, B (τ a) (τ b) = β a b := by
      rintro ⟨β, h1, h2, h3⟩
      refine h ⟨Tw.pullA τ.symm β, Tw.pullA_mem hcs hτs h1, fun y => h2 _, fun a b => ?_⟩
      rw [Tw.pullA_apply, ← h3, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.CompanionTheory.Ar.Fan.TwistedCarrierFunction
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceOfFaceCut
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.CellFaces

variable {O : Type} [CommRing O] {bar : O → O} {ψ : InvFun O}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]


omit [Module O X] [Module.Finite O X] in
theorem apply_eq_sum_of_toReal {m : ℕ} {β : LinearMap.BilinForm ℤ X} {u : Fin m → LinearMap.BilinForm ℤ X}
    {c : Fin m → ℝ} (hβ : toReal β = ∑ i, c i • toReal (u i)) (F : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) :
    (F β : ℝ) = ∑ i, c i * (F (u i) : ℝ) := by
  have hpt : ∀ a b : X, ((β a b : ℤ) : ℝ) = ∑ i, c i * ((u i a b : ℤ) : ℝ) := by
    intro a b
    have := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B a b) hβ
    simpa [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply] using this
  have hπ : ∀ (π : ℝ →ₗ[ℚ] ℚ) (x : ℝ) (n : ℤ), π (x * (n : ℝ)) = π x * (n : ℚ) := by
    intro π x n
    rw [mul_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]
  have hrat : ∀ π : ℝ →ₗ[ℚ] ℚ, π 1 * (F β : ℚ) = ∑ i, π (c i) * (F (u i) : ℚ) := by
    intro π
    have hq : ∀ a b : X, π 1 * ((β a b : ℤ) : ℚ) = ∑ i, π (c i) * ((u i a b : ℤ) : ℚ) := by
      intro a b
      have h1 := congrArg π (hpt a b)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← one_mul ((β a b : ℤ) : ℝ), hπ, map_sum] at h1
      simpa only [hπ] using h1
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
      (Finset.univ : Finset (Option (Fin m))) (fun o : Option (Fin m) => o.elim (π 1) (fun i => π (c i)))
    choose z hz using fun o => hb o (Finset.mem_univ o)
    have hz' : ∀ o, ((z o : ℤ) : ℚ) = ((b : ℤ) : ℚ) * o.elim (π 1) (fun i => π (c i)) := by
      intro o
      simpa [zsmul_eq_mul] using hz o
    have hint : z none • β = ∑ i, z (some i) • u i := by
      ext x y
      apply Int.cast_injective (α := ℚ)
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, Int.cast_mul, Int.cast_sum, hz',
        Option.elim_none, Option.elim_some]
      rw [mul_assoc, hq x y, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h2 := congrArg (fun β => ((F β : ℤ) : ℚ)) hint
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_zsmul, map_sum, smul_eq_mul, Int.cast_mul, Int.cast_sum, hz', Option.elim_none,
      Option.elim_some] at h2
    have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero b.2
    apply mul_left_cancel₀ hb0
    rw [Finset.mul_sum, ← mul_assoc, h2]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hr : ∑ i, c i * (F (u i) : ℝ) - (F β : ℝ) = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff ℚ _).mp fun π => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, ← one_mul ((F β : ℤ) : ℝ), hπ]
    simp only [hπ]
    rw [← hrat π]
    ring
  linarith

theorem est_at {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hstr : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i)
    (hle : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * ψ.evalZ β ≤ ℓ β)
    (hγ : ∀ j, 0 ≤ h (γ j)) {C : ℕ} (hC : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β)
    {u : LinearMap.BilinForm ℤ X} (hu : u ∈ balForms bar X) (hp : ∀ y, 0 ≤ u y y) (n : ℤ) (hn : ψ.evalZ u = n)
    {B0 L : ℝ} (hb : N * ψ.evalZ u ≤ B0) (hB0 : 0 ≤ B0) (hL : C * (B0 + 1) + C ≤ L) :
    L * (N * ψ.evalZ u) ≤ L * ℓ u + h u := by
  have hle' := hle u hu hp
  have hhC := hC u hu hp
  rw [hn] at hle' hb ⊢
  have hleZ : (N : ℤ) * n ≤ ℓ u := by exact_mod_cast hle'
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  rcases hleZ.lt_or_eq with hlt | heq
  · have h1 : ((N : ℤ) * n + 1 : ℤ) ≤ ℓ u := hlt
    have h1R : (N : ℝ) * n + 1 ≤ (ℓ u : ℝ) := by exact_mod_cast h1
    have hLC : (C : ℝ) * (B0 + 1) ≤ L - C := by linarith
    have hLC0 : (0 : ℝ) ≤ L - C := le_trans (mul_nonneg hC0 (by linarith)) hLC
    have k1 : (L - C) * 1 ≤ (L - C) * ((ℓ u : ℝ) - N * n) :=
      mul_le_mul_of_nonneg_left (by linarith) hLC0
    have k2 : (C : ℝ) * (N * n) ≤ C * B0 := mul_le_mul_of_nonneg_left hb hC0
    nlinarith [k1, k2, hhC, hLC]
  · have heqR : (N : ℝ) * ψ.evalZ u = ℓ u := by rw [hn]; exact_mod_cast heq
    obtain ⟨k, c, hk, hkc⟩ := hstr u hu hp heqR
    have hsum : (k : ℤ) * h u = ∑ i, (c i : ℤ) * h (γ i) := by
      have := congrArg h hkc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_nsmul, map_sum, nsmul_eq_mul] using this
    have hnn : 0 ≤ ∑ i, (c i : ℤ) * h (γ i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hγ i)
    have hhu : 0 ≤ h u := by
      by_contra hneg
      have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) (not_le.mp hneg)
      linarith
    have hhuR : (0 : ℝ) ≤ h u := by exact_mod_cast hhu
    have hℓR : ((ℓ u : ℤ) : ℝ) = (N : ℝ) * n := by exact_mod_cast heq.symm
    rw [hℓR]
    linarith

theorem isCell_comp : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (ψ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar ψ X → Dominates bar X → ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ → IsFaceCut γ s h → IsCell bar ψ (fun i => γ (s i)) := by
  intro O _ _ _ _ bar _ ψ X _ _ _ hfan hdom m m' γ s h hcell hface
  obtain ⟨hmem, hnn, hlin, hstrict⟩ := hcell
  obtain ⟨N, ℓ, hN, hℓγ, hle, hstr⟩ := hstrict
  obtain ⟨hh0, hhz⟩ := hface
  have reidx : ∀ (c' : Fin m' → ℝ) (f : Fin m → ℝ),
      ∑ j, Function.extend s c' 0 j * f j = ∑ i, c' i * f (s i) := by
    intro c' f
    refine ((Finset.sum_subset (Finset.subset_univ (Finset.univ.map s)) fun j _ hj => ?_).symm.trans
      (Finset.sum_map Finset.univ s (fun j => Function.extend s c' 0 j * f j))).trans ?_
    · rw [Function.extend_apply' _ _ _ (by simpa using hj), Pi.zero_apply, zero_mul]
    · exact Finset.sum_congr rfl fun i _ => by rw [s.injective.extend_apply]
  have hext_nn : ∀ c' : Fin m' → ℝ, (∀ i, 0 ≤ c' i) → ∀ j, 0 ≤ Function.extend s c' 0 j := by
    intro c' hc' j
    by_cases hj : ∃ i, s i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [s.injective.extend_apply]
      exact hc' i
    · rw [Function.extend_apply' _ _ _ hj]
      exact le_refl _
  have hlin' : ψ.LinearOn (fun i => γ (s i)) := by
    intro c' hc'
    have hl := hlin (Function.extend s c' 0) (hext_nn c' hc')
    show ψ.eval X (fun a b => ∑ i, c' i * ((γ (s i) a b : ℤ) : ℝ)) = ∑ i, c' i * ψ.evalZ (γ (s i))
    have e1 : (fun a b => ∑ i, c' i * ((γ (s i) a b : ℤ) : ℝ)) =
        (fun a b => ∑ j, Function.extend s c' 0 j * ((γ j a b : ℤ) : ℝ)) := by
      funext a b
      rw [reidx c' (fun j => ((γ j a b : ℤ) : ℝ))]
    rw [e1, hl, reidx c' (fun j => ψ.evalZ (γ j))]
  have hpos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := by
    intro β hβ hp hne
    have h1 := hle β hβ hp
    have h2 := hfan.pos β hβ hp hne
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos hNR h2) h1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hdom ℓ (-h) hpos
  have hCR : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → -(h β : ℝ) ≤ C * ℓ β := by
    intro β hβ hp
    have := hC β hβ hp
    rw [LinearMap.neg_apply] at this
    exact_mod_cast this
  obtain ⟨S, hSfin, hcov⟩ := hfan.finite
  set B0 : ℝ := ∑ x ∈ hSfin.toFinset, |(N : ℝ) * ψ.evalZ x| with hB0def
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0ge : ∀ x ∈ S, (N : ℝ) * ψ.evalZ x ≤ B0 := fun x hx =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |(N : ℝ) * ψ.evalZ x|)
      (fun _ _ => abs_nonneg _) (hSfin.mem_toFinset.mpr hx))
  have key : ∀ L : ℝ, (C : ℝ) * (B0 + 1) + C ≤ L → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      L * (N * ψ.evalZ β) ≤ L * ℓ β + h β := by
    intro L hL β hβ hp
    have hB : toReal β ∈ psdCone (bar := bar) (X := X) := by
      have := GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 (fun _ => β) (fun _ => 1)
        (fun _ => hβ) (fun _ => hp) (fun _ => zero_le_one)
      simpa using this
    obtain ⟨e, k, γ', c, hcell', hS', hc', heq⟩ := hcov _ hB
    have hsurj : Function.Surjective (e.symm : X →ₗ[O] X) := fun x => ⟨e x, by simp⟩
    have hcellu : IsCell bar ψ (fun i => pull (e.symm : X →ₗ[O] X) (γ' i)) := isCell_pull_equiv hcell' e.symm
    have hpt : ∀ a b : X, ((β a b : ℤ) : ℝ) = ∑ i, c i * ((pull (e.symm : X →ₗ[O] X) (γ' i) a b : ℤ) : ℝ) := by
      intro a b
      have := congrArg (fun B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ => B (e.symm a) (e.symm b)) heq
      simpa [pullR, pull_apply, toReal_apply, LinearMap.sum_apply] using this
    have hrel : toReal β = ∑ i, c i • toReal (pull (e.symm : X →ₗ[O] X) (γ' i)) := by
      ext a b
      simpa [toReal_apply, LinearMap.sum_apply] using hpt a b
    have hℓ := apply_eq_sum_of_toReal hrel ℓ
    have hh := apply_eq_sum_of_toReal hrel h
    have hφ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)) := by
      rw [← hcellu.linear c hc']
      show ψ.eval X (fun a b => ((β a b : ℤ) : ℝ)) = _
      congr 1
      funext a b
      exact hpt a b
    have hest : ∀ i, L * (N * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i))) ≤
        L * ℓ (pull (e.symm : X →ₗ[O] X) (γ' i)) + h (pull (e.symm : X →ₗ[O] X) (γ' i)) := by
      intro i
      obtain ⟨n, hn⟩ := hfan.integral _ (hcellu.mem i) (hcellu.nonneg i)
      have hbi : (N : ℝ) * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)) ≤ B0 := by
        rw [evalZ_pull ψ hsurj]
        exact hB0ge _ (hS' i)
      exact est_at (bar := bar) hstr hle hh0 hCR (hcellu.mem i) (hcellu.nonneg i) n hn hbi hB0 hL
    calc L * (N * ψ.evalZ β)
        = ∑ i, c i * (L * (N * ψ.evalZ (pull (e.symm : X →ₗ[O] X) (γ' i)))) := by
          rw [hφ, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, c i * (L * ℓ (pull (e.symm : X →ₗ[O] X) (γ' i)) + h (pull (e.symm : X →ₗ[O] X) (γ' i))) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hest i) (hc' i)
      _ = L * ℓ β + h β := by
          rw [hℓ, hh, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hL0 := Nat.le_ceil ((C : ℝ) * (B0 + 1) + C)
  set L0 : ℕ := ⌈(C : ℝ) * (B0 + 1) + C⌉₊ with hL0def
  have reidxN : ∀ c : Fin m → ℕ, (∀ j, j ∉ Set.range s → c j = 0) →
      ∑ j, c j • γ j = ∑ i, c (s i) • γ (s i) := by
    intro c hc
    exact (Finset.sum_subset (Finset.subset_univ (Finset.univ.map s)) fun j _ hj => by
      rw [hc j (by simpa using hj), zero_smul]).symm.trans (Finset.sum_map Finset.univ s (fun j => c j • γ j))
  refine ⟨fun i => hmem (s i), fun i => hnn (s i), hlin', ?_⟩
  unfold GlobalTheory.PolFan.IsStrict
  refine ⟨(L0 + 1) * N, ((L0 + 1 : ℕ) : ℤ) • ℓ + h, Nat.mul_pos (Nat.succ_pos _) hN, ?_, ?_, ?_⟩
  · intro i
    have hz : h (γ (s i)) = 0 := (hhz (s i)).mpr ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hz, add_zero, smul_eq_mul]
    push_cast
    rw [hℓγ (s i)]
    ring
  · intro β hβ hp
    have hA := key ((L0 + 1 : ℕ) : ℝ) (by push_cast; linarith) β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    push_cast at hA ⊢
    nlinarith [hA]
  · intro β hβ hp heqβ
    have hA := key ((L0 + 1 : ℕ) : ℝ) (by push_cast; linarith) β hβ hp
    have hB := key (L0 : ℝ) hL0 β hβ hp
    have hle' := hle β hβ hp
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at heqβ
    push_cast at heqβ hA
    have hd : (N : ℝ) * ψ.evalZ β = ℓ β := by nlinarith [hB, heqβ, hle']
    have hh0β : (h β : ℝ) = 0 := by nlinarith [hB, heqβ, hd]
    obtain ⟨k, c, hk, hkc⟩ := hstr β hβ hp hd
    have hsum : (k : ℤ) * h β = ∑ j, (c j : ℤ) * h (γ j) := by
      have := congrArg h hkc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_nsmul, map_sum, nsmul_eq_mul] using this
    have hhβ : h β = 0 := by exact_mod_cast hh0β
    rw [hhβ, mul_zero] at hsum
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (Int.natCast_nonneg (c j)) (hh0 j))).mp hsum.symm
    have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := by
      intro j hj
      have h2 : h (γ j) ≠ 0 := fun h0 => hj ((hhz j).mp h0)
      rcases mul_eq_zero.mp (hterm j (Finset.mem_univ j)) with h3 | h3
      · exact_mod_cast h3
      · exact absurd h3 h2
    exact ⟨k, fun i => c (s i), hk, hkc.trans (reidxN c hc0)⟩

end GlobalTheory.CompanionTheory.Ar.Fan.CellFaces
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CellFaceRestriction
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.FaceCells

theorem isCell_face_of_isFaceCut : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ : InvFun O), IsPolyFan bar q ψ → ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → Dominates bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ v → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell bar ψ (fun j => v (s j)) := by
  intro O _ _ _ _ bar _ q ψ hψ X _ _ _ _ hX hD m v hv m' s h hcut
  have hP := hψ X hX
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hv.strict
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓpos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos hNr e2) e1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hD ℓ (-h) hℓpos
  obtain ⟨S, hS, hcov⟩ := hP.finite
  obtain ⟨b, hb⟩ : ∃ b : ℕ, ∀ γ ∈ S, ψ.evalZ γ ≤ b := by
    refine ⟨⌈∑ γ ∈ hS.toFinset, |ψ.evalZ γ|⌉₊, fun γ hγ => ?_⟩
    refine le_trans ?_ (Nat.le_ceil _)
    exact le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun γ => |ψ.evalZ γ|) (fun _ _ => abs_nonneg _) (hS.mem_toFinset.2 hγ))
  set K : ℕ := C * (1 + N * b) + 1 with hK
  have hKpos : 0 < K := Nat.succ_pos _

  have gen : ∀ u ∈ balForms bar X, (∀ y, 0 ≤ u y y) → ψ.evalZ u ≤ b →
      (0 ≤ h u ∧ (ℓ u : ℝ) = N * ψ.evalZ u) ∨
        (0 : ℝ) < K * (ℓ u : ℝ) + h u - K * N * ψ.evalZ u := by
    intro u hu hp hub
    by_cases heq : (ℓ u : ℝ) = N * ψ.evalZ u
    · left
      obtain ⟨k, c, hk, hc⟩ := h3 u hu hp heq.symm
      have e1 : (k : ℤ) * h u = ∑ i, (c i : ℤ) * h (v i) := by
        have := congrArg h hc
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
      have hnn : 0 ≤ (k : ℤ) * h u := e1 ▸ Finset.sum_nonneg fun i _ => mul_nonneg (Int.natCast_nonneg _) (hcut.1 i)
      exact ⟨(mul_nonneg_iff_of_pos_left (by exact_mod_cast hk)).1 hnn, heq⟩
    · right
      obtain ⟨n, hn⟩ := hP.integral u hu hp
      have hle : (N : ℝ) * ψ.evalZ u ≤ ℓ u := h2 u hu hp
      have hlt : (N : ℝ) * ψ.evalZ u < ℓ u := lt_of_le_of_ne hle (Ne.symm heq)
      rw [hn] at hlt hub ⊢
      have hint : (N : ℤ) * n + 1 ≤ ℓ u := by
        have : (((N : ℤ) * n : ℤ) : ℝ) < ℓ u := by push_cast; exact hlt
        exact_mod_cast this
      have hint' : (N : ℝ) * n + 1 ≤ ℓ u := by exact_mod_cast hint
      have hCu : -h u ≤ C * ℓ u := by simpa using hC u hu hp
      have hCu' : -(h u : ℝ) ≤ C * ℓ u := by exact_mod_cast hCu
      have hKr : (K : ℝ) = C * (1 + N * b) + 1 := by rw [hK]; push_cast; ring
      have hCN : (0 : ℝ) ≤ C * N := by positivity
      have a1 : (K - C : ℝ) * 1 ≤ (K - C) * (ℓ u - N * n) :=
        mul_le_mul_of_nonneg_left (by linarith) (by rw [hKr]; have : (0 : ℝ) ≤ C * N * b := by positivity
                                                    nlinarith)
      have a2 : (C * N : ℝ) * n ≤ C * N * b := mul_le_mul_of_nonneg_left hub hCN
      rw [hKr] at a1 ⊢
      nlinarith

  have core : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      ((K * N : ℕ) : ℝ) * ψ.evalZ β ≤ ((K • ℓ + h) β : ℤ) ∧
        (((K * N : ℕ) : ℝ) * ψ.evalZ β = ((K • ℓ + h) β : ℤ) → h β = 0) := by
    intro β hβ hp
    have hR : toReal β ∈ psdCone (bar := bar) (X := X) := by
      simpa using GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (by simp [hβ])
        (by simp [hp]) (by simp)
    obtain ⟨e, mm, γ, c, hγ, hγS, hc, hsum⟩ := hcov (toReal β) hR
    set u : Fin mm → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (γ i) with hu
    have hβu : toReal β = ∑ i, c i • toReal (u i) := LinearMap.ext₂ fun a b => by
      have := LinearMap.congr_fun₂ hsum (e.symm a) (e.symm b)
      simpa [LinearMap.sum_apply, u] using this
    have hlin : ψ.LinearOn u := (linearOn_pull_iff e.symm.surjective).2 hγ.linear
    have hψβ : ψ.evalZ β = ∑ i, c i * ψ.evalZ (u i) := by
      rw [← evalR_toReal, hβu, (linearOn_iff ψ u).1 hlin c hc]
    have hℓβ := apply_eq_of_toReal_eq hβu ℓ
    have hhβ := apply_eq_of_toReal_eq hβu h
    have hT : (((K • ℓ + h) β : ℤ) : ℝ) - ((K * N : ℕ) : ℝ) * ψ.evalZ β =
        ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, Int.cast_add, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul]
      rw [hℓβ, hhβ, hψβ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hg : ∀ i, (0 ≤ h (u i) ∧ (ℓ (u i) : ℝ) = N * ψ.evalZ (u i)) ∨
        (0 : ℝ) < K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i) := fun i =>
      gen (u i) (pull_mem _ (hγ.mem i)) (fun y => hγ.nonneg i _)
        (by rw [hu, evalZ_pull ψ e.symm.surjective]; exact hb _ (hγS i))
    have hterm : ∀ i, 0 ≤ c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) := fun i => by
      refine mul_nonneg (hc i) ?_
      rcases hg i with ⟨h0, he⟩ | hpos
      · rw [he]
        have : (0 : ℝ) ≤ h (u i) := by exact_mod_cast h0
        nlinarith
      · exact hpos.le
    refine ⟨?_, fun heq => ?_⟩
    · have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hterm i
      linarith
    · have h0 : ∑ i, c i * (K * (ℓ (u i) : ℝ) + h (u i) - K * N * ψ.evalZ (u i)) = 0 := by
        rw [← hT, heq, sub_self]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hterm i).1 h0
      have : (h β : ℝ) = 0 := by
        rw [hhβ]
        refine Finset.sum_eq_zero fun i hi => ?_
        rcases eq_or_ne (c i) 0 with hci | hci
        · rw [hci, zero_mul]
        · have hTi := (mul_eq_zero.1 (hz i hi)).resolve_left hci
          rcases hg i with ⟨-, he⟩ | hpos
          · rw [he] at hTi
            have : (h (u i) : ℝ) = 0 := by linarith
            rw [this, mul_zero]
          · exact absurd hTi hpos.ne'
      exact_mod_cast this
  refine ⟨fun j => hv.mem _, fun j => hv.nonneg _, linearOn_comp hv.linear s, K * N, K • ℓ + h,
    Nat.mul_pos hKpos hN, fun i => ?_, fun β hβ hp => (core β hβ hp).1, fun β hβ hp heq => ?_⟩
  · have hz : h (v (s i)) = 0 := (hcut.2 _).2 ⟨i, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hz, add_zero, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul]
    rw [h1]; ring
  · have hh := (core β hβ hp).2 heq
    have hℓ : (N : ℝ) * ψ.evalZ β = ℓ β := by
      have e1 := heq
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, hh, add_zero, Int.cast_mul,
        Int.cast_natCast, Nat.cast_mul] at e1
      have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
      have : (K : ℝ) * (N * ψ.evalZ β - ℓ β) = 0 := by linarith
      linarith [(mul_eq_zero.1 this).resolve_left hKr.ne']
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp hℓ
    have e1 : (k : ℤ) * h β = ∑ j, (c j : ℤ) * h (v j) := by
      have := congrArg h hc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    rw [hh, mul_zero] at e1
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      mul_nonneg (Int.natCast_nonneg (c j)) (hcut.1 j)).1 e1.symm
    have hc0 : ∀ j, j ∉ Set.range s → c j = 0 := fun j hj => by
      have hne : h (v j) ≠ 0 := fun h0 => hj ((hcut.2 j).1 h0)
      have := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_right hne
      exact_mod_cast this
    refine ⟨k, fun i => c (s i), hk, ?_⟩
    rw [hc]
    classical
    rw [← Finset.sum_map Finset.univ s (fun j => c j • v j)]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    rw [hc0 j fun ⟨i, hi⟩ => hj (by simp [← hi]), zero_smul]

end GlobalTheory.CompanionTheory.Ar.Fan.FaceCells
end
end

