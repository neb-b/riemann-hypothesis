module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeStrictnessGapOffCentres
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarGap

theorem gap_eq_sum {O : Type} [CommRing O] {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hlin : φ.LinearOn γ) {β : LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (hsum : toReal β = ∑ i, c i • toReal (γ i)) :
    (ℓ β : ℝ) - N * φ.evalZ β = ∑ i, c i * ((ℓ (γ i) : ℝ) - N * φ.evalZ (γ i)) := by
  have h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  have h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff φ γ).1 hlin c hc
  have h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by simp at h2; linarith
  rw [h4, h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem starDepth_le_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (starDepth H.bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  intro E _ _ _ H q ψ w hψ _ X _ _ _ _ hX m γ N ℓ _ hno _ hsw β hβ hp
  have hfan := hψ X hX
  obtain ⟨-, hge, heq⟩ := hsw

  have hmem : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m', δ₀, c, hδ₀, -, hc, he⟩ := hS _ hmem
  set δ : Fin m' → LinearMap.BilinForm ℤ X := fun i => pull e.symm.toLinearMap (δ₀ i) with hδdef
  have hδ : IsCell H.bar ψ δ := CarDim.isCell_pull_equiv hδ₀ e.symm
  have hβc : toReal β = ∑ i, c i • toReal (δ i) := LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [hδdef, LinearMap.sum_apply] using this
  rw [← evalR_toReal]
  refine evalR_starDepth_le _ H.bar ψ w X m' δ (toReal β) _ hδ ⟨c, hc, hβc⟩ (sub_nonneg.2 (hge β hβ hp)) ?_
  rintro v hv hvp hwv ⟨b, hb, hvb⟩ t ht ⟨d, hd, hdt⟩

  have hv1 : (1 : ℝ) ≤ (ℓ v : ℝ) - N * ψ.evalZ v := by
    obtain ⟨n, hn⟩ := hfan.integral v hv hvp
    have h0 := hge v hv hvp
    have hne : (N : ℝ) * ψ.evalZ v ≠ ℓ v := fun h => by
      obtain ⟨k, a, hk, hka⟩ := heq v hv hvp h
      obtain ⟨g, hg, hgs⟩ := StarUpper.sum_mem_rcone (δ := ![v]) (γ := γ) ![1] (fun i => by fin_cases i; norm_num)
        (fun i _ => by fin_cases i; exact ⟨k, a, hk, hka⟩)
      have := hno v hv hvp ⟨g, hg, by simpa using hgs⟩
      rw [hwv] at this
      exact one_ne_zero this
    have hlt := lt_of_le_of_ne h0 hne
    rw [hn] at hlt ⊢
    have h1 : (N : ℤ) * n < ℓ v := by exact_mod_cast hlt
    have h2 : (1 : ℤ) ≤ ℓ v - N * n := by omega
    exact_mod_cast h2
  have hβ' : toReal β = ∑ i, (t * b i + d i) • toReal (δ i) := by
    have : toReal β = t • toReal v + (toReal β - t • toReal v) := by abel
    rw [this, hdt, hvb, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [add_smul, smul_smul]
  have e1 := gap_eq_sum N ℓ hδ.linear (fun i => add_nonneg (mul_nonneg ht.le (hb i)) (hd i)) hβ'
  have e2 := gap_eq_sum N ℓ hδ.linear hb hvb
  have e3 : 0 ≤ ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sub_nonneg.2 (hge _ (hδ.mem i) (hδ.nonneg i)))
  have e4 : (ℓ β : ℝ) - N * ψ.evalZ β = t * ((ℓ v : ℝ) - N * ψ.evalZ v) +
      ∑ i, d i * ((ℓ (δ i) : ℝ) - N * ψ.evalZ (δ i)) := by
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e4]
  nlinarith [mul_le_mul_of_nonneg_left hv1 ht.le]

end GlobalTheory.PolFan.StarGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarLabEvalZOfEqOne
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.StarLab

variable {O : Type} [CommRing O]

def IsCentreRay (w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∃ β : LinearMap.BilinForm ℤ X, w.evalZ β = 1 ∧ ∀ a b, t * B a b = β a b

theorem isCentreRay_comp (w : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] [Module.Projective O X₁] {r : X →ₗ[O] X₁}
    (hr : Function.Surjective r) (B : X₁ → X₁ → ℝ) :
    IsCentreRay w X (fun a b => B (r a) (r b)) ↔ IsCentreRay w X₁ B := by
  constructor
  · rintro ⟨t, ht, β, hw, hβ⟩
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hs' : ∀ x, r (s x) = x := fun x => LinearMap.congr_fun hs x
    refine ⟨t, ht, pull s β, ?_, fun x y => ?_⟩
    · have e : pull r (pull s β) = β := LinearMap.ext₂ fun a b => by
        have h1 := hβ (s (r a)) (s (r b))
        have h2 := hβ a b
        simp only [hs'] at h1
        simp only [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [← evalZ_pull w hr, e, hw]
    · have := hβ (s x) (s y)
      simp only [hs'] at this
      simpa only [pull_apply] using this
  · rintro ⟨t, ht, β, hw, hβ⟩
    exact ⟨t, ht, pull r β, by rw [evalZ_pull w hr, hw], fun a b => by simp only [pull_apply, hβ]⟩


open Classical in
def starLab (lab w : InvFun O) : InvFun O where
  toFun n B := if IsCentreRay w (Fin n → O) B then -1 else Real.exp (lab.toFun n B) - 1
  inv n m r hr B := by
    simp only [isCentreRay_comp w hr B, lab.inv n m r hr B]
  zero B := by
    have : ¬ IsCentreRay w (Fin 0 → O) B := by
      rintro ⟨t, -, β, hw, -⟩
      rw [InvFun.evalZ, w.eval_of_subsingleton] at hw
      norm_num at hw
    rw [if_neg this, lab.zero, Real.exp_zero, sub_self]


open Classical in
theorem starLab_eval (lab w : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (B : X → X → ℝ) :
    (starLab lab w).eval X B = if IsCentreRay w X B then -1 else Real.exp (lab.eval X B) - 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(starLab lab w).eval_eq hr, lab.eval_eq hr]
  simp only [starLab, isCentreRay_comp w hr B]

variable {X : Type} [AddCommGroup X]


open Classical in
theorem starLab_evalZ_of_eq_one (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : w.evalZ β = 1) : (starLab lab w).evalZ β = -1 := by
  rw [InvFun.evalZ, starLab_eval, if_pos ⟨1, one_pos, β, h, fun a b => one_mul _⟩]

theorem starLab_evalZ_of_not (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : ¬ IsCentreRay w X (fun a b => (β a b : ℝ))) :
    (starLab lab w).evalZ β = Real.exp (lab.evalZ β) - 1 := by
  rw [InvFun.evalZ, starLab_eval, if_neg h]; rfl

theorem isCentreRay_smul_iff (w : InvFun O) [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) {k : ℕ}
    (hk : 0 < k) :
    IsCentreRay w X (fun a b => ((((k : ℤ) • β) a b : ℤ) : ℝ)) ↔ IsCentreRay w X (fun a b => (β a b : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t * k, mul_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; ring
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t / k, div_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; field_simp

theorem starLab_evalZ_smul (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X) {k : ℕ} (hk : 0 < k) (hlab : lab.evalZ ((k : ℤ) • β) = lab.evalZ β) :
    (starLab lab w).evalZ ((k : ℤ) • β) = (starLab lab w).evalZ β := by
  unfold InvFun.evalZ at hlab ⊢
  rw [starLab_eval, starLab_eval, hlab]
  by_cases hc : IsCentreRay w X (fun a b => (β a b : ℝ))
  · rw [if_pos ((isCentreRay_smul_iff w β hk).2 hc), if_pos hc]
  · rw [if_neg (mt (isCentreRay_smul_iff w β hk).1 hc), if_neg hc]

theorem exists_of_isCentreRay {bar : O → O} (w : InvFun O) [Module O X] [Module.Finite O X]
    {β : LinearMap.BilinForm ℤ X} (hb : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y)
    (h : IsCentreRay w X (fun a b => (β a b : ℝ))) :
    ∃ t : ℝ, 0 < t ∧ ∃ β' : LinearMap.BilinForm ℤ X, β' ∈ balForms bar X ∧ (∀ y, 0 ≤ β' y y) ∧ w.evalZ β' = 1 ∧
      toReal β' = t • toReal β := by
  obtain ⟨t, ht, β', hw, h⟩ := h
  simp only at h
  refine ⟨t, ht, β', ⟨fun y z => ?_, fun a y z => ?_⟩, fun y => ?_, hw, LinearMap.ext₂ fun a b => ?_⟩
  · have : (β' y z : ℝ) = β' z y := by rw [← h, ← h, hb.1 y z]
    exact_mod_cast this
  · have : (β' (a • y) z : ℝ) = β' y (bar a • z) := by rw [← h, ← h, hb.2 a y z]
    exact_mod_cast this
  · have : (0 : ℝ) ≤ β' y y := by rw [← h]; exact mul_nonneg ht.le (by exact_mod_cast hp y)
    exact_mod_cast this
  · simp [← h]

theorem InRCone.of_toReal_eq_smul {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β β' : LinearMap.BilinForm ℤ X}
    (hβ : InRCone γ β) {t : ℝ} (ht : 0 ≤ t) (e : toReal β' = t • toReal β) : InRCone γ β' := by
  obtain ⟨c, hc, e'⟩ := hβ
  refine ⟨fun i => t * c i, fun i => mul_nonneg ht (hc i), ?_⟩
  rw [e, e', Finset.smul_sum]
  simp only [smul_smul]

theorem exists_isFaceCut {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hh : ∀ j, 0 ≤ h (γ j)) : ∃ (m' : ℕ) (s : Fin m' ↪ Fin m), IsFaceCut γ s h := by
  classical
  let e := Fintype.equivFin {j : Fin m // h (γ j) = 0}
  refine ⟨_, e.symm.toEmbedding.trans (Function.Embedding.subtype _), hh, fun j => ⟨fun hj => ⟨e ⟨j, hj⟩, by simp⟩, ?_⟩⟩
  rintro ⟨i, rfl⟩
  exact (e.symm i).2

theorem inRCone_face {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β)
    (h0 : h β = 0) : InRCone (fun j => γ (s j)) β := by
  classical
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  rw [h0, Int.cast_zero] at h1
  have hz : ∀ i, c i * (h (γ i) : ℝ) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hc i) (by exact_mod_cast hf.1 i))).1 h1.symm i
      (Finset.mem_univ _)
  have hc0 : ∀ i, i ∉ Set.range s → c i = 0 := fun i hi => by
    have hpos : (h (γ i) : ℝ) ≠ 0 := by exact_mod_cast fun h' => hi ((hf.2 i).1 h')
    exact (mul_eq_zero.1 (hz i)).resolve_right hpos
  refine ⟨fun j => c (s j), fun j => hc _, ?_⟩
  rw [e]
  have hm := Finset.sum_map Finset.univ s (fun i => c i • toReal (γ i))
  rw [← hm]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hc0 i (fun ⟨j, hj⟩ => hi (Finset.mem_map.2 ⟨j, Finset.mem_univ _, hj⟩)), zero_smul]

theorem IsFaceCut.apply_eq_zero {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X}
    (hβ : InRCone (fun j => γ (s j)) β) : h β = 0 := by
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  simp only [(hf.2 _).2 ⟨_, rfl⟩, Int.cast_zero, mul_zero, Finset.sum_const_zero] at h1
  exact_mod_cast h1

theorem inRCone_of_sub {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (s : Fin m' → Fin m)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone (fun j => γ (s j)) β) : InRCone γ β :=
  inRCone_trans (fun j => inRCone_self γ (s j)) hβ

theorem isTwInv_starLab {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {lab w : InvFun (𝓞 E)}
    (hl : IsTwInv H lab) (hw : IsTwInv H w) : IsTwInv H (starLab lab w) := by
  intro σ hσ n B
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] (Fin n → 𝓞 E) :=
    AddEquiv.toIntLinearEquiv (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)
  have he : ∀ a, e a = fun i => σ (a i) := fun a => rfl
  have hwt : ∀ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E),
      w.evalZ (β.compl₁₂ e.toLinearMap e.toLinearMap) = w.evalZ β := fun β => by
    simp only [InvFun.evalZ, InvFun.eval_pi, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he]
    exact hw σ hσ n (fun a b => (β a b : ℝ))
  have key : IsCentreRay w (Fin n → 𝓞 E) (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ↔
      IsCentreRay w (Fin n → 𝓞 E) B := by
    constructor
    · rintro ⟨t, ht, β, h1, h2⟩
      refine ⟨t, ht, β.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, ?_, fun a b => ?_⟩
      · rw [← hwt, ← h1]
        congr 1
        ext a b
        simp
      · have := h2 (e.symm a) (e.symm b)
        simp only [← he, LinearEquiv.apply_symm_apply] at this
        simpa using this
    · rintro ⟨t, ht, β, h1, h2⟩
      exact ⟨t, ht, β.compl₁₂ e.toLinearMap e.toLinearMap, by rw [hwt, h1], fun a b => by
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he, h2]⟩
  have hlab := hl σ hσ n B
  simp only [starLab]
  by_cases hc : IsCentreRay w (Fin n → 𝓞 E) B
  · rw [if_pos (key.2 hc), if_pos hc]
  · rw [if_neg (mt key.1 hc), if_neg hc, hlab]

end GlobalTheory.PolFan.StarLab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellsFiniteCoverUpToAut
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan

theorem inRCone_of_range_subset {X : Type} [AddCommGroup X] {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}
    {γ' : Fin m' → LinearMap.BilinForm ℤ X} (hsub : Set.range γ ⊆ Set.range γ') {β : LinearMap.BilinForm ℤ X}
    (h : InRCone γ β) : InRCone γ' β := by
  classical
  obtain ⟨c, hc, hβ⟩ := h
  have hj : ∀ i, ∃ j, γ' j = γ i := fun i => hsub ⟨i, rfl⟩
  choose j hj using hj
  refine ⟨fun k => ∑ i, if j i = k then c i else 0, fun k => Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact hc i
    · exact le_refl 0, ?_⟩
  rw [hβ]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (j i) (fun k _ hk => by rw [if_neg (Ne.symm hk), zero_smul]) (by simp), if_pos rfl, hj]

theorem evalZ_zero_form {O : Type} [CommRing O] (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] : φ.evalZ (0 : LinearMap.BilinForm ℤ X) = 0 := by
  rw [← evalR_toReal]
  have : toReal (0 : LinearMap.BilinForm ℤ X) = 0 := LinearMap.ext₂ fun a b => by simp
  rw [this, evalR_zero]

theorem isStarOf_finite_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' →
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
    Module.finrank (𝓞 E) X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X),
      ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar ψ' γ ∧
        (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  intro E _ _ _ H q ψ w ψ' hψ hw hst X _ _ _ _ hX
  obtain ⟨S, hS, hcov⟩ := (hψ X hX).finite
  obtain ⟨hw1, -, hw3⟩ := hw X hX

  let C : Set (LinearMap.BilinForm ℤ X) := {v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
    (∀ i, γ i ∈ S) ∧ v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}
  let CT : Set (LinearMap.BilinForm ℤ X) → Set (LinearMap.BilinForm ℤ X) := fun T =>
    {v | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ Set.range γ = T ∧
      v ∈ balForms H.bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v}
  have hCT : ∀ T, (CT T).Subsingleton := by
    rintro T v₁ ⟨m₁, γ₁, hγ₁, hr₁, hb₁, hp₁, hv₁, hi₁⟩ v₂ ⟨m₂, γ₂, hγ₂, hr₂, hb₂, hp₂, hv₂, hi₂⟩
    exact hw3 m₁ γ₁ hγ₁ v₁ hb₁ hp₁ v₂ hb₂ hp₂ hv₁ hv₂ hi₁
      (inRCone_of_range_subset (by rw [hr₁, hr₂]) hi₂)
  have hC : C.Finite := by
    refine (hS.powerset.biUnion fun T _ => (hCT T).finite).subset ?_
    rintro v ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩
    refine Set.mem_biUnion (x := Set.range γ) ?_ ⟨m, γ, hγ, rfl, hb, hp, hv, hi⟩
    rintro _ ⟨i, rfl⟩
    exact hγS i
  refine ⟨S ∪ C, hS.union hC, fun B hB => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hBc⟩ := hcov B hB
  by_cases hex : ∃ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hb, hp, hv, hi⟩ := hex
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [evalZ_zero_form] at hv
      exact zero_ne_one hv
    obtain ⟨m', s, h, hcut, hpos, t, ht, hBt⟩ :=
      _root_.GlobalTheory.StarCover.star_cover X m γ v (pullR e.toLinearMap B) (fun i y z => (hγ.mem i).1 y z) hγ.nonneg hv0 hi ⟨c, hc, hBc⟩
    refine ⟨e, m' + 1, Fin.cons v fun j => γ (s j), t,
      hst.2.1 X hX m γ hγ v hb hp hv hi m' s h hcut hpos, fun i => ?_, ht, hBt⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inr ⟨m, γ, hγ, hγS, hb, hp, hv, hi⟩
    · simp only [Fin.cons_succ]
      exact Or.inl (hγS (s j))
  · refine ⟨e, m, γ, c, hst.1 X hX m γ hγ fun β hb hp hi => ?_, fun i => Or.inl (hγS i), hc, hBc⟩
    rcases hw1 β hb hp with h0 | h1
    · exact h0
    · exact (hex ⟨β, hb, hp, h1, hi⟩).elim

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

theorem charpolyRev_conj_of_mul_eq_one {R : Type*} [CommRing R] {r : Type*} [Fintype r] [DecidableEq r]
    (M P Q : Matrix r r R) (hQP : Q * P = 1) : (Q * M * P).charpolyRev = M.charpolyRev := by
  have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : (1 : Matrix r r (Polynomial R)) - (Polynomial.X : Polynomial R) • (Q * M * P).map Polynomial.C =
      Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • M.map Polynomial.C) * P.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
      Matrix.mul_smul, Matrix.smul_mul]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
    ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]

theorem curvPoly_eq_sum {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : curvPoly G v =
      ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) • (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern

theorem gram_eq_changeFrame {r : Type} [Fintype r] (c : ℝ) (hc : 0 < c) (g K : Matrix r r ℂ) :
    (c : ℂ) • (g * K * gᴴ) = (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᵀ * K * (((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ := by
  have h1 : ((((Real.sqrt c : ℝ) : ℂ) • gᵀ)ᴴᵀ) = ((Real.sqrt c : ℝ) : ℂ) • gᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  have h2 : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rw [h1, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, h2]

theorem chernTop_changeFrame : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (G K g : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (c : ι → ℝ) (v : ReciprocityTheory.L2DbarEstimates.V n), (∀ τ, 0 < c τ) → (∀ τ i j, AnalyticAt ℂ (fun w => g w τ i j) v) → (∀ τ, IsUnit (g v τ).det) → (∀ τ, MContDiffAt 2 (fun w => K w τ) v) → (∀ τ, IsUnit (K v τ).det) → (∀ᶠ w in 𝓝 v, ∀ τ, G w τ = (c τ : ℂ) • (g w τ * K w τ * (g w τ)ᴴ)) → chernTop R G v = chernTop R K v := by
  intro n ι m R G K g c v hc hg hgu hK hKu hG
  have key : ∀ τ, curvPoly (fun u => G u τ) v = ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)⁻¹).map C *
      curvPoly (fun u => K u τ) v * ((((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ)).map C := by
    intro τ
    set A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ :=
      fun u => ((Real.sqrt (c τ) : ℝ) : ℂ) • (g u τ)ᵀ with hAdef
    have hent : ∀ a b, (fun x => A x a b) = fun x => ((Real.sqrt (c τ) : ℝ) : ℂ) * g x τ b a := fun a b => rfl
    have hA : MContDiffAt 2 A v := fun a b => by
      rw [hent]
      exact contDiffAt_const.mul ((hg τ b a).contDiffAt.restrict_scalars ℝ)
    have hAu : IsUnit (A v).det := by
      simp only [hAdef, Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
      have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => g w τ b a) x :=
        eventually_all.2 fun a => eventually_all.2 fun b => (hg τ b a).eventually_analyticAt
      filter_upwards [hev] with x hx η
      ext a b
      rw [mdbar_apply, hent, GlobalTheory.dbar_eq_zero (((hx a b).differentiableAt).const_mul _)]
      rfl
    have hGe : (fun u => G u τ) =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u τ * (A u)ᴴᵀ :=
      hG.mono fun u hu => by show G u τ = _; rw [hu τ]; exact gram_eq_changeFrame _ (hc τ) _ _
    have hcurv : ∀ ξ η, curv (fun u => G u τ) v ξ η = (A v)⁻¹ * curv (fun u => K u τ) v ξ η * A v :=
      fun ξ η => by rw [curv_congr hGe, curv_changeFrame (hK τ) (hKu τ) hA hAu hA0]
    clear_value A
    rw [curvPoly_eq_sum, curvPoly_eq_sum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
    subst hAdef
    rfl
  have key2 : ∀ τ k, chernPoly (fun u => G u τ) v k = chernPoly (fun u => K u τ) v k := by
    intro τ k
    have hu : IsUnit (((Real.sqrt (c τ) : ℝ) : ℂ) • (g v τ)ᵀ).det := by
      simp only [Matrix.det_smul, Matrix.det_transpose]
      refine IsUnit.mul (IsUnit.pow _ (Ne.isUnit ?_)) (hgu τ)
      exact_mod_cast (Real.sqrt_pos.2 (hc τ)).ne'
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Fin n × Fin n) ℂ)), -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], charpolyRev_conj_of_mul_eq_one]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [chernTop, key2]

end GlobalTheory.PointChern
end

