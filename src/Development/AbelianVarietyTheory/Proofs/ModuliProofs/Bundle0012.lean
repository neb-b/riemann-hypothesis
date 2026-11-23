module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ThetaQuasiPeriods.Transl
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HolPeriods

section HolTo

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X : Scheme.{0}}

theorem isHolTo_congr {B : Set V} {y y' : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (hy : ∀ b ∈ B, y' b = y b) :
    IsHolTo B y' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, hy b h1 ▸ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hy b h1).symm ▸ h2⟩
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [hy b hb.1]⟩

theorem isHolTo_comp {B : Set V} {C : Set W} {y : V → (Sp ℂ ⟶ X)} {φ : W → V} (h : IsHolTo B y)
    (hC : IsOpen C) (hφ : DifferentiableOn ℂ φ C) (hm : Set.MapsTo φ C B) :
    IsHolTo C (fun c => y (φ c)) := by
  intro U f
  have hs : {c ∈ C | ⊤ ≤ y (φ c) ⁻¹ᵁ U} = C ∩ φ ⁻¹' {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext c
    exact ⟨fun hc => ⟨hc.1, hm hc.1, hc.2⟩, fun hc => ⟨hc.1, hc.2.2⟩⟩
  refine ⟨?_, ?_⟩
  · rw [hs]; exact hφ.continuousOn.isOpen_inter_preimage hC (h U f).1
  · exact (h U f).2.comp (hφ.mono fun c hc => hc.1) fun c hc => ⟨hm hc.1, hc.2⟩

theorem isHolTo_of_local {B : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : ∀ b ∈ B, ∃ B' : Set V, b ∈ B' ∧ B' ⊆ B ∧ IsHolTo B' y) : IsHolTo B y := by
  intro U f
  have key : ∀ b ∈ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}, {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∈ nhds b ∧
      DifferentiableAt ℂ (fun b => valAt' (y b) U f) b := by
    intro b hb
    obtain ⟨B', hb', hsub, hB'⟩ := h b hb.1
    have hn := (hB' U f).1.mem_nhds (⟨hb', hb.2⟩ : b ∈ {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ U})
    exact ⟨Filter.mem_of_superset hn fun c hc => ⟨hsub hc.1, hc.2⟩, (hB' U f).2.differentiableAt hn⟩
  exact ⟨isOpen_iff_mem_nhds.2 fun b hb => (key b hb).1,
    fun b hb => (key b hb).2.differentiableWithinAt⟩

end HolTo

theorem exists_local_section {n : ℕ} {U : Set (Fin n → ℂ)} {F : (Fin n → ℂ) → (Fin n → ℂ)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {a : Fin n → ℂ} (ha : a ∈ U) (hb : Function.Bijective (fderiv ℂ F a)) :
    ∃ (W : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin n → ℂ)), IsOpen W ∧ F a ∈ W ∧ DifferentiableOn ℂ G W ∧
      ∀ w ∈ W, G w ∈ U ∧ F (G w) = w := by
  have han : AnalyticAt ℂ F a := GlobalTheory.SCV.analyticAt_of_differentiableOn hF (hU.mem_nhds ha)
  have hc : ContDiffAt ℂ ⊤ F a := han.contDiffAt
  let f' : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearEquiv.ofBijective (fderiv ℂ F a : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) hb).toContinuousLinearEquiv
  have hd : HasFDerivAt F (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) a := by
    have : (f' : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F a := by ext1; rfl
    rw [this]; exact han.differentiableAt.hasFDerivAt
  have hinv := hc.to_localInverse hd (by simp)
  have hs := hc.hasStrictFDerivAt' hd (by simp)
  have h1 : ∀ᶠ w in nhds (F a), F (hc.localInverse hd (by simp) w) = w := hs.eventually_right_inverse
  have h2 : ∀ᶠ w in nhds (F a), hc.localInverse hd (by simp) w ∈ U := by
    have := hinv.continuousAt
    rw [ContinuousAt, hc.localInverse_apply_image] at this
    exact this (hU.mem_nhds ha)
  have h3 : ∀ᶠ w in nhds (F a), DifferentiableAt ℂ (hc.localInverse hd (by simp)) w :=
    (hinv.analyticAt.eventually_analyticAt).mono fun w hw => hw.differentiableAt
  obtain ⟨W, hW, hWo, hWa⟩ := eventually_nhds_iff.1 (h1.and (h2.and h3))
  exact ⟨W, _, hWo, hWa, fun w hw => (hW w hw).2.2.differentiableWithinAt,
    fun w hw => ⟨(hW w hw).2.1, (hW w hw).1⟩⟩

theorem exists_differentiableOn_transfer {V Λ : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [AddCommGroup Λ]
    {g : ℕ} {B : Set V} (hB : IsOpen B) {Q Q' : V → (Λ →+ (Fin g → ℂ))}
    (hQ : ∀ x, DifferentiableOn ℂ (fun b => Q b x) B) (hQ' : ∀ x, DifferentiableOn ℂ (fun b => Q' b x) B)
    {b₀ : V} (hb₀ : b₀ ∈ B) (hspan : Submodule.span ℝ (Set.range (Q b₀)) = ⊤)
    (k : V → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (hk : ∀ b ∈ B, ∀ x, Q' b x = k b (Q b x)) :
    ∃ B' : Set V, IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => k bz.1 bz.2) (B' ×ˢ Set.univ) := by
  classical
  have hc : ∀ i : Fin g, ∃ c : Λ →₀ ℝ, (c.sum fun a r => r • Q b₀ a) = Pi.single i 1 := fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 (by rw [hspan]; trivial)
  choose c hc using hc
  let M : (V → (Λ →+ (Fin g → ℂ))) → V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun R b =>
    ∑ i, (ContinuousLinearMap.proj i : (Fin g → ℂ) →L[ℂ] ℂ).smulRight
      (∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • R b a)
  have hM : ∀ R : V → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun b => R b x) B) →
      DifferentiableOn ℂ (M R) B := by
    intro R hR
    refine DifferentiableOn.fun_sum fun i _ => ?_
    refine ((ContinuousLinearMap.smulRightL ℂ (Fin g → ℂ) (Fin g → ℂ)
      (ContinuousLinearMap.proj i)).differentiable.comp_differentiableOn ?_)
    exact DifferentiableOn.fun_sum fun a _ => (hR a).fun_const_smul _
  have h0 : M Q b₀ = 1 := by
    ext1 z
    have : ∀ i, ∑ a ∈ (c i).support, ((c i a : ℝ) : ℂ) • Q b₀ a = Pi.single i 1 := fun i => by
      rw [← hc i]; simp [Finsupp.sum]
    simp only [M, this, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.one_apply]
    ext j; simp [Pi.single_apply]
  have hkM : ∀ b ∈ B, ∀ z, k b (M Q b z) = M Q' b z := by
    intro b hb z
    set_option synthInstance.maxHeartbeats 100000 in
      simp [M, map_sum, hk b hb]
  refine ⟨B ∩ M Q ⁻¹' {x | IsUnit x}, (hM Q hQ).continuousOn.isOpen_inter_preimage hB Units.isOpen,
    ⟨hb₀, by simp [h0]⟩, Set.inter_subset_left, ?_⟩
  have hd : DifferentiableOn ℂ (fun b => M Q' b * Ring.inverse (M Q b)) (B ∩ M Q ⁻¹' {x | IsUnit x}) := by
    refine ((hM Q' hQ').mono Set.inter_subset_left).mul fun b hb => ?_
    exact (differentiableAt_inverse hb.2).comp_differentiableWithinAt b
      ((hM Q hQ).mono Set.inter_subset_left b hb)
  have hd2 : DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => (M Q' bz.1 * Ring.inverse (M Q bz.1)) bz.2)
      ((B ∩ M Q ⁻¹' {x | IsUnit x}) ×ˢ Set.univ) :=
    (hd.comp differentiableOn_fst (fun (bz : V × (Fin g → ℂ))
      (hbz : bz ∈ (B ∩ M Q ⁻¹' {x | IsUnit x}) ×ˢ Set.univ) => hbz.1)).clm_apply differentiableOn_snd
  refine hd2.congr fun bz hbz => ?_
  rw [ContinuousLinearMap.mul_apply, ← hkM _ hbz.1.1, ← ContinuousLinearMap.mul_apply,
    Ring.mul_inverse_cancel _ hbz.1.2, ContinuousLinearMap.one_apply]

theorem isDerivAt0_comp_equiv {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => e (k z)) w v ↔ IsDerivAt0 e (k w) v := by
  have : ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (k z)) U f) 0 w =
      fderiv ℂ (fun z => valAt' (e z) U f) 0 (k w) := by
    intro U f
    have := k.toContinuousLinearEquiv.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)
    have h2 := congrArg (fun L => L w) this
    simpa [Function.comp_def] using h2
  simp only [IsDerivAt0, map_zero, this]

end GlobalTheory.HolPeriods
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHalfOfSqEqOne
section
noncomputable section

open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real

namespace GlobalTheory.ThetaPoint

open CanTh

variable {g : ℕ}

theorem isSymm_and_eq_imInv {M τ : Matrix (Fin g) (Fin g) ℂ} (hH : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) (hτ : (τ.map Complex.im).PosDef)
    {s : ℝ} (hs : s = 1 ∨ s = -1)
    (h₁₁ : ∀ i j, (hermForm M (Pi.single i 1) (Pi.single j 1)).im = 0)
    (h₁₂ : ∀ i j, (hermForm M (Pi.single i 1) (τ *ᵥ Pi.single j 1)).im = if i = j then s else 0)
    (h₂₂ : ∀ i j, (hermForm M (τ *ᵥ Pi.single i 1) (τ *ᵥ Pi.single j 1)).im = 0) :
    τ.IsSymm ∧ M = imInv τ := by
  let Y : Matrix (Fin g) (Fin g) ℝ := M.map Complex.re
  have hY : M = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · have := h₁₁ i j
      rw [hermForm, SiegelNormalForm.form_single] at this
      simpa using this
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (hH.apply i j)
    simpa [Y] using this
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : (fun i => (a i : ℂ)) ≠ 0 := fun h0 =>
      ha (funext fun i => by simpa using congrFun h0 i)
    have := hpos _ hne
    rw [hY] at this
    simpa [hermForm, Matrix.mulVec, dotProduct] using this
  rw [hY] at h₁₂ h₂₂
  rcases hs with rfl | rfl
  · obtain ⟨-, h2, -⟩ := SiegelNormalForm.siegel_of_relations Y hYp (-τ)
      (fun i j => by
        have := h₁₂ i j
        rw [hermForm] at this
        rw [Matrix.neg_mulVec, star_neg, Matrix.mulVec_neg, dotProduct_neg, Complex.neg_im, this]
        split_ifs <;> simp)
      (fun i j => by
        have := h₂₂ i j
        rw [hermForm] at this
        rw [Matrix.neg_mulVec, Matrix.neg_mulVec, star_neg, Matrix.mulVec_neg, dotProduct_neg,
          neg_dotProduct, neg_neg, this])
    have hf : ∀ i : Fin g, False := fun i => by
      have e1 := h2.diag_pos (i := i)
      have e2 := hτ.diag_pos (i := i)
      simp only [Matrix.map_apply, Matrix.neg_apply, Complex.neg_im] at e1 e2
      linarith
    exact ⟨by ext i; exact (hf i).elim, by ext i; exact (hf i).elim⟩
  · obtain ⟨h1, -, h3⟩ := SiegelNormalForm.siegel_of_relations Y hYp τ h₁₂ h₂₂
    refine ⟨h1, ?_⟩
    rw [hY, imInv, Matrix.inv_eq_left_inv h3]

def lawSubgroup {Λ V : Type*} [AddCommGroup Λ] [AddCommGroup V] (ι : Λ →+ V) (J : Λ → V → ℂ)
    (hJ : ∀ l z, J l z ≠ 0) (hc : ∀ l m z, J (l + m) z = J l (z + ι m) * J m z) (θ : V → ℂ) :
    AddSubgroup Λ where
  carrier := {l | ∀ z, θ (z + ι l) = J l z * θ z}
  zero_mem' := fun z => by
    have h := hc 0 0 z
    rw [add_zero, map_zero, add_zero] at h
    rw [map_zero, add_zero, (mul_eq_left₀ (hJ 0 z)).1 h.symm, one_mul]
  add_mem' := fun {l m} hl hm z => by
    rw [map_add (f := _), add_comm (ι l), ← add_assoc, hl, hm, hc, mul_assoc]
  neg_mem' := fun {l} hl z => by
    have h0 := hc 0 0 z
    rw [add_zero, map_zero, add_zero] at h0
    have h1 := hc l (-l) z
    rw [add_neg_cancel, (mul_eq_left₀ (hJ 0 z)).1 h0.symm] at h1
    have h2 := hl (z + ι (-l))
    rw [add_assoc, ← map_add (f := _), neg_add_cancel, map_zero, add_zero] at h2
    rw [h2, ← mul_assoc, mul_comm (J (-l) z), ← h1, one_mul]

theorem exists_half_of_sq_eq_one {c : ℂ} (hc : c ^ 2 = 1) :
    ∃ a : ℝ, (a = 0 ∨ a = 1 / 2) ∧ cexp (2 * π * I * a) = c ∧ cexp (-(2 * π * I * a)) = c := by
  rcases sq_eq_one_iff.1 hc with rfl | rfl
  · exact ⟨0, Or.inl rfl, by simp, by simp⟩
  · refine ⟨1 / 2, Or.inr rfl, ?_, ?_⟩
    · rw [← Complex.exp_pi_mul_I]; congr 1; push_cast; ring
    · rw [← Complex.exp_neg_pi_mul_I]; congr 1; push_cast; ring

theorem exists_half_char {d : ℕ} (Λ : Submodule ℤ (Fin d → ℂ)) (Hm : Matrix (Fin d) (Fin d) ℂ) (χ : Λ → ℂ)
    (Φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef)
    (hform : ∀ z w, hermForm Hm (Φ z) (Φ w) = hermForm (imInv τ) z w)
    (hΛ : ∀ z, Φ z ∈ Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ))
    (hχ : ∀ l, χ l ^ 2 = 1)
    (hc : ∀ (l m : Λ) z, χ (l + m) * cexp (π * hermForm Hm z (l + m : Λ) + π / 2 * hermForm Hm (l + m : Λ) (l + m : Λ)) =
      χ l * cexp (π * hermForm Hm (z + m) l + π / 2 * hermForm Hm l l) *
        (χ m * cexp (π * hermForm Hm z m + π / 2 * hermForm Hm m m))) :
    ∃ a b : Fin g → ℝ, (∀ k, a k = 0 ∨ a k = 1 / 2) ∧ (∀ k, b k = 0 ∨ b k = 1 / 2) ∧
      ∀ (l : Λ) z, canTh τ a b (Φ.symm (z + l)) =
        χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l) * canTh τ a b (Φ.symm z) := by
  have hsingle : ∀ j : Fin g, (fun i => (((Pi.single j (1 : ℤ) : Fin g → ℤ) i : ℤ) : ℂ)) = Pi.single j (1 : ℂ) := by
    intro j
    ext i
    by_cases hij : i = j <;> simp [Pi.single_apply, hij]
  have hzero : (fun i => (((0 : Fin g → ℤ) i : ℤ) : ℂ)) = 0 := by ext i; simp
  let e : Fin g → Λ := fun i => ⟨Φ (Pi.single i 1), (hΛ _).2 ⟨Pi.single i 1, 0, by
    rw [hsingle, hzero, mulVec_zero, add_zero]⟩⟩
  let f : Fin g → Λ := fun i => ⟨Φ (τ *ᵥ Pi.single i 1), (hΛ _).2 ⟨0, Pi.single i 1, by
    rw [hsingle, hzero, zero_add]⟩⟩
  choose a ha ha' _ using fun i => exists_half_of_sq_eq_one (hχ (e i))
  choose b hb _ hb' using fun i => exists_half_of_sq_eq_one (hχ (f i))
  refine ⟨a, b, ha, hb, fun l => ?_⟩
  let S := lawSubgroup Λ.subtype.toAddMonoidHom
    (fun l z => χ l * cexp (π * hermForm Hm z l + π / 2 * hermForm Hm l l))
    (fun l z => mul_ne_zero (fun h => by simpa [h] using hχ l) (Complex.exp_ne_zero _)) hc
    (fun z => canTh τ a b (Φ.symm z))
  have key : ∀ (l : Λ) (m n : Fin g → ℤ), (l : Fin d → ℂ) = Φ ((fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) →
      canMult a b m n = χ l → l ∈ S := fun l m n hl hm z => by
    obtain ⟨z, rfl⟩ := Φ.surjective z
    change canTh τ a b (Φ.symm (Φ z + l)) = χ l * cexp (π * hermForm Hm (Φ z) l + π / 2 * hermForm Hm l l) *
      canTh τ a b (Φ.symm (Φ z))
    rw [hl, ← map_add (f := _), Φ.symm_apply_apply, Φ.symm_apply_apply, hform, hform,
      canTh_add_period hs hp a b m n rfl, hm]
  have he : ∀ i, e i ∈ S := fun i => key _ (Pi.single i 1) 0
    (by rw [hsingle, hzero, mulVec_zero, add_zero]) (by
      rw [← ha', canMult]
      congr 1
      simp [dotProduct, Pi.single_apply])
  have hf : ∀ i, f i ∈ S := fun i => key _ 0 (Pi.single i 1)
    (by rw [hsingle, hzero, zero_add]) (by
      rw [← hb', canMult]
      congr 1
      simp [dotProduct, Pi.single_apply])
  obtain ⟨m, n, hmn⟩ := (hΛ (Φ.symm l)).1 (by rw [Φ.apply_symm_apply]; exact l.2)
  have hl : l = ∑ i, m i • e i + ∑ i, n i • f i := by
    apply Subtype.ext
    have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    rw [← Φ.apply_symm_apply l, hmn, h1 m, h1 n]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_add (f := _), map_sum, map_zsmul, e, f]
    simp
  have : l ∈ S := hl ▸ S.add_mem (S.sum_mem fun i _ => S.zsmul_mem (he i) _)
    (S.sum_mem fun i _ => S.zsmul_mem (hf i) _)
  exact this

theorem half_char_unique {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    {a b a' b' : Fin g → ℝ} (ha : ∀ k, a k = 0 ∨ a k = 1 / 2) (hb : ∀ k, b k = 0 ∨ b k = 1 / 2)
    (ha' : ∀ k, a' k = 0 ∨ a' k = 1 / 2) (hb' : ∀ k, b' k = 0 ∨ b' k = 1 / 2)
    {U : (Fin g → ℂ) → ℂ} (hU : Differentiable ℂ U) (hU0 : ∀ z, U z ≠ 0)
    (h : ∀ z, theta a' b' z τ = U z * theta a b z τ) : a' = a ∧ b' = b := by
  have H₁ : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
      (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z,
        (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') =
          eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧
        (fun z => theta 0 0 z τ) ≠ 0 := fun g τ hτ => by
    refine ⟨⟨?_, fun n n' z => ?_⟩, theta_ne_zero hτ 0 0⟩
    · have := differentiable_thetaChar (mem_thetaDomain hτ.2) 0 0
      simpa only [← thetaChar_eq_theta] using this
    · have h0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
      simp only [thetaQuasiPeriod_holds (Fin g) 0 0 z τ n n' hτ.1, autFactor, h0, zero_dotProduct, sub_zero, eC_zero,
        one_mul]
      congr 2
      ring
  let p : (Fin g → ℝ) → (Fin g → ℝ) → (Fin g → ℂ) → ℂ := fun a b z =>
    eC (ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a) / 2 + ofRealVec a ⬝ᵥ (z + ofRealVec b + ofRealVec 0))
  have hp0 : ∀ a b z, p a b z ≠ 0 := fun a b z => Complex.exp_ne_zero _
  have hpd : ∀ a b, Differentiable ℂ (p a b) := fun a b => by
    simp only [p, eC, dotProduct]
    fun_prop
  have sh : ∀ a b z, theta a b z τ = p a b z * theta 0 0 (z + τ *ᵥ ofRealVec a + ofRealVec b) τ := fun a b z => by
    simpa only [zero_add] using thetaCharShift_holds (Fin g) a b 0 0 z τ hs
  let v := τ *ᵥ ofRealVec a + ofRealVec b
  obtain ⟨n, n', hn⟩ := mem_periodLattice_of_theta_translate_eq_unit_mul H₁
    periodLattice_isLattice_of_mem_siegelH g τ ⟨hs, hp⟩ (τ *ᵥ ofRealVec a' + ofRealVec b' - v)
    (fun z => U (z - v) * p a b (z - v) * (p a' b' (z - v))⁻¹)
    (((hU.comp (differentiable_id.sub_const v)).mul ((hpd a b).comp (differentiable_id.sub_const v))).mul
      (((hpd a' b').comp (differentiable_id.sub_const v)).inv fun z => hp0 _ _ _))
    (fun z => mul_ne_zero (mul_ne_zero (hU0 _) (hp0 _ _ _)) (inv_ne_zero (hp0 _ _ _))) (fun z => by
      have e := h (z - v)
      rw [sh a' b', sh a b, show z - v + τ *ᵥ ofRealVec a + ofRealVec b = z by simp only [v]; abel,
        show z - v + τ *ᵥ ofRealVec a' + ofRealVec b' = z + (τ *ᵥ ofRealVec a' + ofRealVec b' - v) by abel] at e
      have := hp0 a' b' (z - v)
      field_simp
      linear_combination e)
  have him : (τ.map Complex.im) *ᵥ (a' - a - fun i => (n i : ℝ)) = 0 := by
    ext i
    have := congrArg Complex.im (congrFun hn i)
    simp only [v, mulVec, dotProduct, ofRealVec, ofIntVec, Pi.add_apply, Pi.sub_apply, add_im, sub_im, im_sum,
      mul_im, ofReal_re, ofReal_im, intCast_re, intCast_im, mul_zero, zero_add, add_zero] at this
    simp only [mulVec, dotProduct, map_apply, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
    linarith
  have h1 : (a' - a - fun i => (n i : ℝ)) = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.2 hp.isUnit) (him.trans (mulVec_zero _).symm)
  have half : ∀ (x y : ℝ) (k : ℤ), (x = 0 ∨ x = 1 / 2) → (y = 0 ∨ y = 1 / 2) → x - y = k → x = y ∧ k = 0 := by
    intro x y k hx hy e
    have h1 : (-1 : ℝ) < k := by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
    have h2 : (k : ℝ) < 1 := by rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> linarith
    have h3 : k = 0 := by
      have : (-1 : ℤ) < k := by exact_mod_cast h1
      have : k < 1 := by exact_mod_cast h2
      omega
    subst h3
    exact ⟨by simpa [sub_eq_zero] using e, rfl⟩
  have h2 := fun i => half _ _ (n i) (ha' i) (ha i) (sub_eq_zero.1 (congrFun h1 i))
  obtain rfl : a' = a := funext fun i => (h2 i).1
  obtain rfl : n = 0 := funext fun i => (h2 i).2
  refine ⟨rfl, funext fun i => (half _ _ (n' i) (hb' i) (hb i) ?_).1⟩
  simp only [v, ofIntVec_zero, mulVec_zero, zero_add, add_sub_add_left_eq_sub] at hn
  have := congrFun hn i
  simp only [Pi.sub_apply, ofRealVec, ofIntVec] at this
  exact_mod_cast this

end GlobalTheory.ThetaPoint
end
end

