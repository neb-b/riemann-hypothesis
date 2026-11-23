module

public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.ContinuousOnOrbit
section
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {Hm : Mat n} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat n → (H →L[ℂ] H)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem LieWd.lieW {W : List (Mat n)} (h : LieWd Hm W) : LieW (UH Hm) W := fun X hX t => ex_mem_of_lie (h X hX) t

theorem CWLin.comp_sigma (hAd : DsAd) (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {y : Mat n}
    (hy : y ∈ UH Hm) : CWLin Hm σ (fun v => B (σ y v)) := by
  refine ⟨fun x hx x' hx' => ?_, fun a x hx => ?_, ?_⟩
  · rw [map_add (f := _), hB.add _ (hx.apply hU.rep hy) _ (hx'.apply hU.rep hy)]
  · rw [map_smul, hB.smul _ _ (hx.apply hU.rep hy)]
  · obtain ⟨C, Ws, hWs, hb⟩ := hB.bd
    refine ⟨C, Ws.map fun W => W.map fun X => y⁻¹ * X * y, fun W hW => ?_, fun v hv => ?_⟩
    · obtain ⟨W', hW', rfl⟩ := List.mem_map.1 hW
      exact (hAd n Hm H σ hU y hy W' (hWs W' hW')).1
    · refine (hb _ (hv.apply hU.rep hy)).trans_eq ?_
      rw [List.map_map]
      congr 2
      refine List.map_congr_left fun W hW => ?_
      rw [(hAd n Hm H σ hU y hy W (hWs W hW)).2 v hv, hU.iso y hy]
      rfl

omit [CompleteSpace H] in
theorem CWLin.comb {B₁ B₂ : H → V} (h₁ : CWLin Hm σ B₁) (h₂ : CWLin Hm σ B₂) (a b : ℂ) :
    CWLin Hm σ (fun v => a • B₁ v + b • B₂ v) := by
  refine ⟨fun x hx x' hx' => ?_, fun c x hx => ?_, ?_⟩
  · rw [h₁.add _ hx _ hx', h₂.add _ hx _ hx', smul_add, smul_add]; abel
  · rw [h₁.smul _ _ hx, h₂.smul _ _ hx, smul_add, smul_comm a c, smul_comm b c]
  · obtain ⟨C₁, W₁, hW₁, hb₁⟩ := h₁.bd
    obtain ⟨C₂, W₂, hW₂, hb₂⟩ := h₂.bd
    refine ⟨‖a‖ * |C₁| + ‖b‖ * |C₂|, W₁ ++ W₂, fun W hW => (List.mem_append.1 hW).elim (hW₁ W) (hW₂ W),
      fun v hv => ?_⟩
    rw [List.map_append, List.sum_append]
    set s₁ := (W₁.map fun W => ‖dsW σ W v‖).sum
    set s₂ := (W₂.map fun W => ‖dsW σ W v‖).sum
    have p₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
      obtain ⟨W, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    have p₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
      obtain ⟨W, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    have q₁ : ‖B₁ v‖ ≤ |C₁| * s₁ := (hb₁ v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₁)
    have q₂ : ‖B₂ v‖ ≤ |C₂| * s₂ := (hb₂ v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p₂)
    have r₁ := mul_le_mul_of_nonneg_left q₁ (norm_nonneg a)
    have r₂ := mul_le_mul_of_nonneg_left q₂ (norm_nonneg b)
    have t₁ : 0 ≤ ‖a‖ * |C₁| * s₂ := by positivity
    have t₂ : 0 ≤ ‖b‖ * |C₂| * s₁ := by positivity
    calc ‖a • B₁ v + b • B₂ v‖ ≤ ‖a‖ * ‖B₁ v‖ + ‖b‖ * ‖B₂ v‖ := by
          rw [← norm_smul, ← norm_smul]; exact norm_add_le _ _
      _ ≤ _ := by nlinarith

omit [CompleteSpace H] in
theorem CWLin.zero {B : H → V} (hB : CWLin Hm σ B) : B 0 = 0 := by
  simpa using hB.smul 0 0 IsSm.zero

omit [CompleteSpace H] in
theorem CWLin.sum_orbit (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w)
    (h0 : ∀ g ∈ UH Hm, B (σ g w) = 0) {ι : Type} (s : Finset ι) (c : ι → ℂ) (g : ι → Mat n)
    (hg : ∀ i, g i ∈ UH Hm) : IsSm (UH Hm) σ (∑ i ∈ s, c i • σ (g i) w) ∧ B (∑ i ∈ s, c i • σ (g i) w) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ⟨IsSm.zero, hB.zero⟩
  | insert a s ha ih =>
    have h1 := hw.apply hU.rep (hg a)
    rw [Finset.sum_insert ha]
    exact ⟨(h1.smul _).add ih.1, by rw [hB.add _ (h1.smul _) _ ih.1, hB.smul _ _ h1, h0 _ (hg a), ih.2]; simp⟩


omit [CompleteSpace H] in
theorem CWLin.eq_zero (hU : URep Hm σ) {B : H → V} (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w)
    (h0 : ∀ g ∈ UH Hm, B (σ g w) = 0) {x : H} (hx : IsSm (UH Hm) σ x)
    (happ : ∀ Ws : List (List (Mat n)), (∀ W ∈ Ws, LieWd Hm W) → ∀ δ : ℝ, 0 < δ →
      ∃ (N : ℕ) (c : Fin N → ℂ) (g : Fin N → Mat n), (∀ i, g i ∈ UH Hm) ∧
        (Ws.map fun W => ‖dsW σ W (x - ∑ i, c i • σ (g i) w)‖).sum < δ) : B x = 0 := by
  obtain ⟨C, Ws, hWs, hb⟩ := hB.bd
  rw [← norm_le_zero_iff]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hC : 0 < |C| + 1 := by positivity
  obtain ⟨N, c, g, hg, hs⟩ := happ Ws hWs (δ / (|C| + 1)) (div_pos hδ hC)
  obtain ⟨hy, hBy⟩ := hB.sum_orbit hU hw h0 Finset.univ c g hg
  have e : B x = B (x - ∑ i, c i • σ (g i) w) := by
    have := hB.add _ (hx.sub hy) _ hy
    rw [sub_add_cancel, hBy, add_zero] at this
    exact this
  have p : 0 ≤ (Ws.map fun W => ‖dsW σ W (x - ∑ i, c i • σ (g i) w)‖).sum := List.sum_nonneg fun t ht => by
    obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht; exact norm_nonneg _
  rw [e, zero_add]
  refine (hb _ (hx.sub hy)).trans ?_
  rw [lt_div_iff₀ hC] at hs
  nlinarith [le_abs_self C]

theorem CWLin.continuousOn_orbit [FiniteDimensional ℂ V] (hF : Factor) (hU : URep Hm σ) {B : H → V}
    (hB : CWLin Hm σ B) {w : H} (hw : IsSm (UH Hm) σ w) : ContinuousOn (fun g => B (σ g w)) (UH Hm) := by
  obtain ⟨N, W, β, hW, hβ⟩ := hF n Hm H σ hU V B hB
  refine (continuousOn_finsetSum Finset.univ fun i _ =>
    (β i).continuous.comp_continuousOn (continuousOn_dsW_orbit hU.rep hw (hW i).lieW)).congr fun g hg => ?_
  exact hβ _ (hw.apply hU.rep hg)

end CompanionTheory.Bmu
end
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.NormPsiGen
section
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spanFam {n : ℕ} (S : Submodule ℝ (Mat n)) : ∃ (d : ℕ) (X : Fin d → Mat n), (∀ j, X j ∈ S) ∧
    ∀ Y ∈ S, ∃ a : Fin d → ℝ, Y = ∑ j, (a j : ℂ) • X j := by
  let b := Module.finBasis ℝ S
  refine ⟨_, fun j => (b j : Mat n), fun j => (b j).2, fun Y hY => ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩⟩
  have h := congrArg (Subtype.val) (b.sum_repr ⟨Y, hY⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
  simp only [Complex.coe_smul]
  exact h.symm

theorem lie_add {n : ℕ} {Hm X Y : Mat n} (hX : Lie Hm X) (hY : Lie Hm Y) : Lie Hm (X + Y) := by
  unfold Lie at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Xᴴ * Hm + Yᴴ * Hm + (Hm * X + Hm * Y) = (Xᴴ * Hm + Hm * X) + (Yᴴ * Hm + Hm * Y) := by abel
    _ = 0 := by rw [hX, hY, add_zero]

theorem lie_smul {n : ℕ} {Hm X : Mat n} (c : ℝ) (hX : Lie Hm X) : Lie Hm (c • X) := by
  unfold Lie at *
  rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem lie_zero {n : ℕ} (Hm : Mat n) : Lie Hm 0 := by simp [Lie]

variable {k r : ℕ}

def sUw (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InUw k r z X}
  zero_mem' := ⟨lie_zero _, fun _ => ⟨zero_mulVec _, zero_mulVec _⟩, zero_mulVec _⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun a =>
    ⟨by rw [add_mulVec, (hX.2.1 a).1, (hY.2.1 a).1, add_zero], by rw [add_mulVec, (hX.2.1 a).2, (hY.2.1 a).2, add_zero]⟩,
    by rw [add_mulVec, hX.2.2, hY.2.2, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun a =>
    ⟨by rw [smul_mulVec, (hX.2.1 a).1, smul_zero], by rw [smul_mulVec, (hX.2.1 a).2, smul_zero]⟩,
    by rw [smul_mulVec, hX.2.2, smul_zero]⟩

def sN (k r : ℕ) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InN k r X}
  zero_mem' := ⟨lie_zero _, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun a i h => by
    rw [Matrix.add_apply, hX.2.1 a i h, hY.2.1 a i h, add_zero], fun i j h1 h2 h3 => by
    rw [Matrix.add_apply, hX.2.2 i j h1 h2 h3, hY.2.2 i j h1 h2 h3, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun a i h => by
    rw [Matrix.smul_apply, hX.2.1 a i h, smul_zero], fun i j h1 h2 h3 => by
    rw [Matrix.smul_apply, hX.2.2 i j h1 h2 h3, smul_zero]⟩

def sQ (k r : ℕ) (Γ : Mat (2 * r + k + 1)) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InQ k r Γ X}
  zero_mem' := ⟨lie_zero _, fun _ _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun i j h => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX.2 i j h, hY.2 i j h, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun i j h => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX.2 i j h, smul_zero]⟩

theorem psiGen_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) :
    PI.BesselMapUniq.psiGen k r z c 1 = 1 := by
  have h : ∀ a, PI.BesselMapUniq.ellA k r z 1 a = 0 := by
    intro a
    unfold PI.BesselMapUniq.ellA
    split_ifs with h
    · refine Matrix.one_apply_ne fun e => ?_
      have := congrArg Fin.val e
      simp [eI] at this
    · rw [one_mulVec]
      exact hz _ (Or.inl a.2)
  simp [PI.BesselMapUniq.psiGen, h]

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (PI.BesselMapUniq.psiGen k r z c) := by
  have h : ∀ a, Continuous fun g => PI.BesselMapUniq.ellA k r z g a := by
    intro a
    unfold PI.BesselMapUniq.ellA
    split_ifs with h
    · exact continuous_id.matrix_elem _ _
    · exact (continuous_apply (eI k r a)).comp
        ((continuous_id (X := Mat (2 * r + k + 1))).matrix_mulVec (continuous_const (y := z)))
  unfold PI.BesselMapUniq.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul (h a)))))

theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat (2 * r + k + 1)) :
    ‖PI.BesselMapUniq.psiGen k r z c g‖ = 1 := by
  unfold PI.BesselMapUniq.psiGen
  exact Complex.norm_exp_I_mul_ofReal _

theorem one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat (2 * r + k + 1)) ∈ UWset k r z :=
  ⟨by simp [UH], fun _ => ⟨one_mulVec _, one_mulVec _⟩, one_mulVec _⟩

theorem bounded_of (hQB : QBound) (hAB : AbsBound) (hAd : AdaptExists) (hDec : Decomp) (hTB : TorBound)
    (hSp : SpanG) (hEx : ExpMem) (hRV : RootVec) : Bounded := by
  intro k r H _ _ _ σ hU hk z c hz hT hc V _ _ _ π hπ1 hπi hπc B hB heq w hw
  obtain ⟨Γ, hΓ⟩ := (hAd k r hk).2 z hz hT
  obtain ⟨d₁, X₁, hX₁, sp₁⟩ := spanFam (sUw k r z)
  obtain ⟨d₂, X₂, hX₂, sp₂⟩ := spanFam (sN k r)
  obtain ⟨e, Q, hQ, sp₃⟩ := spanFam (sQ k r Γ)
  have hX : ∀ j, InUw k r z (Fin.append X₁ X₂ j) ∨ InN k r (Fin.append X₁ X₂ j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact Or.inl (hX₁ i)
    · rw [Fin.append_right]; exact Or.inr (hX₂ i)
  have hspan : Spans (Hpk k r) (Fin.append X₁ X₂) Q := by
    intro Y hY
    obtain ⟨Y₁, Y₂, Y₃, h1, h2, h3, rfl⟩ := hSp k r z Γ hk hΓ Y hY
    obtain ⟨a₁, e₁⟩ := sp₁ Y₁ h1
    obtain ⟨a₂, e₂⟩ := sp₂ Y₂ h2
    obtain ⟨b, e₃⟩ := sp₃ Y₃ h3
    refine ⟨Fin.append a₁ a₂, b, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← e₁, ← e₂, ← e₃]
  have hχ : ∀ j, ∃ χ : ℝ → (V →L[ℂ] V), Continuous χ ∧ χ 0 = 1 ∧
      ∀ t v, IsSm (UH (Hpk k r)) σ v → B (σ (ex (Fin.append X₁ X₂ j) t) v) = χ t (B v) := by
    intro j
    rcases hX j with h | h
    · have hm := fun t => (hEx k r z _ t).1 h
      refine ⟨fun t => π (ex (Fin.append X₁ X₂ j) t), hπc.comp_continuous (continuous_ex _) hm, ?_, fun t v hv => ?_⟩
      · simp only [ex_zero, hπ1]
      · have := heq _ (hm t) 1 WeylGroupFacts.mem_n_one v hv
        rwa [Matrix.mul_one, psiGen_one hz, one_smul] at this
    · have hm := fun t => (hEx k r z _ t).2 h
      refine ⟨fun t => PI.BesselMapUniq.psiGen k r z c (ex (Fin.append X₁ X₂ j) t) • (1 : V →L[ℂ] V),
        ((psiGen_cont z c).comp (continuous_ex _)).smul continuous_const, ?_, fun t v hv => ?_⟩
      · simp only [ex_zero, psiGen_one hz, one_smul]
      · have := heq 1 (one_uw z) _ (hm t) v hv
        rw [Matrix.one_mul, hπ1] at this
        exact this
  choose χ hχc hχ0 hχe using hχ
  have hXL : ∀ j, Lie (Hpk k r) (Fin.append X₁ X₂ j) := fun j => (hX j).elim (fun h => h.1) fun h => h.1
  have hQL : ∀ i, Lie (Hpk k r) (Q i) := fun i => (hQ i).1
  obtain ⟨C, m, hC, hQ'⟩ := hQB _ _ H σ hU V B hB _ e _ Q hXL hQL hspan χ hχc hχ0 hχe
  obtain ⟨C₁, hC₁⟩ := hRV k r z Γ c hk hΓ hc
  set C₂ : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ∑ i, ‖Γ⁻¹ * Q i * Γ‖ with hC₂
  obtain ⟨K, hK⟩ := hAB _ _ H σ hU V B hB e Q hQL C m hC hQ' (max C₁ C₂) (2 * r + k + 1) w hw
  refine ⟨K, fun g hg => ?_⟩
  obtain ⟨h, hh, m', hm', d, R, hd, hR, hg', rfl⟩ := hDec k r z Γ hk hz hΓ g hg
  set g' := Γ * dg d * R with hg'def
  have hsm : IsSm (UH (Hpk k r)) σ (σ g' w) := hw.apply hU.rep hg'
  rw [hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hm'.1) hg', heq h hh m' hm' _ hsm, norm_smul, norm_psiGen, one_mul,
    hπi h hh]
  have hconj : ∀ M : ℝ, 1 ≤ M → (∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) →
      ∀ i, ‖g'⁻¹ * Q i * g'‖ ≤ max C₁ C₂ * M ^ (2 * r + k + 1) := by
    intro M hM hr i
    have e1 : g'⁻¹ * Q i * g' = (dg d * R)⁻¹ * (Γ⁻¹ * Q i * Γ) * (dg d * R) := by
      rw [hg'def, Matrix.mul_assoc Γ, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    rw [e1]
    refine (hTB k r d R _ M hk hd hR hM hr (hQ i).2).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    refine le_trans ?_ (le_max_right _ _)
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => ‖Γ⁻¹ * Q i * Γ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
      (by positivity)
  by_cases hall : ∀ a : Fin r, d (eI k r a) / d (nxt k r a) ≤ 1
  · refine hK g' hg' 1 le_rfl (hconj 1 le_rfl fun a => ?_) (Or.inl rfl)
    exact (div_le_iff₀ (hd.1 _)).1 (hall a)
  · push Not at hall
    obtain ⟨a₁, ha₁⟩ := hall
    obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ (fun a : Fin r => d (eI k r a) / d (nxt k r a))
      ⟨a₁, Finset.mem_univ _⟩
    have hM : 1 ≤ d (eI k r a₀) / d (nxt k r a₀) := ha₁.le.trans (ha₀ a₁ (Finset.mem_univ _))
    obtain ⟨Y, hY, hYn, hYe⟩ := hC₁ a₀ d R hd hR hg'
    refine hK g' hg' _ hM (hconj _ hM fun a => (div_le_iff₀ (hd.1 _)).1 (ha₀ a (Finset.mem_univ _)))
      (Or.inr ⟨Y, d (eI k r a₀) / d (nxt k r a₀), hY, hYn.trans (le_max_left _ _), le_abs_self _, fun τ u hu => ?_⟩)
    obtain ⟨hN, hψ⟩ := hYe τ
    have hinv : g'⁻¹ * g' = 1 := mul_eq_one_comm.1 (hU.grp.2.2.2 g' hg').2
    have e2 : g' * ex Y τ = 1 * (g' * ex Y τ * g'⁻¹) * g' := by
      rw [Matrix.one_mul, Matrix.mul_assoc (g' * ex Y τ), hinv, Matrix.mul_one]
    rw [e2, hU.rep.apply_mul (hU.rep.mul_mem _ hU.rep.one_mem _ hN.1) hg',
      heq 1 (one_uw z) _ hN _ (hu.apply hU.rep hg'), hπ1, hψ]
    rfl

end CompanionTheory.Bmu
end
end

