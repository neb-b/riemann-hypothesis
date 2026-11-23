module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0222
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0243

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

def sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (by intro a b c; simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum, mul_div_assoc])
    (by intro a b c; simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c), ← Finset.mul_sum,
        mul_div_assoc])

theorem isHerm_sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : IsHerm (sesqOf D T N N') := by
  intro x y
  change Hf D T y x = starRingEnd ℂ (Hf D T x y)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem lam_mul_mem (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem klat_gen {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    ∃ S : Set (Matrix (Fin N') (Fin N) D.host.E), Submodule.span D.host.K S = ⊤ ∧
      A = AddSubgroup.closure {z | ∃ w ∈ lamOf D cc δ, ∃ B ∈ S, z = w • embV D (tor0 D cc δ) B} := by
  rcases hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩
  · refine ⟨Set.range b, hb.2, ?_⟩
    unfold LaB
    congr 1
    ext z
    simp [tor0]
  · refine ⟨YYl D L L', ?_, rfl⟩
    obtain ⟨r, y, y', hy, -, h⟩ := GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
    rw [eq_top_iff]
    intro x _
    rw [h x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hy i))

theorem klat_smul_mem {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) (a : 𝓞 D.host.K)
    {x : VC D N N'} (hx : x ∈ A) : D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ A := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, lam_mul_mem a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem embV_smul (h : GL3Theta.InducedCMType D) (k : D.host.K) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (k • B) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) B := by
  funext τ i j
  change embT D τ ((k : D.host.E) * B i j) = D.host.φ₀ (k : D.host.E) * embT D τ (B i j)
  rw [map_mul, h τ k]

theorem embV_add (B B' : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (B + B') = embV D (tor0 D cc δ) B + embV D (tor0 D cc δ) B' := by
  funext τ i j
  exact map_add (embT D τ) _ _

theorem embV_zero : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  exact map_zero (embT D τ)

theorem klat_rat (h : GL3Theta.InducedCMType D) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A)
    {x : VC D N N'} (hx : x ∈ A) : ∃ B, x = δ • embV D (tor0 D cc δ) B := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  have hl : ∀ w ∈ lamOf D cc δ, ∃ k : D.host.K, w = δ * D.host.φ₀ (k : D.host.E) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw => obtain ⟨c, -, rfl⟩ := hw; exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨k, rfl⟩ := ha
      obtain ⟨k', rfl⟩ := hb
      exact ⟨k + k', by simp [mul_add]⟩
    | neg a _ ha =>
      obtain ⟨k, rfl⟩ := ha
      exact ⟨-k, by simp⟩
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, -, rfl⟩ := hw
    obtain ⟨k, rfl⟩ := hl w hw
    exact ⟨k • B, by rw [embV_smul h, smul_smul]⟩
  | zero => exact ⟨0, by rw [embV_zero, smul_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨B', rfl⟩ := hb
    exact ⟨B + B', by rw [embV_add, smul_add]⟩
  | neg a _ ha =>
    obtain ⟨B, rfl⟩ := ha
    exact ⟨(-1 : D.host.K) • B, by rw [embV_smul h]; simp⟩

theorem klat_mul_mem (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A : AddSubgroup (VC D N N')}
    (hA : KLat D (tor0 D cc δ) A) (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ m • (δ • embV D (tor0 D cc δ) B) ∈ A := by
  have hA' := hA
  obtain ⟨S, hS, hAS⟩ := klat_gen hA'
  have hB : B ∈ Submodule.span D.host.K S := hS ▸ Submodule.mem_top
  induction hB using Submodule.span_induction with
  | mem B hB =>
    refine ⟨Ideal.absNorm cc, Nat.pos_of_ne_zero (fun e => hcc (Ideal.absNorm_eq_zero_iff.1 e)), ?_⟩
    rw [hAS]
    refine AddSubgroup.subset_closure ⟨(Ideal.absNorm cc : ℂ) * δ,
      AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp [mul_comm]⟩, B, hB, ?_⟩
    rw [← smul_smul, Nat.cast_smul_eq_nsmul]
  | zero => exact ⟨1, one_pos, by simp [embV_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, ha⟩ := ha
    obtain ⟨n, hn, hb⟩ := hb
    refine ⟨m * n, by positivity, ?_⟩
    rw [embV_add, smul_add, smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.nsmul_mem ha _
    · rw [mul_smul]; exact A.nsmul_mem hb _
  | smul k B _ hB =>
    obtain ⟨m, hm, hB⟩ := hB
    obtain ⟨n, hn, hk⟩ := exists_integral_multiples ℤ ℚ ({k} : Finset D.host.K)
    have hk' : IsIntegral ℤ (n.natAbs • k) := by
      have := hk k (Finset.mem_singleton_self k)
      rcases Int.natAbs_eq n with e | e
      · rw [e] at this; simpa using this
      · rw [e] at this; simpa using this.neg
    refine ⟨m * n.natAbs, Nat.mul_pos hm (Int.natAbs_pos.2 hn), ?_⟩
    convert klat_smul_mem hA ⟨_, hk'⟩ hB using 1
    rw [embV_smul h]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    change _ = D.host.φ₀ ((n.natAbs • k : D.host.K) : D.host.E) * _
    simp
    ring

theorem klat_finite (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A₁ A₂ : AddSubgroup (VC D N N')}
    (h₁ : KLat D (tor0 D cc δ) A₁) (h₂ : KLat D (tor0 D cc δ) A₂) (hfg : A₂.FG) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) :=
  finite_quot hfg fun x hx => by
    obtain ⟨B, rfl⟩ := klat_rat h h₂ hx
    exact klat_mul_mem h hcc h₁ B

theorem klat_facts (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ IsSelfDual (sesqOf D (tor0 D cc δ) N N') A ∧
      IsSemiChar (sesqOf D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h3, h4, le_antisymm h2 h1, ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine isSemiChar_round (isHerm_sesqOf D _ N N') (Real.sqrt D.host.d) h1 (fun x hx => ?_) h5
  have := klat_smul_mem hA a hx
  rwa [ha] at this

end GlobalTheory.ThetaInter


open GlobalTheory.ThetaInter in
theorem GlobalTheory.theta_translation_intertwiner_unitary : ∀ D : D7, IntertwinerUnitary D := by
  intro D cc δ hc N N' A₁ A₂ h₁ h₂ th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  obtain ⟨f₂, s₂, d₂, c₂⟩ := klat_facts hc h₂
  have hH := isHerm_sesqOf D (tor0 D cc δ) N N'
  have hψ := (GlobalTheory.InducedType.induced_type D).1.1
  have := klat_finite hψ hc.1.1 h₁ h₂ f₂
  have := klat_finite hψ hc.1.1 h₂ h₁ f₁
  have : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have t₂ := discrete_of_selfDual hH d₂ f₂
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A₁ := hth.2
  exact ⟨fun x => mean_opU MeasureTheory.volume hH t₁ s₁ c₁ hth.1.continuous hF x,
    ⟨differentiable_inter (H := sesqOf D (tor0 D cc δ) N N') (α := al D (tor0 D cc δ)) A₁ A₂ hth.1,
      inter_mem_fixedBy hH c₁ d₂ c₂ hF⟩,
    mean_inter MeasureTheory.volume hH t₁ s₁ t₂ s₂ d₁ c₁ d₂ c₂ hth.1 hF,
    inter_inter hH d₁ d₂ c₁ hF⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionMapCarriesTorusLattices
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_coords_of_mem_LaB (D : D7) (T : Tor D) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : VC D N N') (hy : y ∈ LaB D T b) :
    ∃ w : Fin r → ℂ, (∀ j, w j ∈ T.abelian₂) ∧ y = ∑ j, w j • embV D T (b j) := by
  unfold LaB at hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, i, rfl⟩ := hz
    refine ⟨Pi.single i w, fun j => ?_, ?_⟩
    · by_cases h : j = i
      · subst h; simpa using hw
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨w, hw, rfl⟩ := hy
    obtain ⟨w', hw', rfl⟩ := hz
    refine ⟨w + w', fun j => add_mem (hw j) (hw' j), ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    refine ⟨fun j => -w j, fun j => neg_mem (hw j), ?_⟩
    simp only [neg_smul, Finset.sum_neg_distrib]

theorem adpB_lattices : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → (∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ n : ℕ, 0 < n → (∀ x x' y y', AdpB D (tor0 D cc δ) M ρ b n x x' → AdpB D (tor0 D cc δ) M ρ b n y y' → AdpB D (tor0 D cc δ) M ρ b n (x - y) (x' - y')) ∧ (∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → ∃ t', AdpB D (tor0 D cc δ) M ρ b n t t') ∧ ∀ (k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D (tor0 D cc δ) Y, ∃ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ (∀ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, ∃ x ∈ LaS D (tor0 D cc δ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ ∀ x x', AdpB D (tor0 D cc δ) M ρ b n x x' → (x ∈ LaS D (tor0 D cc δ) Y ↔ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y) := by
  intro D hG hS cc δ hc M ρ hK hD hM N N' r b hb n hn
  obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := hS cc δ hc M ρ hK hD.2.1 hD.2.2
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hneg : ∀ t t', StarPt M ρ (lamOf D cc δ) t t' → StarPt M ρ (lamOf D cc δ) (-t) (-t') := by
    intro t t' h
    have := h5 (-1) t t' h
    simpa using this
  have hsub : ∀ t t' u u', StarPt M ρ (lamOf D cc δ) t t' → StarPt M ρ (lamOf D cc δ) u u' →
      StarPt M ρ (lamOf D cc δ) (t - u) (t' - u') := by
    intro t t' u u' h h'
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact h4 _ _ _ _ h (hneg _ _ h')
  have hone : ∀ t t', StarPt M ρ (lamOf D cc δ) t t' →
      (t ∈ lamOf D cc δ ↔ t' ∈ lamConj M ρ (lamOf D cc δ)) := by
    intro t t' h
    simpa using h6 1 t t' h
  have hex : ∀ t, InRationalLattice (lamOf D cc δ) t → ∃ t', StarPt M ρ (lamOf D cc δ) t t' := by
    intro t hq
    refine h1 _ hq ?_
    by_cases h : t ∈ lamOf D cc δ
    · exact Or.inl h
    · exact Or.inr (hM _ hq h)
  have hex' : ∀ t', InRationalLattice (lamConj M ρ (lamOf D cc δ)) t' → ∃ t, StarPt M ρ (lamOf D cc δ) t t' := by
    rintro t' ⟨m, hm, ht'⟩
    obtain ⟨t, -, ht⟩ := h7 m hm (fun t h h' => hM t ⟨m, hm, h⟩ h') t' ht'
    exact ⟨t, ht⟩
  have hst : ∀ a : 𝓞 D.host.K, ∀ w ∈ lamOf D cc δ,
      D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
    intro a w hw
    have := h5 a w 0 (Or.inl ⟨hw, zero_mem _⟩)
    rw [hone _ _ this, mul_zero]; exact zero_mem _
  have hst' : ∀ a : 𝓞 D.host.K, ∀ w ∈ lamConj M ρ (lamOf D cc δ),
      D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamConj M ρ (lamOf D cc δ) := by
    intro a w hw
    have := h5 a 0 w (Or.inl ⟨zero_mem _, hw⟩)
    rw [← hone _ _ this, mul_zero]; exact zero_mem _
  have hT := isTraceCompatibleTorusEmbedding_standardTorus D hG cc δ
  have hT' := good_torConj D hG cc δ M ρ hK hD
  refine ⟨?_, ?_, ?_⟩
  · rintro _ _ _ _ ⟨c, c', hc, rfl, rfl, hcc⟩ ⟨d, d', hd, rfl, rfl, hdd⟩
    refine ⟨c - d, c' - d', fun j => ?_, ?_, ?_, fun j => ?_⟩
    · obtain ⟨m, hm, h⟩ := hc j
      obtain ⟨m', hm', h'⟩ := hd j
      refine ⟨m * m', Nat.mul_pos hm hm', ?_⟩
      have : ((m * m' : ℕ) : ℂ) * (c - d) j = m' • ((m : ℂ) * c j) - m • ((m' : ℂ) * d j) := by
        simp only [nsmul_eq_mul, Pi.sub_apply]; push_cast; ring
      rw [this]
      exact sub_mem (AddSubgroup.nsmul_mem _ h _) (AddSubgroup.nsmul_mem _ h' _)
    · simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    · simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    · show StarPt M ρ (lamOf D cc δ) ((c j - d j) / n) ((c' j - d' j) / n)
      rw [sub_div, sub_div]
      exact hsub _ _ _ _ (hcc j) (hdd j)
  · intro x m hm hmx
    obtain ⟨w, hw, hsum⟩ := exists_coords_of_mem_LaB D _ b _ hmx
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hq : ∀ j, ∃ t', StarPt M ρ (lamOf D cc δ) (w j / m / n) t' := by
      intro j
      refine hex _ ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      have : ((m * n : ℕ) : ℂ) * (w j / m / n) = w j := by push_cast; field_simp
      rw [this]; exact hw j
    choose t' ht' using hq
    refine ⟨_, fun j => w j / m, fun j => (n : ℂ) * t' j, ?_, ?_, rfl, ?_⟩
    · intro j
      refine ⟨m, hm, ?_⟩
      have : (m : ℂ) * (w j / m) = w j := by field_simp
      rw [this]; exact hw j
    · have hx : x = (m : ℂ)⁻¹ • (m • x) := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
      rw [hx, hsum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← div_eq_inv_mul]
    · intro j
      have : (n : ℂ) * t' j / n = t' j := by field_simp
      show StarPt M ρ (lamOf D cc δ) (w j / m / n) ((n : ℂ) * t' j / n)
      rw [this]; exact ht' j
  · intro k Y hk hkn hY
    obtain ⟨A1, A2⟩ := _root_.GlobalTheory.ThetaConj.corr_lattice D (tor0 D cc δ) (torConj D (tor0 D cc δ) M ρ) hT hT' hst N N' r b hb.1
      (StarPt M ρ (lamOf D cc δ)) hex (fun t t₁ t₂ h h' => (h2 t t₁ t₂ h).1 h') h4 h5
      (fun m t t' h => (h6 m t t' h).1) n k Y hn hk hkn hY
    obtain ⟨B1, B2⟩ := _root_.GlobalTheory.ThetaConj.corr_lattice D (torConj D (tor0 D cc δ) M ρ) (tor0 D cc δ) hT' hT hst' N N' r b hb.1
      (fun t' t => StarPt M ρ (lamOf D cc δ) t t') hex'
      (fun t t₁ t₂ h h' => (hone _ _ (hsub _ _ _ _ h h')).2 (by rw [sub_self]; exact zero_mem _))
      (fun t t' u u' h h' => h4 _ _ _ _ h h') (fun a t t' h => h5 a _ _ h)
      (fun m t t' h => (h6 m _ _ h).2) n k Y hn hk hkn hY
    refine ⟨fun x hx => ?_, fun x' hx' => ?_, ?_⟩
    · obtain ⟨c, c', hc, hxc, hcc, hmem⟩ := A1 x hx
      exact ⟨_, hmem, c, c', hc, hxc, rfl, hcc⟩
    · obtain ⟨c', c, hc', hxc, hcc, hmem⟩ := B1 x' hx'
      refine ⟨_, hmem, c, c', fun j => ?_, rfl, hxc, hcc⟩
      obtain ⟨m, hm, h⟩ := hc' j
      refine ⟨m, hm, ?_⟩
      have h' := (h6 (m * n) _ _ (hcc j)).2 (by
        have : ((m * n : ℕ) : ℂ) * (c' j / n) = m * c' j := by push_cast; field_simp
        rw [this]; exact h)
      have : ((m * n : ℕ) : ℂ) * (c j / n) = m * c j := by push_cast; field_simp
      rw [this] at h'; exact h'
    · rintro _ _ ⟨c, c', -, rfl, rfl, hcc⟩
      exact ⟨A2 c c' hcc, B2 c' c hcc⟩

end GlobalTheory.ThetaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTranslateMemThetaPullbackSpan
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TorsionTranslate

theorem ee_mem_Qbar (x : ℝ) (n : ℕ) (hn : 0 < n) (k : ℤ) (h₀ : (n : ℝ) * x = k) : ee x ∈ Qbar := by
  have h : (n : ℂ) * x = k := by exact_mod_cast h₀
  have h1 : ee x ^ n = 1 := by
    unfold ee
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k, ← h]
    congr 1
    ring
  refine (mem_algebraicClosure_iff).2 ?_
  refine IsAlgebraic.of_pow hn ?_
  rw [h1]
  exact isAlgebraic_one

theorem Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (m m' : ℕ) (x y : VC D N N') :
    Hf D T (m • x) (m' • y) = (m * m' : ℕ) * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left, Hf_conj D T (m' • y) x, ← Nat.cast_smul_eq_nsmul ℂ,
    Hf_smul_left, Hf_conj D T y x]
  simp [mul_assoc]

theorem translate_mem : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, ∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → U D (tor0 D cc δ) t F ∈ Tr D (tor0 D cc δ) b := by
  intro D cc δ hC N N' r b hb F hF t m hm ht
  have hint := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N'
    (LaB D (tor0 D cc δ) b) (Or.inl ⟨r, b, hb, rfl⟩)).2.2.1
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨s, ⟨m', hm', hs⟩, rfl⟩ := hG
    obtain ⟨k, hk⟩ := hint _ ht _ hs
    rw [Hf_nsmul] at hk
    have hk' : ((m * m' : ℕ) : ℝ) * (Hf D (tor0 D cc δ) t s).im = k := by
      rw [← hk]; simp
    have hq : ee (-(Hf D (tor0 D cc δ) t s).im / 2) ∈ Qbar := by
      refine ee_mem_Qbar _ (2 * (m * m')) (by positivity) (-k) ?_
      push_cast at hk' ⊢
      linear_combination -hk'
    have : U D (tor0 D cc δ) t (U D (tor0 D cc δ) s (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂))) =
        (⟨_, hq⟩ : Qbar) • U D (tor0 D cc δ) (t + s) (pullB D (tor0 D cc δ) b (sgStar (tor0 D cc δ).abelian₂)) := by
      funext z
      rw [U_U]
      rfl
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨t + s, ⟨m * m', by positivity, ?_⟩, rfl⟩)
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_nsmul]; exact AddSubgroup.nsmul_mem _ ht _
    · rw [mul_nsmul']; exact AddSubgroup.nsmul_mem _ hs _
  | zero =>
    have : U D (tor0 D cc δ) t (0 : VC D N N' → ℂ) = 0 := by
      funext z; simp [U]
    rw [this]; exact zero_mem _
  | add G G' _ _ h h' =>
    have : U D (tor0 D cc δ) t (G + G') = U D (tor0 D cc δ) t G + U D (tor0 D cc δ) t G' := by
      funext z; simp [U, add_mul]
    rw [this]; exact add_mem h h'
  | smul a G _ h =>
    have : U D (tor0 D cc δ) t (a • G) = a • U D (tor0 D cc δ) t G := by
      funext z
      change U D (tor0 D cc δ) t (fun z => (a : ℂ) * G z) z = (a : ℂ) * U D (tor0 D cc δ) t G z
      simp only [U]; ring
    rw [this]; exact Submodule.smul_mem _ _ h

end GlobalTheory.TorsionTranslate
end
end

