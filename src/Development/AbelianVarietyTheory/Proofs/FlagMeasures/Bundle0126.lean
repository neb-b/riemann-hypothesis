module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagLatticesNearUnderStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormIdealDivisibility
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairSplitTermNearReferenceBySkew
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormCongruenceLiftSmallGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairInnerLatticeIndicesAndGenerators
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormExistsConjNearReference
section
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.NormalPos

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem mem_smul_iff (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (y : V) :
    y ∈ s • Λ ↔ ∃ x ∈ Λ, s x = y := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  rfl

theorem smul_inf_eq (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (S : Submodule K V)
    (h : ∀ y ∈ S, s y = y) : (s • Λ) ⊓ rs (𝓞 K) S = Λ ⊓ rs (𝓞 K) S := by
  ext y
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_smul_iff]
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hy⟩
    have : x = y := s.injective (hxy.trans (h y hy).symm)
    exact ⟨this ▸ hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨y, hx, h y hy⟩, hy⟩

theorem line_le (A : Submodule (𝓞 K) K) (v : V) (S : Submodule K V) (hv : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t hv

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_mem_II (N : NF H r) (a : Fin r) (ha : N.j ≤ a.val) : N.F.e a.castSucc ∈ II N.F N.F' := by
  have hc : N.c ≠ 0 := by
    intro h
    have := N.c_norm
    rw [h, zero_mul] at this
    exact zero_ne_one this
  refine ⟨Submodule.subset_span ⟨a, a.2, rfl⟩, ?_⟩
  have h1 : N.F'.e a.castSucc ∈ N.F'.X := Submodule.subset_span ⟨a, a.2, rfl⟩
  have h2 := N.F'.X.smul_mem N.c⁻¹ h1
  rwa [N.same a.castSucc ha, smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem isotropicMeet_le_jointSpan (N : NF H r) : II N.F N.F' ≤ V0 N.F N.F' :=
  inf_le_left.trans (le_sup_left.trans le_sup_left)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem eq_zero_of_mem (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F')
    (d : V) (hd : d ∈ N.Ist) (hd' : d ∈ V0 N.F N.F') : d = 0 := by
  let φ : V →ₗ[K] V := ∑ a ∈ Finset.univ.filter (fun a : Fin r => N.j ≤ a.val),
    (H.B.flip (N.F.e a.castSucc)).smulRight (N.ist a)
  have h1 : N.Ist ≤ LinearMap.eqLocus φ LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, rfl⟩
    have hb' : N.j ≤ b.val := hb
    show φ (N.ist b) = N.ist b
    simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
    rw [Finset.sum_eq_single b]
    · rw [← H.herm, N.ist_e b b hb']; simp
    · intro a _ hab
      rw [← H.herm, N.ist_e a b hb']; simp [hab]
    · intro h; exact absurd (by simpa using hb') h
  have h2 : φ d = d := h1 hd
  rw [← h2]
  simp only [φ, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.flip_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  have ha' : N.j ≤ a.val := by simpa using ha
  have he := e_mem_II N a ha'
  rw [← H.herm, (hrad _ (isotropicMeet_le_jointSpan N he)).2 he d hd']
  simp

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem Xa_le_X (F : FlagD H r) (j : ℕ) : F.Xa j ≤ F.X :=
  Submodule.span_mono (Set.image_mono fun b _ => b.2)

theorem P0_inf_V0_le_sup_of_radical (N : NF H r)
    (hrad : ∀ v ∈ V0 N.F N.F', (∀ w ∈ V0 N.F N.F', H.B v w = 0) ↔ v ∈ II N.F N.F') :
    N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') ≤ (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z := by
  set Q := (N.P0 ⊓ rs (𝓞 K) (N.F.Xa N.j)) ⊔ (N.P0 ⊓ rs (𝓞 K) (N.F'.Xa N.j)) ⊔
      (N.P0 ⊓ rs (𝓞 K) (II N.F N.F')) ⊔ line 1 N.F.z with hQ
  have hQV : Q ≤ rs (𝓞 K) (V0 N.F N.F') := by
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F N.j).trans (le_sup_left.trans le_sup_left) : N.F.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx =>
        ((Xa_le_X N.F' N.j).trans (le_sup_right.trans le_sup_left) : N.F'.Xa N.j ≤ V0 N.F N.F') hx
    · exact inf_le_right.trans fun x hx => isotropicMeet_le_jointSpan N hx
    · exact line_le _ _ _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hP : N.P0 ≤ Q ⊔ rs (𝓞 K) N.Ist := by
    refine sup_le (le_sup_of_le_left (sup_le (sup_le ?_ ?_) le_sup_right)) (le_sup_of_le_right ?_)
    · refine iSup_le fun a => ?_
      have h0 : line (N.aa a) (N.F.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_iSup (fun a : Fin r => line (N.aa a) (N.F.e a.castSucc)) a)))
      by_cases ha : a.val < N.j
      · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
      · exact le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (e_mem_II N a (not_lt.1 ha)))))
    · refine iSup₂_le fun a ha => ?_
      have h0 : line (N.aa a) (N.F'.e a.castSucc) ≤ N.P0 :=
        le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_iSup₂ (f := fun (a : Fin r) (_ : a.val < N.j) => line (N.aa a) (N.F'.e a.castSucc)) a ha)))
      exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
          (le_inf h0 (line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)))))
    · exact iSup₂_le fun a ha => line_le _ _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  rintro p ⟨hp, hpV⟩
  obtain ⟨u, hu, d, hd, rfl⟩ := Submodule.mem_sup.1 (hP hp)
  have hdV : d ∈ V0 N.F N.F' := by
    have := (V0 N.F N.F').sub_mem hpV (hQV hu)
    rwa [add_sub_cancel_left] at this
  rw [eq_zero_of_mem N hrad d hd hdV, add_zero]
  exact hu

theorem fix_of_mem_Rs (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) : ∀ y ∈ N.Wt, s y = y :=
  fun y hy => (mem_fixingSubgroup_iff _).1 hs.2 y hy

theorem split_smul (N : NF H r) {s : V ≃ₗ[K] V} (hs : s ∈ N.Rs) {Λ : Submodule (𝓞 K) V}
    (hT : latTh N.F N.F' (s • Λ) = latTh N.F N.F' Λ) (h : N.Split Λ) : N.Split (s • Λ) := by
  unfold NF.Split at h ⊢
  rw [hT, smul_inf_eq s Λ _ (fix_of_mem_Rs N hs), h]

theorem near_mono (N : NF H r) {𝔞 𝔟 : Ideal (𝓞 K)} (h : 𝔞 ≤ 𝔟) {Λ : Submodule (𝓞 K) V}
    (hn : N.Near 𝔟 Λ) : N.Near 𝔞 Λ :=
  ⟨(Submodule.smul_mono_left h).trans hn.1, (Submodule.smul_mono_left h).trans hn.2⟩

end

theorem exists_near : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → N.Split Λ → ∃ s ∈ N.Rs, N.Split (s • Λ) ∧ N.Near (𝔠 ^ (12 * r + 50)) (s • Λ) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD hS
  have hrad := (GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).1.2.2.2.1
  obtain ⟨s₁, hs₁, -, h₁⟩ := _root_.GlobalTheory.DegCnt.PosJ.main K V H hK r N g Λ hg hΛ 𝔠 h0 hst hT hD
  obtain ⟨a₁, a₂, a₃, a₄⟩ := h₁ _ rfl
  obtain ⟨t₁, -, th₁, -⟩ := _root_.GlobalTheory.DegCnt.StabInv.main K V H hK r N g Λ hg hΛ s₁ hs₁.1
  have hS₁ := split_smul N hs₁ th₁ hS
  obtain ⟨s₂, hs₂, hfix, h₂⟩ := _root_.GlobalTheory.DegCnt.PosIso.normal_position K V H hK r N g _ hg t₁ 𝔠 h0 hst hT hD
  obtain ⟨b₁, b₂, b₃⟩ := h₂ _ rfl
  obtain ⟨t₂, -, th₂, -⟩ := _root_.GlobalTheory.DegCnt.StabInv.main K V H hK r N g _ hg t₁ s₂ hs₂.1
  have hS₂ := split_smul N hs₂ th₂ hS₁
  have e₁ := smul_inf_eq s₂ (s₁ • Λ) (N.F.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_left hy)
  have e₂ := smul_inf_eq s₂ (s₁ • Λ) (N.F'.Xa N.j) fun y hy => hfix y (Submodule.mem_sup_right hy)
  have key : 𝔠 ^ (2 * r + 2) • (N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F')) ≤ s₂ • s₁ • Λ := by
    refine (smul_mono_right _ (P0_inf_V0_le_sup_of_radical N hrad)).trans ?_
    rw [Submodule.smul_sup, Submodule.smul_sup, Submodule.smul_sup]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · refine le_trans ?_ (e₁.ge.trans inf_le_left)
      exact le_inf a₁ (Submodule.smul_le_right.trans inf_le_right)
    · refine le_trans ?_ (e₂.ge.trans inf_le_left)
      exact le_inf a₂ (Submodule.smul_le_right.trans inf_le_right)
    · exact (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))).trans b₁
    · exact (Submodule.smul_mono_left (Ideal.pow_le_self (by omega))).trans b₃
  obtain ⟨s₃, hs₃, hn⟩ := _root_.GlobalTheory.DegCnt.DualPos.near_of_skew K V H hK r N g _ hg t₂ 𝔠 h0 hst hT hD hS₂ (2 * r + 2) (by omega)
    key (by rw [e₁]; exact a₃) (by rw [e₂]; exact a₄) b₂
  have hs₃' : s₃ ∈ N.Rs := ⟨hs₃.1.1, hs₃.2⟩
  obtain ⟨-, -, th₃, -⟩ := _root_.GlobalTheory.DegCnt.StabInv.main K V H hK r N g _ hg t₂ s₃ hs₃'.1
  refine ⟨s₃ * (s₂ * s₁), N.Rs.mul_mem hs₃' (N.Rs.mul_mem hs₂ hs₁), ?_, ?_⟩
  · rw [mul_smul, mul_smul]
    exact split_smul N hs₃' th₃ hS₂
  · rw [mul_smul, mul_smul]
    exact near_mono N (Ideal.pow_le_pow_right (by omega)) hn

end GlobalTheory.DegCnt.NormalPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolTopLayerLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem inN_map_mem_of_le (F : FlagD H r) {g : V →ₗ[K] V} (hg : F.InN g) {S : Submodule K V} (hX : F.X ≤ S)
    (hz : F.z ∈ S) : (∀ x ∈ F.X, g x ∈ S) ∧ g F.z ∈ S := by
  have hXa : ∀ a : Fin r, F.Xa a ≤ F.X := fun a =>
    Submodule.span_mono (Set.image_mono fun b _ => b.isLt)
  have he : ∀ a : Fin r, F.e a.castSucc ∈ F.X := fun a => Submodule.subset_span ⟨a, a.isLt, rfl⟩
  constructor
  · have : F.X ≤ S.comap g := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, -, rfl⟩
      have := S.add_mem (hX (hXa a (hg.2.2.1 a))) (hX (he a))
      simpa using this
    exact fun x hx => this hx
  · have := S.add_mem (hX (hg.2.2.2 F.z F.zperp)) hz
    simpa using this

theorem unipotent_map_mem_V0 (F F' : FlagD H r) {g : V →ₗ[K] V} (hg : F.InN g) (hg' : F'.InN g) :
    ∀ x ∈ V0 F F', g x ∈ V0 F F' := by
  have h1 := inN_map_mem_of_le F hg (S := V0 F F') (le_sup_left.trans le_sup_left)
    (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have h2 := inN_map_mem_of_le F' hg' (S := V0 F F') (le_sup_right.trans le_sup_left)
    (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have : V0 F F' ≤ (V0 F F').comap g := by
    refine sup_le (sup_le h1.1 h2.1) (Submodule.span_le.2 ?_)
    rintro _ (rfl | rfl)
    · exact h1.2
    · exact h2.2
  exact fun x hx => this hx

end

theorem star_stable_pow {K : Type} [Field K] [StarRing K] (𝔠 : Ideal (𝓞 K))
    (h : ∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ 𝔠 ^ (n + 1), ∃ y ∈ 𝔠 ^ (n + 1), (y : K) = star (x : K) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', ea⟩ := ih a ha
      obtain ⟨b', hb', eb⟩ := h b hb
      refine ⟨a' * b', Ideal.mul_mem_mul ha' hb', ?_⟩
      show (a' : K) * (b' : K) = star ((a : K) * (b : K))
      rw [ea, eb, star_mul']
    · rintro a b ⟨a', ha', ea⟩ ⟨b', hb', eb⟩
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      show (a' : K) + (b' : K) = star ((a : K) + (b : K))
      rw [ea, eb, star_add]

theorem invVol_top_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊔ N.R1) (N.Gam Λ ⊔ N.R1) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 hc0 hcs hcT hcD e hsp hnear
  obtain ⟨hR, -⟩ := _root_.GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N
  obtain ⟨hNF, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨-, -, -, -, hlat, hint⟩ := _root_.GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hΛ
  set L := N.Ref (latL N.F N.F' Λ) with hL
  set M := N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') with hM
  have hMfg : M.FG := by
    rw [← hint]
    exact Submodule.FG.of_le hlat.fg inf_le_left
  have hstab : ∀ A : Subgroup (V ≃ₗ[K] V), (∀ s ∈ A, ∀ x ∈ M, s x ∈ M) →
      A ≤ MulAction.stabilizer (V ≃ₗ[K] V) M := by
    intro A hA s hs
    rw [MulAction.mem_stabilizer_iff]
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      exact hA s hs y hy
    · intro x hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ • x, hA _ (A.inv_mem hs) x hx, ?_⟩
      rw [smul_inv_smul]
  have hG : N.Gam L ⊔ N.R1 ≤ MulAction.stabilizer (V ≃ₗ[K] V) M := by
    refine sup_le (hstab _ ?_) (hstab _ ?_)
    · intro s hs x hx
      rw [← hint] at hx ⊢
      refine ⟨?_, unipotent_map_mem_V0 N.F N.F' ((hR s).1 hs.1).1 ((hR s).1 hs.1).2 x hx.2⟩
      have h1 : s • L = L := hs.2
      have h2 := Submodule.smul_mem_pointwise_smul x s L hx.1
      rw [h1] at h2
      exact h2
    · intro s hs x hx
      have h1 : s • x = x := (mem_fixingSubgroup_iff _).1 hs.2 x hx.2
      have h2 : s x = x := h1
      rw [h2]
      exact hx
  have hGR : N.Gam L ⊔ N.R1 ≤ N.R := sup_le inf_le_left inf_le_left
  have hle : 𝔠 ^ (3 * e + 11) ≤ Ideal.span {(N.T : 𝓞 K)} * 𝔠 ^ (3 * e + 10) := by
    rw [show 3 * e + 11 = (3 * e + 10) + 1 from rfl, pow_succ']
    exact Ideal.mul_mono_left fun x hx => Ideal.mem_span_singleton.2 (hcT x hx)
  obtain ⟨h0, hidx⟩ := _root_.GlobalTheory.CongIndex.relIndex_le K V (N.Gam L ⊔ N.R1) M (𝔠 ^ (3 * e + 11)) (N.Gam Λ ⊔ N.R1) hMfg
    (pow_ne_zero _ hc0) (fun s hs => hG hs) (by
      intro s hs hcong
      obtain ⟨s', hs', hV, hP⟩ := _root_.GlobalTheory.DegCnt.LiftS.lift_congruence K V H hK r N (𝔠 ^ (3 * e + 10))
        (star_stable_pow 𝔠 hcs (3 * e + 9)) s (hGR hs)
        (fun x hx => Submodule.smul_mono_left hle (hcong x hx))
      have hfix := _root_.GlobalTheory.DegCnt.stab_of_deep_congruence K V H hK r N g Λ hg hΛ 𝔠 hc0 hcs hcT hcD e hsp hnear s' hs' hP
      have h1 : s' ∈ N.Gam Λ := ⟨hs'.1, hfix⟩
      have h2 : s'⁻¹ * s ∈ N.R1 := by
        refine ⟨N.R.mul_mem (N.R.inv_mem hs'.1) (hGR hs), (mem_fixingSubgroup_iff _).2 fun y hy => ?_⟩
        have h3 : s • y = s' • y := (hV y hy).symm
        rw [mul_smul, h3, inv_smul_smul]
      have h4 := mul_mem (Subgroup.mem_sup_left h1 : s' ∈ N.Gam Λ ⊔ N.R1) (Subgroup.mem_sup_right h2)
      rwa [mul_inv_cancel_left] at h4)
  have hd : Module.finrank K (Submodule.span K (M : Set V)) ≤ 2 * r + 1 := by
    have h1 : Submodule.span K (M : Set V) ≤ V0 N.F N.F' := Submodule.span_le.2 fun x hx => hx.2
    have h2 := Submodule.finrank_mono h1
    have h3 := hNF.2.2.2.2.1
    have h4 := N.j_le
    omega
  have hn : 1 ≤ Ideal.absNorm 𝔠 := Nat.one_le_iff_ne_zero.2 (fun h => hc0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hfin : (N.Gam Λ ⊔ N.R1).relIndex (N.Gam L ⊔ N.R1) ≤
      Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
    refine hidx.trans ?_
    rw [map_pow, ← pow_mul]
    exact Nat.pow_le_pow_right hn (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 2))
  have hdiv : ∀ a b : ℕ, (a : ℝ) / (b : ℝ) ≤ a := by
    intro a b
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact div_le_self (Nat.cast_nonneg a) (by exact_mod_cast hb)
  unfold GlobalTheory.HL.invVol
  refine (hdiv _ _).trans ?_
  exact_mod_cast hfin

end GlobalTheory.DegCnt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairScalarEqQuotIdealsNormLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt

theorem mem_ipow_one_iff_exists {K : Type} [Field K] [NumberField K] (𝔞 : Ideal (𝓞 K)) (t : K) :
    t ∈ ipow 𝔞 1 ↔ ∃ a ∈ 𝔞, algebraMap (𝓞 K) K a = t := by
  unfold ipow
  rw [zpow_one]
  exact FractionalIdeal.mem_coeIdeal _

theorem exists_ideal_coeff {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L M : Submodule (𝓞 K) V) (z : V) (hML : M ≤ L)
    (hidx : idx L M ≠ 0) (hz : ∀ t : K, t • z ∈ L ↔ t ∈ (1 : Submodule (𝓞 K) K)) :
    ∃ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ Ideal.absNorm 𝔞 ≤ idx L M ∧ ∀ t : K, t ∈ ipow 𝔞 1 ↔ t • z ∈ M := by
  let f : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V z
  have hf : ∀ a : 𝓞 K, f a = (algebraMap (𝓞 K) K a) • z := fun a => by
    simp only [f, LinearMap.toSpanSingleton_apply, algebraMap_smul]
  let 𝔞 : Ideal (𝓞 K) := M.comap f
  have hr : f.toAddMonoidHom.range ≤ L.toAddSubgroup := by
    rintro _ ⟨a, rfl⟩
    show f a ∈ L
    rw [hf, hz]
    exact Submodule.mem_one.2 ⟨a, rfl⟩
  have hN : Ideal.absNorm 𝔞 = M.toAddSubgroup.relIndex f.toAddMonoidHom.range := by
    rw [← AddSubgroup.index_comap, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hle : Ideal.absNorm 𝔞 ≤ idx L M := by
    rw [hN]; exact AddSubgroup.relIndex_le_of_le_right hr hidx
  have hne : Ideal.absNorm 𝔞 ≠ 0 := by
    rw [hN]
    exact fun h => hidx (AddSubgroup.relIndex_eq_zero_of_le_right hr h)
  refine ⟨𝔞, fun h => hne (by rw [h, Ideal.absNorm_bot]), hle, fun t => ?_⟩
  rw [mem_ipow_one_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [← hf]; exact ha
  · intro ht
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ((hz t).1 (hML ht))
    refine ⟨a, ?_, rfl⟩
    show f a ∈ M
    rw [hf]; exact ht

theorem c_eq_quot_ideals : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, -, hz, hz', -⟩ := _root_.GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hΛ
  obtain ⟨hb, -, hD, h1⟩ := _root_.GlobalTheory.DegCnt.SplitIdx.main K V H hK r N g Λ hg hΛ
  obtain ⟨hi, hi', hle, -⟩ := _root_.GlobalTheory.DegCnt.InnerIndex.main K V H hK r N g Λ hg hΛ
  set i := idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) with hidef
  have hi0 : i ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hB : cardB N.F N.F' Λ ≠ 0 := by
    intro h; rw [h] at hi; simp at hi; linarith
  have hiD : (i : ℝ) ≤ N.Del := by
    have hB1 : (1 : ℝ) ≤ cardB N.F N.F' Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hB
    have hb1 : (1 : ℝ) ≤ N.bI Λ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
    have hb2 : (1 : ℝ) ≤ (N.bI Λ : ℝ) ^ 2 := one_le_pow₀ hb1
    have hi1 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    calc (i : ℝ) ≤ i * cardB N.F N.F' Λ := le_mul_of_one_le_right hi1 hB1
      _ = delBar N.F N.F' Λ := hi
      _ ≤ delBar N.F N.F' Λ * (N.bI Λ : ℝ) ^ 2 := le_mul_of_one_le_right (by linarith) hb2
      _ = N.Del := hD
  obtain ⟨𝔞, h0, hn, hm⟩ := exists_ideal_coeff _ _ N.F.z (hle.trans inf_le_left) hi0 hz
  obtain ⟨𝔞', h0', hn', hm'⟩ := exists_ideal_coeff _ _ N.F'.z (hle.trans inf_le_right) (hi' ▸ hi0) hz'
  refine ⟨𝔞, 𝔞', h0, h0', le_trans (by exact_mod_cast hn) hiD,
    le_trans (by exact_mod_cast hi' ▸ hn') hiD, fun t => ?_⟩
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) (by simpa using N.j_le)
  rw [hm, hm', hzz, mul_smul]

end GlobalTheory.DegCnt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUpperUnitriangularSuperdiagNeg
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory

theorem inv_upperUnitriangular (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k)
    (hlow : ∀ x y : Fin n, y < x → A x y = 0) (hdiag : ∀ x, A x x = 1) :
    (∀ x y : Fin n, y < x → A⁻¹ x y = 0) ∧ (∀ x, A⁻¹ x x = 1) ∧
      ∀ x y : Fin n, x.1 + 1 = y.1 → A⁻¹ x y = - A x y := by
  have hA : A.BlockTriangular id := fun i j h => hlow i j h
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hA]
    simp [hdiag]
  haveI : Invertible A := Matrix.invertibleOfIsUnitDet A (by rw [hdet]; exact isUnit_one)
  have hB : (A⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hA
  have hlowB : ∀ x y : Fin n, y < x → A⁻¹ x y = 0 := fun x y h => hB h
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (by rw [hdet]; exact isUnit_one)
  have hdiagB : ∀ x, A⁻¹ x x = 1 := by
    intro x
    have h := congrFun (congrFun hmul x) x
    rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single x] at h
    · simpa [hdiag] using h
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [hlow x j hj, zero_mul]
      · rw [hlowB j x hj, mul_zero]
    · simp
  refine ⟨hlowB, hdiagB, ?_⟩
  intro x y hxy
  have hxy' : x < y := by
    rw [Fin.lt_def]; omega
  have h := congrFun (congrFun hmul x) y
  rw [Matrix.mul_apply, Matrix.one_apply_ne (ne_of_lt hxy'),
    Finset.sum_eq_add (x) (y) (ne_of_lt hxy')] at h
  · rw [hdiag x, hdiagB y, one_mul, mul_one] at h
    exact eq_neg_of_add_eq_zero_left h
  · intro j _ hj
    rcases lt_trichotomy j x with h1 | h1 | h1
    · rw [hlow x j h1, zero_mul]
    · exact absurd h1 hj.1
    · have : y < j := by
        rcases lt_trichotomy j y with h2 | h2 | h2
        · exfalso; rw [Fin.lt_def] at h1 h2; omega
        · exact absurd h2 hj.2
        · exact h2
      rw [hlowB j y this, mul_zero]
  · simp
  · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicSpanOfLatticeIffForallPlace
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.mem_hat_iff_forall_loc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F L ↔ ∀ v : HeightOneSpectrum (𝓞 F), prVec v x ∈ loc v L := by
  intro F E _ _ _ _ _ n L hL x
  haveI := hL.1
  exact GlobalTheory.LatticeStabLocal.mem_latS_adele_iff L x
end

