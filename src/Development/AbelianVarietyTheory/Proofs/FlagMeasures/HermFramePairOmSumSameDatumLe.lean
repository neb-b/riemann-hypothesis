module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardUnimodularHermGluingsLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonUnipotentStabiliserPreservesTermsAndDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.OmCount

theorem encard_le_of_fibres {α β : Type*} (S : Set α) (A : Set β) (f : α → β) (c : ℝ≥0∞)
    (hA : ∀ x ∈ S, f x ∈ A)
    (hc : ∀ x ∈ S, ((({y | y ∈ S ∧ f y = f x} : Set α).encard : ℕ∞) : ℝ≥0∞) ≤ c) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ ((A.encard : ℕ∞) : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const,
    ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun x : S => (⟨f x, hA x x.2⟩ : A))]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [ENNReal.tsum_set_one]
  rcases Set.eq_empty_or_nonempty ((fun x : S => (⟨f x, hA x x.2⟩ : A)) ⁻¹' {a}) with h | ⟨x, hx⟩
  · rw [h]; simp
  · refine le_trans (ENat.toENNReal_le.2 ?_) (hc x x.2)
    refine Set.encard_le_encard_of_injOn (f := Subtype.val) ?_ Subtype.val_injective.injOn
    intro y hy
    refine ⟨y.2, ?_⟩
    have h1 : (⟨f y, hA y y.2⟩ : A) = a := hy
    have h2 : (⟨f x, hA x x.2⟩ : A) = a := hx
    exact congrArg Subtype.val (h1.trans h2.symm)

theorem tsum_orbits_le {G α : Type*} [Group G] [MulAction G α] (Q : α → Prop) (w : α → ℝ≥0∞) (S : Set α)
    (B : ℝ≥0∞) (h : ∀ x, Q x → w x ≤ B ∧ ∃ s : G, s • x ∈ S) :
    (∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0) ≤
      ((S.encard : ℕ∞) : ℝ≥0∞) * B := by
  set T : Set (MulAction.orbitRel.Quotient G α) := {o | Q o.out} with hT
  have h1 : (∑' o : MulAction.orbitRel.Quotient G α, if Q o.out then w o.out else 0) ≤ ∑' _ : T, B := by
    rw [tsum_subtype T (fun _ => B)]
    refine ENNReal.tsum_le_tsum fun o => ?_
    by_cases ho : Q o.out
    · rw [if_pos ho, Set.indicator_of_mem (show o ∈ T from ho)]
      exact (h _ ho).1
    · rw [if_neg ho]; exact zero_le
  refine h1.trans ?_
  rw [ENNReal.tsum_set_const]
  gcongr
  have h2 : T ⊆ (fun x : α => (Quotient.mk (MulAction.orbitRel G α) x)) '' S := by
    intro o ho
    obtain ⟨s, hs⟩ := (h _ ho).2
    refine ⟨_, hs, ?_⟩
    conv_rhs => rw [← Quotient.out_eq o]
    exact Quotient.sound ⟨s, rfl⟩
  exact (Set.encard_le_encard h2).trans (Set.encard_image_le _ _)

section

variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V]

theorem idx_dual_sup (H : HermSpace K V) (W I : Submodule K V) (A : Submodule R V) (hA : A ≤ rs R W)
    (hWI : W ⊓ I = ⊥) (h1 : ∀ x ∈ W ⊔ I, ∀ y ∈ I, H.B x y = 0) (h2 : ∀ x ∈ W ⊔ I, ∀ y ∈ I, H.B y x = 0)
    (hint : IsIntegralLat H A) :
    idx (dual H (A ⊔ rs R I)) (A ⊔ rs R I) = idx (dual H A) A := by
  have hsp : Submodule.span K (A : Set V) ≤ W := Submodule.span_le.2 hA
  have hdW : dual H A ≤ rs R W := fun y hy => hsp ((mem_dual_iff H A y).1 hy).1
  have hAd : A ≤ dual H A := fun y hy => (mem_dual_iff H A y).2
    ⟨Submodule.subset_span hy, fun x hx => (isIntegralLat_iff H A).1 hint y hy x hx⟩
  have hspan : Submodule.span K ((A ⊔ rs R I : Submodule R V) : Set V) = Submodule.span K (A : Set V) ⊔ I := by
    apply le_antisymm
    · rw [Submodule.span_le]
      have : A ⊔ rs R I ≤ rs R (Submodule.span K (A : Set V) ⊔ I) :=
        sup_le (fun x hx => Submodule.mem_sup_left (Submodule.subset_span hx))
          (fun x hx => Submodule.mem_sup_right hx)
      exact this
    · exact sup_le (Submodule.span_mono fun x hx => Submodule.mem_sup_left hx)
        (fun x hx => Submodule.subset_span (Submodule.mem_sup_right hx))
  have hd : dual H (A ⊔ rs R I) = dual H A ⊔ (A ⊔ rs R I) := by
    rw [← sup_assoc, sup_eq_left.2 hAd]
    apply le_antisymm
    · intro y hy
      obtain ⟨hy1, hy2⟩ := (mem_dual_iff H _ y).1 hy
      rw [hspan] at hy1
      obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hy1
      refine Submodule.add_mem_sup ((mem_dual_iff H A a).2 ⟨ha, fun x hx => ?_⟩) hi
      have := hy2 x (Submodule.mem_sup_left hx)
      rwa [map_add, LinearMap.add_apply, h2 x (Submodule.mem_sup_left (hA hx)) i hi, add_zero] at this
    · intro y hy
      obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hy
      obtain ⟨ha1, ha2⟩ := (mem_dual_iff H A a).1 ha
      refine (mem_dual_iff H _ _).2 ⟨?_, fun x hx => ?_⟩
      · rw [hspan]; exact Submodule.add_mem_sup ha1 hi
      · obtain ⟨a', ha', i', hi', rfl⟩ := Submodule.mem_sup.1 hx
        rw [map_add (f := _), h1 (a + i) (Submodule.add_mem_sup (hsp ha1) hi) i' hi', add_zero, map_add (f := _),
          LinearMap.add_apply, h2 a' (Submodule.mem_sup_left (hA ha')) i hi, add_zero]
        exact ha2 a' ha'
  have hinf : (A ⊔ rs R I) ⊓ dual H A = A := by
    rw [sup_inf_assoc_of_le _ hAd, sup_eq_left]
    intro x hx
    have : x ∈ W ⊓ I := ⟨hdW hx.2, hx.1⟩
    rw [hWI, Submodule.mem_bot] at this
    rw [this]; exact A.zero_mem
  unfold idx
  rw [hd, Submodule.sup_toAddSubgroup (dual H A), AddSubgroup.relIndex_sup_right,
    ← AddSubgroup.inf_relIndex_right]
  congr 1
  exact congrArg Submodule.toAddSubgroup hinf

end

theorem numeric (r k : ℕ) (i b c n Db Del NT x : ℝ) (hi : 0 < i) (hb : 0 ≤ b) (hn0 : 0 ≤ n) (hx0 : 0 ≤ x)
    (hDb : 1 ≤ Db) (hDel : 1 ≤ Del) (hNT : 1 ≤ NT) (hn : n ≤ (Db * NT) ^ 2) (hx : x ≤ (Del * NT) ^ 2) :
    i ^ ((k : ℝ) + c) * (n ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2) * x ^ (2 * r + 1) *
      (b ^ k * Del ^ r * n ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2)) ≤
    (i * b) ^ k * i ^ c * (Db * Del * NT) ^ (10000 * (r + 1) ^ 3) := by
  set M := Db * Del * NT with hM
  have hM1 : Db * NT ≤ M := by rw [hM]; nlinarith [mul_nonneg (sub_nonneg.2 hDel) (mul_nonneg (zero_le_one.trans hDb) (zero_le_one.trans hNT))]
  have hM2 : Del * NT ≤ M := by rw [hM]; nlinarith [mul_nonneg (sub_nonneg.2 hDb) (mul_nonneg (zero_le_one.trans hDel) (zero_le_one.trans hNT))]
  have hM3 : Del ≤ M := le_trans (le_mul_of_one_le_right (by linarith) hNT) hM2
  have hM4 : 1 ≤ M := hDel.trans hM3
  have hn' : n ≤ M ^ 2 := hn.trans (by gcongr)
  have hx' : x ≤ M ^ 2 := hx.trans (by gcongr)
  have hic : 0 ≤ i ^ c := by positivity
  calc _ = (i * b) ^ k * i ^ c * ((n ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2) * x ^ (2 * r + 1) *
      Del ^ r * n ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2)) := by
        rw [Real.rpow_add hi, Real.rpow_natCast, mul_pow]; ring
    _ ≤ (i * b) ^ k * i ^ c * (((M ^ 2) ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2) * (M ^ 2) ^ (2 * r + 1) *
      M ^ r * (M ^ 2) ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2)) := by
        have : 0 ≤ Del := by linarith
        gcongr
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simp only [← pow_mul, ← pow_add]
        refine pow_le_pow_right₀ hM4 ?_
        ring_nf
        nlinarith [Nat.zero_le r, Nat.zero_le (r ^ 2), Nat.zero_le (r ^ 3)]

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

theorem om_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {g : ℕ} {Λ : Submodule (𝓞 K) V} (hg : 1 ≤ g)
    (hΛ : N.IsTerm g Λ) {s : V ≃ₗ[K] V} (hs : s ∈ N.R) : N.om (s • Λ) = N.om Λ := by
  obtain ⟨-, hS, -, -⟩ := _root_.GlobalTheory.DegCnt.StabInv.main K V H hK r N g Λ hg hΛ s hs
  obtain ⟨-, -, -, -, hnil⟩ := _root_.GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N
  have hLat := ((isUnimod_iff H Λ).1 hΛ.1.1).1
  have hL : Submodule.IsFullLattice K Λ :=
    { Submodule.IsLattice.of_fg K hLat.1 with span_eq_top := hLat.2 }
  unfold NF.om NF.Gam
  rw [hS.1]
  let A := N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ
  let B := N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (s • Λ)
  let C := N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (N.Ref (latL N.F N.F' Λ))
  have hB : Submodule.IsFullLattice K (s • Λ) := Unimod.isLattice_smul s hL
  have hab : A.relIndex B ≠ 0 := Unimod.relIndex_ne_zero N.R hL hB
  have hba : B.relIndex A ≠ 0 := Unimod.relIndex_ne_zero N.R hB hL
  have hd : GlobalTheory.HL.invVol A B = 1 := by
    have h := (Unimod.invVol_smul K V N.R (2 * r + 1) hnil Λ Λ hL hL).2 s hs
    simpa [A, B, GlobalTheory.HL.invVol] using h
  change GlobalTheory.HL.invVol C B = GlobalTheory.HL.invVol C A
  by_cases hca : C.relIndex A = 0
  · have hcb : C.relIndex B = 0 := by
      by_contra h
      exact (Subgroup.relIndex_ne_zero_trans h hba) hca
    simp [GlobalTheory.HL.invVol, hca, hcb]
  · by_cases hac : A.relIndex C = 0
    · have hbc : B.relIndex C = 0 := by
        by_contra h
        exact (Subgroup.relIndex_ne_zero_trans hab h) hac
      simp [GlobalTheory.HL.invVol, hac, hbc]
    · have hcb : C.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hca hab
      have hbc : B.relIndex C ≠ 0 := Subgroup.relIndex_ne_zero_trans hba hac
      have h := (GlobalTheory.HL.invVol_mul_pos_le_conj C A B hca hac hcb hbc).1
      simpa [hd] using h

theorem isLatMod_latLa (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {g : ℕ} {Λ : Submodule (𝓞 K) V} (hg : 1 ≤ g)
    (hΛ : N.IsTerm g Λ) :
    IsLatMod (latLa N.F N.F' Λ (g : 𝓞 K)) (wSp N.F N.F') (II N.F N.F') := by
  obtain ⟨hTh, -, -, -, -, -, -, ⟨M, -, hM⟩, hsp⟩ := _root_.GlobalTheory.DegCnt.FixIdx.main K V H hK r N g Λ hg hΛ
  obtain ⟨⟨⟨⟨M', hM', hL⟩, -⟩, -⟩, -⟩ := _root_.GlobalTheory.DegCnt.InnerLat.main K V H hK r N g Λ hg hΛ
  have h0 : latLa N.F N.F' Λ (g : 𝓞 K) ≤ flagPairDefinitePartLattice N.F N.F' Λ := fun x hx => hx.1.2
  have hI : rs (𝓞 K) (II N.F N.F') ≤ latLa N.F N.F' Λ (g : 𝓞 K) := le_trans (by rw [hM]; exact le_sup_right) hTh
  refine ⟨⟨latLa N.F N.F' Λ (g : 𝓞 K) ⊓ M', ?_, ?_⟩, le_antisymm ?_ ?_⟩
  · haveI : IsNoetherian (𝓞 K) M' := isNoetherian_of_fg_of_noetherian _ hM'
    exact isNoetherian_submodule.1 this _ inf_le_right
  · rw [inf_sup_assoc_of_le _ hI, ← hL]
    exact (inf_eq_left.2 (h0.trans inf_le_left)).symm
  · exact Submodule.span_le.2 fun x hx => (h0 hx).2
  · rw [← hsp]; exact Submodule.span_mono hTh

theorem inf_Wt_of_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {Λ : Submodule (𝓞 K) V} (h : N.Split Λ) :
    Λ ⊓ rs (𝓞 K) N.Wt = latTh N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt := by
  obtain ⟨-, hlift, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  rw [h, sup_inf_assoc_of_le _ inf_le_right, eq_comm, sup_eq_left]
  intro x hx
  have : x ∈ N.Wt ⊓ II N.F N.F' := ⟨hx.2, hx.1⟩
  rw [hlift.2.1, Submodule.mem_bot] at this
  rw [this]; exact Submodule.zero_mem _

theorem idx_dual_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (N : NF H r) {g : ℕ} {Λ : Submodule (𝓞 K) V} (hg : 1 ≤ g)
    (hΛ : N.IsTerm g Λ) (h : N.Split Λ) :
    (idx (dual H (Λ ⊓ rs (𝓞 K) N.Wt)) (Λ ⊓ rs (𝓞 K) N.Wt) : ℝ) ≤ (N.Del * N.NT) ^ 2 := by
  obtain ⟨-, hlift, -, -, -, -, hw, -, hPD, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨-, -, -, -, hgi, -, hdel, hlat⟩ := _root_.GlobalTheory.DegCnt.FixIdx.main K V H hK r N g Λ hg hΛ
  have h1 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B x y = 0 := by
    intro x hx y hy
    rw [← hw] at hx
    exact (mem_perp_iff H _ x).1 hx y (Submodule.mem_sup_left (Submodule.mem_sup_left hy.1))
  have h2 : ∀ x ∈ N.Wt ⊔ II N.F N.F', ∀ y ∈ II N.F N.F', H.B y x = 0 := by
    intro x hx y hy
    rw [← H.herm, h1 x hx y hy, star_zero]
  have hintΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx y hy
    have hu : dual H Λ = Λ := hΛ.1.1.2
    rw [← hu] at hx
    exact ((mem_dual_iff H Λ x).1 hx).2 y hy
  have hintA : IsIntegralLat H (Λ ⊓ rs (𝓞 K) N.Wt) :=
    (isIntegralLat_iff H _).2 fun x hx y hy => hintΛ x hx.1 y hy.1
  have hintT : IsIntegralLat H (latTh N.F N.F' Λ) := by
    rw [h]
    refine (isIntegralLat_iff H _).2 fun x hx y hy => ?_
    obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a', ha', i', hi', rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add (f := _), h1 (a + i) (Submodule.add_mem_sup ha.2 hi) i' hi', add_zero, map_add (f := _),
      LinearMap.add_apply, h2 a' (Submodule.mem_sup_left ha'.2) i hi, add_zero]
    exact hintΛ a ha.1 a' ha'.1
  have hrad : ∀ x ∈ wSp N.F N.F', (∀ y ∈ wSp N.F N.F', H.B x y = 0) ↔ x ∈ II N.F N.F' := by
    rw [hw]
    intro x hx
    refine ⟨fun hx0 => ?_, fun hxI y hy => h2 y hy x hxI⟩
    obtain ⟨a, ha, i, hi, rfl⟩ := Submodule.mem_sup.1 hx
    have haa := hx0 a (Submodule.mem_sup_left ha)
    rw [map_add (f := _), LinearMap.add_apply, h2 a (Submodule.mem_sup_left ha) i hi, add_zero] at haa
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have ha0 : a = 0 := by
      by_contra hne
      have := hPD τ ⟨a, ha⟩ (fun h => hne (congrArg Subtype.val h))
      have e : GlobalTheory.Mass.hRes H.B.flip N.Wt ⟨a, ha⟩ ⟨a, ha⟩ = H.B a a := rfl
      rw [e, haa] at this
      simp at this
    rw [ha0, zero_add]; exact hi
  have hd := (DelScale.main K V H hK _ _ _ _ (by rw [hw]; exact le_sup_right) hrad hlat hlat).2.2.2 hintT
  rw [← idx_dual_sup H N.Wt (II N.F N.F') _ inf_le_right hlift.2.1 h1 h2 hintA, ← h, ← hd.2, hdel]
  have : 0 ≤ N.NT := by unfold NF.NT; positivity
  gcongr

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ i b : ℕ, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤ ENNReal.ofReal (((i : ℝ) * b) ^ Module.finrank K N.Wt * (i : ℝ) ^ cf K * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ i b
  obtain ⟨𝔠, hcn, hDb, hDel, hQ⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors K V H hK r N g Λ hg hΛ
  refine hQ _ fun c0 c1 c2 c3 => ?_
  obtain ⟨-, -, hcompl, hrk, -, -, -, -, -, hT, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  have hrkPi : Module.finrank K (perp H N.Wt) = 2 * r + 1 := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    unfold NF.Pi at this
    omega
  have hNT : 1 ≤ N.NT := one_le_pow₀ (by exact_mod_cast hT)
  set S : Set (Submodule (𝓞 K) V) := {Λ' | (N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ∧
    N.Split Λ' ∧ N.Near (𝔠 ^ (12 * r + 50)) Λ'} with hS
  set B : ℝ := (b : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r *
    (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * (12 * r + 50) + 11) * (2 * r + 1) ^ 2) with hB
  have hQs : ∀ Λ', (N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) → ∀ s ∈ N.R,
      (N.IsTerm g (s • Λ') ∧ N.SameDat g Λ (s • Λ') ∧ N.iI g (s • Λ') = i ∧ N.bI (s • Λ') = b) := by
    rintro Λ' ⟨h1, h2, h3, h4⟩ s hs
    obtain ⟨k1, k2, k3, k4⟩ := _root_.GlobalTheory.DegCnt.StabInv.main K V H hK r N g Λ' hg h1 s hs
    refine ⟨k1, ⟨k2.1.trans h2.1, k2.2.1.trans h2.2.1, k2.2.2.trans h2.2.2⟩, ?_, k4.trans h4⟩
    rw [← h3]
    unfold NF.iI latLa
    rw [k3, k2.2.2]
  have step1 : N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) ≤
      ((S.encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal B := by
    refine tsum_orbits_le (G := N.R)
      (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = i ∧ N.bI Λ' = b) (fun Λ' => ENNReal.ofReal (N.om Λ')) S _ ?_
    intro Λ' h
    obtain ⟨s, hs, hsp⟩ := _root_.GlobalTheory.DegCnt.SplitLift.main K V H hK r N g Λ' hg h.1
    have h' := hQs Λ' h s hs
    obtain ⟨t, ht, hsp', hnear⟩ := _root_.GlobalTheory.DegCnt.NormalPos.exists_near K V H hK r N g _ hg h'.1 𝔠 c0 c1 c2 c3 hsp
    have h'' := hQs _ h' t ht.1
    refine ⟨ENNReal.ofReal_le_ofReal ?_, ⟨t, ht.1⟩ * ⟨s, hs⟩, ?_⟩
    · rw [← om_smul hK N hg h.1 hs, ← om_smul hK N hg h'.1 ht.1, hB, ← h''.2.2.2]
      exact _root_.GlobalTheory.DegCnt.Weight.om_le K V H hK r N g _ hg h''.1 𝔠 c0 c1 c2 c3 _ hsp' hnear
    · rw [mul_smul]
      exact ⟨h'', hsp', hnear⟩
  refine step1.trans ?_
  rcases Set.eq_empty_or_nonempty S with hE | ⟨Λ₀, hΛ₀⟩
  · rw [hE]; simp
  have hi : 1 ≤ i := by
    rw [← hΛ₀.1.2.2.1]
    exact (_root_.GlobalTheory.DegCnt.FixIdx.main K V H hK r N g Λ₀ hg hΛ₀.1.1).2.2.1
  have hTh := _root_.GlobalTheory.DegCnt.count_sublattices_definite K V H hK r N _ i hi (isLatMod_latLa hK N hg hΛ)
  have hP := _root_.GlobalTheory.DegCnt.NearCount.main K V H hK r N (𝔠 ^ (12 * r + 50)) (pow_ne_zero _ c0)
  have step2 := encard_le_of_fibres S
    ({Th : Submodule (𝓞 K) V | rs (𝓞 K) (II N.F N.F') ≤ Th ∧ Th ≤ latLa N.F N.F' Λ (g : 𝓞 K) ∧
        idx (latLa N.F N.F' Λ (g : 𝓞 K)) Th = i} ×ˢ
      {P : Submodule (𝓞 K) V | 𝔠 ^ (12 * r + 50) • N.P0 ≤ P ∧ 𝔠 ^ (12 * r + 50) • P ≤ N.P0})
    (fun Λ' => (latTh N.F N.F' Λ', Λ' ⊓ rs (𝓞 K) N.Pi))
    (ENNReal.ofReal (((N.Del * N.NT) ^ 2) ^ (2 * r + 1))) ?_ ?_
  rotate_left
  · rintro Λ' ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    have e : latLa N.F N.F' Λ' (g : 𝓞 K) = latLa N.F N.F' Λ (g : 𝓞 K) := by
      unfold latLa; rw [h2.2.2]
    refine ⟨⟨?_, ?_, ?_⟩, h6⟩
    · show _ ≤ latTh N.F N.F' Λ'
      rw [h5]; exact le_sup_right
    · rw [← e]; exact (_root_.GlobalTheory.DegCnt.FixIdx.main K V H hK r N g Λ' hg h1).1
    · rw [← e]; exact h3
  · rintro Λ' ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    have hgl := _root_.GlobalTheory.DegCnt.Glue.encard_gluings_le K V H hK N.Wt (Λ' ⊓ rs (𝓞 K) N.Wt) (Λ' ⊓ rs (𝓞 K) N.Pi) _ hcompl rfl
    refine le_trans (ENat.toENNReal_le.2 (Set.encard_le_encard ?_)) (hgl.trans ?_)
    · rintro Λ'' ⟨⟨⟨k1, -⟩, k5, -⟩, k⟩
      refine ⟨k1.1.1, ?_, (Prod.ext_iff.1 k).2⟩
      rw [inf_Wt_of_split hK N k5, inf_Wt_of_split hK N h5]
      exact congrArg (· ⊓ rs (𝓞 K) N.Wt) (Prod.ext_iff.1 k).1
    · rw [hrkPi, ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast]
      gcongr
      exact idx_dual_le hK N hg h1 h5
  rw [Set.encard_prod, ENat.toENNReal_mul] at step2
  have hipos : (0 : ℝ) < i := by exact_mod_cast hi
  have hDel0 : 0 ≤ N.Del := by linarith
  have hP' : (Ideal.absNorm (𝔠 ^ (12 * r + 50)) : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) =
      ENNReal.ofReal (((Ideal.absNorm 𝔠 : ℝ) ^ (12 * r + 50)) ^ (2 * (2 * r + 1) ^ 2)) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, map_pow,
      Nat.cast_pow]
  rw [hP'] at hP
  refine le_trans (mul_le_mul_left (step2.trans (mul_le_mul_left (mul_le_mul' hTh hP) _)) _) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (numeric r _ i b (cf K) _ N.Db N.Del N.NT _ hipos (by positivity) (by positivity)
    (by positivity) hDb hDel hNT hcn le_rfl)

end GlobalTheory.DegCnt.OmCount
