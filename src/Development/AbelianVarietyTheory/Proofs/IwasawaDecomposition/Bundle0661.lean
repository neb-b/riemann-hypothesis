module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionBarycentreCellNextStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0009
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BarycentricSubdivisionStarStepCells
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section Helpers

variable {X : Type} [AddCommGroup X]

theorem inRCone_append_left {b a : ℕ} (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X)
    {β : LinearMap.BilinForm ℤ X} (h : InRCone v β) : InRCone (Fin.append v u) β :=
  inRCone_trans (fun k => by simpa using inRCone_self (Fin.append v u) (Fin.castAdd a k)) h

theorem inRCone_cons_of {n m : ℕ} (β₀ : LinearMap.BilinForm ℤ X) {F : Fin m → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (h : InRCone F β) : InRCone (Fin.cons β₀ F : Fin (m + 1) → _) β :=
  inRCone_trans (fun k => by simpa using inRCone_self (Fin.cons β₀ F : Fin (m + 1) → _) k.succ) h

theorem inRCone_cons_mono {n m : ℕ} (β₀ : LinearMap.BilinForm ℤ X) {F : Fin m → LinearMap.BilinForm ℤ X}
    {δ : Fin n → LinearMap.BilinForm ℤ X} (h : ∀ k, InRCone F (δ k)) :
    ∀ k, InRCone (Fin.cons β₀ F : Fin (m + 1) → _) ((Fin.cons β₀ δ : Fin (n + 1) → _) k) := by
  intro k
  refine Fin.cases ?_ (fun k => ?_) k
  · simpa using inRCone_self (Fin.cons β₀ F : Fin (m + 1) → _) 0
  · simpa using inRCone_cons_of (n := n) β₀ (h k)

theorem inRCone_comp_of {m m' : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} (s : Fin m' ↪ Fin m) {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) {β : LinearMap.BilinForm ℤ X} (hβ : toReal β = ∑ j, c j • toReal (G j))
    (h0 : ∀ j, j ∉ Set.range s → c j = 0) : InRCone (fun l => G (s l)) β := by
  refine ⟨fun l => c (s l), fun l => hc _, ?_⟩
  rw [hβ]
  symm
  exact Fintype.sum_of_injective s s.injective _ _ (fun j hj => by rw [h0 j hj, zero_smul]) fun l => rfl

theorem coeff_eq_zero_of_apply {m : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j)
    {β : LinearMap.BilinForm ℤ X} (hβ : toReal β = ∑ j, c j • toReal (G j)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hG : ∀ j, 0 ≤ h (G j)) (h0 : h β = 0) (j : Fin m) (hj : h (G j) ≠ 0) : c j = 0 := by
  have e := apply_eq_of_toReal_eq hβ h
  rw [h0, Int.cast_zero] at e
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ c j * (h (G j) : ℝ) := fun j _ => mul_nonneg (hc j) (by exact_mod_cast hG j)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 e.symm j (Finset.mem_univ _)
  exact (mul_eq_zero.1 this).resolve_right (by exact_mod_cast hj)

theorem exists_faceCut {m : ℕ} (G : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hG : ∀ j, 0 ≤ h (G j)) : ∃ (m' : ℕ) (s : Fin m' ↪ Fin m), IsFaceCut G s h := by
  classical
  let S := Finset.univ.filter fun j => h (G j) = 0
  refine ⟨S.card, (S.orderEmbOfFin rfl).toEmbedding, hG, fun j => ?_⟩
  have : Set.range (S.orderEmbOfFin rfl).toEmbedding = (S : Set (Fin m)) := by
    simp [Finset.range_orderEmbOfFin]
  rw [this]
  simp [S]

end Helpers

section Reduce

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem reduce_of_not_mem {m n : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {γ : Fin n → LinearMap.BilinForm ℤ X}
    (hG : IsCell bar φ G) (hγ : IsCell bar φ γ) (hcov : ∀ k, InRCone G (γ k)) {β₀ : LinearMap.BilinForm ℤ X}
    (hb : β₀ ∈ balForms bar X) (hp : ∀ y, 0 ≤ β₀ y y) (hin : InRCone G β₀) (hnin : ¬ InRCone γ β₀) :
    ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut G s h ∧ 0 < h β₀ ∧
      ∀ k, InRCone (fun l => G (s l)) (γ k) := by
  obtain ⟨h, hh1, hh2, hh3⟩ := _root_.GlobalTheory.PolFan.exists_cut_of_cell_le O bar φ X m n G γ hG hγ hcov
  obtain ⟨m', s, hs⟩ := exists_faceCut G h hh1
  refine ⟨m', s, h, hs, ?_, fun k => ?_⟩
  · rcases (hin.apply_nonneg h hh1).eq_or_lt with e | e
    · exact (hnin (hh3 β₀ hb hp hin e.symm)).elim
    · exact e
  · obtain ⟨c, hc, e⟩ := hcov k
    exact inRCone_comp_of s hc e fun j hj =>
      coeff_eq_zero_of_apply hc e h hh1 (hh2 k) j fun h0 => hj ((hs.2 j).1 h0)

theorem reduce_of_mem {m n n' : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} {δ : Fin n → LinearMap.BilinForm ℤ X}
    (hG : IsCell bar φ G) (hδ : IsCell bar φ δ) (hcov : ∀ k, InRCone G (δ k)) {β₀ : LinearMap.BilinForm ℤ X}
    (hin : InRCone δ β₀) {s : Fin n' ↪ Fin n} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hcut : IsFaceCut δ s h)
    (hpos : 0 < h β₀) :
    ∃ (m' : ℕ) (s' : Fin m' ↪ Fin m) (h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut G s' h' ∧ 0 < h' β₀ ∧
      ∀ k, InRCone (fun l => G (s' l)) (δ (s k)) := by
  obtain ⟨h₁, hh1, hh2, hh3⟩ := _root_.GlobalTheory.PolFan.exists_cut_of_cell_le O bar φ X m n G δ hG hδ hcov
  set K : ℤ := 1 + ∑ j, |h (G j)| with hK
  have hKj : ∀ j, |h (G j)| < K := fun j => by
    have := Finset.single_le_sum (f := fun j => |h (G j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  let h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := K • h₁ + h
  have hv : ∀ β, h' β = K * h₁ β + h β := fun β => rfl
  have hnn : ∀ j, 0 ≤ h' (G j) := fun j => by
    rw [hv]
    rcases (hh1 j).eq_or_lt with e | e
    · rw [← e, mul_zero, zero_add]
      exact (hh3 _ (hG.mem j) (hG.nonneg j) (inRCone_self G j) e.symm).apply_nonneg h hcut.1
    · have h1 : 1 ≤ h₁ (G j) := e
      have := hKj j
      have h2 : -K < h (G j) := by have := neg_abs_le (h (G j)); linarith
      have hK0 : 0 < K := lt_of_le_of_lt (abs_nonneg _) (hKj j)
      have h3 : K ≤ K * h₁ (G j) := le_mul_of_one_le_right hK0.le h1
      linarith
  obtain ⟨m', s', hs'⟩ := exists_faceCut G h' hnn
  have hz : ∀ β, InRCone δ β → h₁ β = 0 := fun β hβ => by
    obtain ⟨c, _, e⟩ := hβ
    have := apply_eq_of_toReal_eq e h₁
    simp only [hh2, Int.cast_zero, mul_zero, Finset.sum_const_zero] at this
    exact_mod_cast this
  refine ⟨m', s', h', hs', by rw [hv, hz β₀ hin, mul_zero, zero_add]; exact hpos, fun k => ?_⟩
  obtain ⟨c, hc, e⟩ := hcov (s k)
  have h0 : h' (δ (s k)) = 0 := by
    rw [hv, hz _ (inRCone_self δ _), mul_zero, zero_add]
    exact (hcut.2 _).2 ⟨k, rfl⟩
  exact inRCone_comp_of s' hc e fun j hj => coeff_eq_zero_of_apply hc e h' hnn h0 j fun h0 => hj ((hs'.2 j).1 h0)

end Reduce

theorem baryStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab φ : InvFun (𝓞 E)) (i : ℕ), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H lab → IsCarrierDim H.bar q ψ lab → IsTwInv H φ → IsBaryStage H.bar q ψ lab φ (i + 1) → ∃ φ' : InvFun (𝓞 E), IsTwInv H φ' ∧ IsBaryStage H.bar q ψ lab φ' i := by
  intro E _ _ _ H q ψ lab φ i hdom hψ hψt hlt hcar hφt hst
  obtain ⟨w, hwt, hw⟩ := _root_.GlobalTheory.PolFan.Mark.exists_markFun_props E H q ψ lab i hdom hψ hψt hlt hcar
  obtain ⟨hφp, hφs, hφc⟩ := hst
  have hcen : IsCentreSet H.bar q φ w := by
    intro X _ _ _ _ hX
    obtain ⟨h1, h2, h3, h4, -⟩ := hw X hX
    refine ⟨h1, h2, fun m γ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc' => ?_⟩
    obtain ⟨b, a, v, u, -, hv, hcov, -, -, hvl, hoff, -⟩ := hφc X hX m γ hγ
    have inv : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 → InRCone γ β → InRCone v β := by
      intro β hβ hp hw1 hc
      by_contra hn
      have := hoff β hβ hp (inRCone_trans hcov hc) hn
      rw [h3 β hβ hp hw1] at this
      exact lt_irrefl _ this
    exact h4 b v hv hvl β hβ hp β' hβ' hp' hw1 hw2 (inv β hβ hp hw1 hc) (inv β' hβ' hp' hw2 hc')
  obtain ⟨φ', hp', ht', hsub, hs1, hs2, hs3⟩ := _root_.GlobalTheory.PolFan.exists_starSubdivision E H q φ w hdom hφp hφt hwt hcen
  refine ⟨φ', ht', hp', hsub.trans hφs, fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw X hX
  have hnat : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n :=
    fun β hβ hp => ⟨_, hcar X hX β hβ hp⟩
  have core : ∀ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
      IsCell H.bar φ (Fin.append v u) → IsCell H.bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) →
      (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) →
      (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) →
      (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β →
        ((i + 1 : ℕ) : ℝ) < lab.evalZ β) →
      (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) →
      ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone (Fin.append v u) β₀ →
      ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
        IsFaceCut (Fin.append v u) s h → 0 < h β₀ →
      ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X),
        IsCell H.bar φ' (Fin.append v' u') ∧ IsCell H.bar ψ v' ∧
        (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → _) k)) ∧
        Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β →
          (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
    intro b a v u hγ hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0
    exact _root_.GlobalTheory.PolFan.star_cell_bary_step (𝓞 E) H.bar ψ lab φ' w i X b a v u hv hinj hlu hvl hoff hind hnat
      (fun m' s h hh => _root_.GlobalTheory.PolFan.isCell_face_of_isFaceCut E H q ψ hψ X hX (hdom X) b v hv m' s h hh) h5
      (fun β hβ hp β' hβ' hp' hw1 hw2 hc hc' => (hcen X hX).2.2 _ _ hγ β hβ hp β' hβ' hp' hw1 hw2 hc hc')
      (fun β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e =>
        _root_.GlobalTheory.PolFan.carrierDim_le_of_add_cell (𝓞 E) H.bar q ψ lab hcar X hX b v hv β₀ hb0 hp0 β hβ hp hin c₀ c hc₀ hc e)
      β₀ hb0 hp0 hw0 (h3 β₀ hb0 hp0 hw0) hin0
      (fun m' s h hh hpos => hs2 X hX _ _ hγ β₀ hb0 hp0 hw0 hin0 m' s h hh hpos)
  rcases hs3 X hX n γ' hγ' with ⟨m, γ, hγ, hno, hcov'⟩ | ⟨m, δ, β₀, m', s, h, hδ, hb0, hp0, hw0, hin0, hcut, hpos, hcov'⟩
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m γ hγ
    by_cases hc : ∃ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) ∧ w.evalZ β₀ = 1 ∧ InRCone (Fin.append v u) β₀
    · obtain ⟨β₀, hb0, hp0, hw0, hin0⟩ := hc
      have hnin : ¬ InRCone γ β₀ := fun hh => by
        have := hno β₀ hb0 hp0 hh
        rw [hw0] at this
        exact one_ne_zero this
      obtain ⟨m', s, h, hcut, hpos, hsub'⟩ := reduce_of_not_mem hG hγ hcov hb0 hp0 hin0 hnin
      obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
        core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 hin0 m' s h hcut hpos
      exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_cons_of (n := 0) β₀
        (inRCone_trans hsub' (hcov' j))), r4, r5, r6, r7, r8⟩
    · push_neg at hc
      have hw0 : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → w.evalZ β = 0 :=
        fun β hβ hp hin => (h1 β hβ hp).resolve_right fun e => hc β hβ hp e hin
      refine ⟨b, a, v, u, hs1 X hX _ _ hG hw0, hv, fun j => inRCone_trans hcov (hcov' j), hinj,
        fun j => ?_, fun β hβ hp hin => ?_, fun β hβ hp hin hn => ?_, hind⟩
      · have := hlu j; push_cast at this ⊢; linarith
      · obtain ⟨k, hk⟩ := hnat β hβ hp
        have hle := hvl β hβ hp hin
        rw [hk] at hle ⊢
        have hle' : k ≤ i + 1 := by exact_mod_cast hle
        rcases hle'.lt_or_eq with hl | hl
        · exact_mod_cast Nat.lt_succ_iff.1 hl
        · obtain ⟨β₁, hb1, hp1, hw1, hin1⟩ := h5 b v hv β hβ hp hin (by rw [hk, hl])
          exact absurd (inRCone_append_left v u hin1) (hc β₁ hb1 hp1 hw1)
      · have := hoff β hβ hp hin hn; push_cast at this ⊢; linarith
  · obtain ⟨b, a, v, u, hG, hv, hcov, hinj, hlu, hvl, hoff, hind⟩ := hφc X hX m δ hδ
    obtain ⟨m'', s', h', hcut', hpos', hsub'⟩ := reduce_of_mem hG hδ hcov hin0 hcut hpos
    obtain ⟨b', a', v', u', r1, r2, r3, r4, r5, r6, r7, r8⟩ :=
      core b a v u hG hv hinj hlu hvl hoff hind β₀ hb0 hp0 hw0 (inRCone_trans hcov hin0) m'' s' h' hcut' hpos'
    exact ⟨b', a', v', u', r1, r2, fun j => inRCone_trans r3 (inRCone_trans (inRCone_cons_mono β₀ hsub') (hcov' j)),
      r4, r5, r6, r7, r8⟩

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGLSymmCastGL
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Shift

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}

end Shift

section Read

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem classPresOf_ext (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    (f : (S.toCSD h).Forms) (g : G) :
    (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q g)) := by

  have key : ∀ (γ : Γ) (c : S.Cl) (k : J),
      (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (ι γ * A.y c * k))) := by
    intro γ c k
    have e1 : (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).ext (f : S.Cl → S.V) (ι γ * A.y c * k) =
        (χ k : ℂ) • ρ γ (coef ((f : S.Cl → S.V) c)) :=
      ClassPres.ext_eq (classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl) f γ c k
    have e2 : A.q (ι γ * A.y c * k) = A.gl (γ, k⁻¹) • S.outSec.rep c := by
      rw [A.q_mul, A.q_y]
    have e3 : (((S.res h).symm f : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
      have := S.resOf_apply h S.outSec ((S.res h).symm f) c
      rw [← this]
      show ((((S.res h) ((S.res h).symm f)).1 : S.Cl → S.V) c) = _
      rw [LinearEquiv.apply_symm_apply]
    have e4 := (S.mem_EqFun _).1 ((S.res h).symm f).2 (A.gl (γ, k⁻¹)) (S.outSec.rep c)
    rw [e1, e2, e4, e3, hgl, map_inv, inv_inv, Units.smul_def]
  rw [(classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).dec_spec g]
  exact key _ _ _

variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'} {ρ : Γ →* Module.End ℂ W} {ρ' : Γ' →* Module.End ℂ W}
  {J' : Subgroup G'} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ} {T : Formalism.L2.DIV.CSD K} {σ : K →+* ℂ}

theorem transport_ext (P : ClassPres ι T σ ρ J χ) (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ))
    (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ) (hJ : J' = J.map eG.toMonoidHom)
    (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k) (f : T.Forms) (g : G) :
    (P.transport eG eΓ hι hρ hJ hχ).ext (f : T.Cl → T.V) (eG g) = P.ext f g := by
  rw [P.dec_spec g]
  have hk : eG (P.decK g : G) ∈ J' := by
    rw [hJ]; exact Subgroup.mem_map_of_mem eG.toMonoidHom (P.decK g).2
  have e : eG (ι (P.decG g) * P.y (P.decC g) * (P.decK g : G)) =
      ι' (eΓ (P.decG g)) * (P.transport eG eΓ hι hρ hJ hχ).y (P.decC g) * ((⟨_, hk⟩ : J') : G') := by
    rw [map_mul, map_mul, hι]; rfl
  rw [e, ClassPres.ext_eq, ClassPres.ext_eq, hχ, hρ]
  rfl

end Read

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

open Formalism.IndefR.Bridge

section Assemble

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ : Type} [Group G] [Group Γ]
  {ι : Γ →* G} {J : Subgroup G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {G' Γ' : Type} [Group G'] [Group Γ'] {ι' : Γ' →* G'}

variable (A : AdPts S ι J) (h : S.Ok) (σ : K →+* ℂ) (ρ' : Γ' →* Module.End ℂ W) (k : G) (eG : G ≃* G') (eΓ : Γ ≃* Γ')
    (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (J' : Subgroup G') (χ' : J' →* ℂˣ)
    (hJ : J' = (J.map (MulAut.conj k).toMonoidHom).map eG.toMonoidHom)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x'))
    (hK1 : ∀ κ : J, (κ : G) ∈ A.K1 → ∀ hx : eG (k * κ * k⁻¹) ∈ J', χ' ⟨_, hx⟩ = 1)
    (hgl : ∀ (γ : Γ) (κ : J) (v : S.V) (hx : eG (k * κ * k⁻¹) ∈ J'),
      coef (S.ρ (A.gl (γ, κ)) v) = ((χ' ⟨_, hx⟩)⁻¹ : ℂˣ) • ρ' (eΓ γ) (coef v))

end Assemble

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

end GlobalTheory.Mem.R3.LiftPres

namespace GlobalTheory.Mem.R3.LiftPres

theorem ufGL_ratHom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : Formalism.L2.Col.URat hc n) :
    Formalism.L2.Col.ufGL E n (Formalism.L2.Col.ratHom hc n γ) = (γ : GL (Fin n) E) := by
  show Formalism.L2.Col.toGLm E n (Formalism.UG.glEquiv (γ : GL (Fin n) E)) = _
  simp only [Formalism.L2.Col.toGLm, Formalism.UG.glEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end GlobalTheory.Mem.R3.LiftPres
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupLeBaseLatticeLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_localGroup_le_baseLattice_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | exact GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | (intros; apply GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChainChartLocalUnitCharacterCompatibleLeveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chainChart_localUnitCharacter_compatible_level : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        ∃ ψ : Formalism.L2.G.awayG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram
            (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Uloc ((w.D Z).what₂.places.resChar v) →* ((w.D Z).gat u v hg).Oˣ,
          Formalism.MainNotions.G.CmpJ.UnitCharacterChartCompatibility hj (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (t.cmp.embW u v hg) ψ := by
  first | exact @GlobalTheory.Mem.Top.KerTwPsi.psi_tied | exact GlobalTheory.Mem.Top.KerTwPsi.psi_tied | (intros; apply GlobalTheory.Mem.Top.KerTwPsi.psi_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantOrbitCentreMarkingPolyFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.OrbMark

theorem centres_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → ∀ c : FormFamily (𝓞 E),
    ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ IsCentreSet H.bar q φ w ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar φ M δ → c.Carries δ →
          ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ InRCone δ β) ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) := by
  intro E _ _ _ H q φ lab _hdom _hfan hφ hlab hsl M hM _hmax c
  classical
  by_cases hex : ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X)
      (_ : Module.Projective (𝓞 E) X), Module.finrank (𝓞 E) X ≤ q ∧
      ∃ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar φ M δ ∧ c.Carries δ
  · obtain ⟨X₀, _, _, _, _, -, m₀, δ₀, hM₀, hc₀⟩ := hex
    obtain ⟨v, hv, hvp, hvn, t, ht, htv⟩ := _root_.GlobalTheory.PolFan.CentreChoice.exists_isPrim_frac H.bar φ M δ₀ hM₀ hM
    obtain ⟨h₀, hli, hpr, -⟩ := hM₀
    have hv0 : v ≠ 0 := fun h => by
      have e : (⟨v, hv⟩ : balForms H.bar X₀) = 0 := Subtype.ext h
      rw [e] at hvp
      exact not_isPrim_zero hvp
    refine ⟨OrbMark.orbFun (𝓞 E) H.w0 v, OrbMark.isTwInv_orbFun H v,
      fun X _ _ _ _ hX => ⟨fun β _ _ => OrbMark.orbFun_eval_eq_zero_or_one _ _ _,
        fun β _ _ h1 => _root_.GlobalTheory.PolFan.OrbMark.eq_one_of_smul_eq_of_orbFun_evalZ_eq_one H.bar H.w0 v hv hvp β h1,
        fun m γ hγ β hβ hβp β' hβ' hβp' h1 h1' hc hc' =>
          _root_.GlobalTheory.PolFan.eq_of_orbMark_of_inRCone_cell E H q φ lab hφ hlab hsl δ₀ h₀ hli hpr v t hv0 (fun i => (ht i).1) htv X hX m γ hγ β hβ hβp β' hβ' hβp'
            h1 h1' hc hc'⟩,
      fun X _ _ _ _ _ m δ _ hδ => ?_,
      fun X _ _ _ _ _ m δ h hδ hδp β hβ hβp h1 c' hc' hβc =>
        _root_.GlobalTheory.orbMark_coord_lt_one E H φ hφ δ₀ h₀ hli hpr v t hv0 ht htv X m δ h hδ hδp β hβ hβp h1 c' hc' hβc⟩
    obtain ⟨β, hβ, hβp, h1, hin⟩ := _root_.GlobalTheory.PolFan.carries_exists_marked H.bar H.w0 c δ₀ v t hv hv0 hvn hc₀ (fun i => (ht i).1) htv X m δ hδ
    exact ⟨β, hβ, hβp, h1, hin⟩
  · refine ⟨zeroFun (𝓞 E), fun _ _ _ _ => rfl, fun X _ _ _ _ _ =>
      ⟨fun β _ _ => Or.inl (zeroFun_evalZ β), fun β _ _ h => by simp at h,
        fun _ _ _ β _ _ _ _ _ h => by simp at h⟩,
      fun X _ _ _ _ hX m δ hδ hc => (hex ⟨X, inferInstance, inferInstance, inferInstance, inferInstance, hX, m, δ, hδ, hc⟩).elim,
      fun X _ _ _ _ _ m δ _ _ _ β _ _ h => by simp at h⟩

end GlobalTheory.PolFan.OrbMark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointClassDensityHodgeMetricBoundedDomain
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnifDens

theorem chernTop_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ (h : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = X.dim) (v : ReciprocityTheory.L2DbarEstimates.V X.dim), GlobalTheory.UnifDens.flatL h v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ∀ A ∈ Eb.S (under (ψ (GlobalTheory.UnifDens.flatL h v))), chernTop (pointPoly H Dw) (fun u => lieGram e U hj f₀ A₀ A (ψ (GlobalTheory.UnifDens.flatL h u))) v = grassConst Dw.p (Dw.p + Dw.q - Dw.p) ^ Fintype.card (U.X k).Ψ * ∏ i, ((hQ (unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((Dw.p + (Dw.p + Dw.q - Dw.p) : ℕ) : ℤ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA
  rw [GlobalTheory.T.pointClass_density_hodge_uniformisation_eq_model E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ h v hv A hA,
    GlobalTheory.T.chernPolyTopDensity_bounded_domain_invariant _ _ _ _ h v hv, GlobalTheory.T.chernTop_density_model_metric_origin]

end GlobalTheory.UnifDens
end

