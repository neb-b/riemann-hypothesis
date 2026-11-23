module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.ProperGenMap
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.SumCoordBasisDual
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.CupK
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem cupK (P : HTPre l K) {M : Model l K} (hM : M.Sm) {D : ℕ} (S : Sq M D) {i j : ℕ} (X : M.T i) (Y : M.T j)
    (Z : S.P.T (i + j)) (hZ : S.P.CupT (Model.pullT S.p₁ S.h₁ i X) (Model.pullT S.p₂ S.h₂ j Y) Z)
    {m m' : ℕ → ℕ} (b : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a i)) (b' : ∀ a, Module.Basis (Fin (m' a)) K (Hdg M.q a j))
    (A : ℕ) (Θ : Module.Dual K (Hdg S.P.q A (i + j))) :
    P.h S.P A (i + j) (S.P.toV _ Z) Θ = ∑ p : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)), ∑ s, ∑ s',
      P.h M p.1.1 i (M.toV _ X) ((b p.1.1).coord s) * P.h M p.1.2 j (M.toV _ Y) ((b' p.1.2).coord s') *
        kC K (Θ (cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl (S.pl₁ p.1.1 i (b p.1.1 s))
          (S.pl₂ p.1.2 j (b' p.1.2 s')))) := by
  classical
  have hfin : ∀ a n, FiniteDimensional K (Hdg S.P.q a n) := fun a n => (P.fin S.P S.smP a n).1
  rw [P.cup S.P S.smP (Model.pullT S.p₁ S.h₁ i X) (Model.pullT S.p₂ S.h₂ j Y) Z hZ
    (fun a => Module.finBasis K (Hdg S.P.q a i)) (fun a => Module.finBasis K (Hdg S.P.q a j)) A Θ]
  refine Finset.sum_congr rfl fun p _ => ?_
  obtain ⟨bl, hbl'⟩ : ∃ bl : Hdg S.P.q p.1.1 i →ₗ[K] Hdg S.P.q p.1.2 j →ₗ[K] Hdg S.P.q A (i + j),
      ∀ x y, bl x y = cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl x y :=
    CrystallineSemistableComparison.P.cup_bilin (grOk (smFun _ S.P.q) (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2)).pair (rfl : i + j = i + j)
  have n₁ : ∀ F, P.h S.P p.1.1 i (S.P.toV i (Model.pullT S.p₁ S.h₁ i X)) F = P.h M p.1.1 i (M.toV i X) (F ∘ₗ S.pl₁ p.1.1 i) := by
    intro F
    rw [← pullV_toV S.p₁ S.h₁ i X, P.nat S.P M S.p₁ S.h₁ S.smP hM]
  have n₂ : ∀ F, P.h S.P p.1.2 j (S.P.toV j (Model.pullT S.p₂ S.h₂ j Y)) F = P.h M p.1.2 j (M.toV j Y) (F ∘ₗ S.pl₂ p.1.2 j) := by
    intro F
    rw [← pullV_toV S.p₂ S.h₂ j Y, P.nat S.P M S.p₂ S.h₂ S.smP hM]
  have key := gen2 (kC K) (P.h S.P p.1.1 i (S.P.toV i (Model.pullT S.p₁ S.h₁ i X))) (P.h M p.1.1 i (M.toV i X))
    (P.h S.P p.1.2 j (S.P.toV j (Model.pullT S.p₂ S.h₂ j Y))) (P.h M p.1.2 j (M.toV j Y))
    (fun k φ => P.lin' _ _ _ k _ φ) (fun k φ => P.lin' _ _ _ k _ φ) (fun k φ => P.lin' _ _ _ k _ φ) (fun k φ => P.lin' _ _ _ k _ φ)
    (S.pl₁ p.1.1 i) (S.pl₂ p.1.2 j) n₁ n₂ (bl.compr₂ Θ)
    (Module.finBasis K (Hdg S.P.q p.1.1 i)) (Module.finBasis K (Hdg S.P.q p.1.2 j)) (b p.1.1) (b' p.1.2)
  simp only [LinearMap.compr₂_apply, hbl'] at key
  exact key

end CrystallineSemistableComparison.Onto

end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.StepA
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem stepA (hC : CupLaws) (P : HTPre l K) {M : Model l K} {d : ℕ} (S : Sq M (d + 1)) (hEt : Etale S.D.f)
    (r : E.Roots l) (v : S.Y.T 2) (hv : IsEtaleFirstChernUntwisted r S.D v) (e : Hdg S.Y.q 1 2) (he : IsDlogFirstChernClass S.Y.q (genD S.D) e)
    (c : S.P.T (2 + 2 * d)) (w : S.Y.T (2 * d)) (z : S.Y.T (2 + 2 * d)) (hz : S.Y.CupT v w z)
    (hcz : S.Y.toV _ (Model.pullT S.π S.hπ _ c) = S.Y.toV _ z) (A : ℕ) (Θ : Module.Dual K (Hdg S.P.q A (2 + 2 * d)))
    (hΘ : ∀ C, (pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) A _ C = 0 ∨ ∃ (a₀ n₀ : ℕ) (ha : 1 + a₀ = A)
      (hn : 2 + n₀ = 2 + 2 * d) (w : Hdg S.Y.q a₀ n₀),
        pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) A _ C = cupH S.Y.q ha hn e w) → Θ C = 0) :
    P.h S.P A (2 + 2 * d) (S.P.toV _ c) Θ = 0 := by
  obtain ⟨φ, hφf, hφg⟩ : ∃ φ : Module.Dual K (Hdg S.Y.q A (2 + 2 * d)),
      φ ∘ₗ pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) A (2 + 2 * d) = Θ ∧
      ∀ (a₀ : ℕ) (ha : 1 + a₀ = A) (u : Hdg S.Y.q a₀ (2 * d)), φ (cupH S.Y.q ha rfl e u) = 0 := by
    rcases Nat.eq_zero_or_pos A with hA | hA
    · subst hA
      obtain ⟨φ, h1, -⟩ := la_kill (pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) 0 (2 + 2 * d))
        (0 : Hdg S.Y.q 0 (2 + 2 * d) →ₗ[K] Hdg S.Y.q 0 (2 + 2 * d)) Θ
        (fun C u h => hΘ C (Or.inl (by simpa using h)))
      exact ⟨φ, h1, fun a₀ ha => absurd ha (by omega)⟩
    · obtain ⟨a, rfl⟩ : ∃ a, A = 1 + a := ⟨A - 1, by omega⟩
      obtain ⟨φ, h1, h2⟩ := la_kill (pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) (1 + a) (2 + 2 * d))
        (cupL hC S.Y.q (a := 1) (a' := a) (c := 1 + a) (i := 2) (j := 2 * d) (n := 2 + 2 * d) rfl rfl e) Θ
        (fun C u h => hΘ C (Or.inr ⟨a, 2 * d, rfl, rfl, u, by rw [h, cupL_apply]⟩))
      refine ⟨φ, h1, fun a₀ ha u => ?_⟩
      obtain rfl : a₀ = a := by omega
      have := LinearMap.congr_fun h2 u
      simpa [cupL_apply] using this
  have hc1 := P.c1 S.Y S.smY S.D hEt S.loc r v e hv he
  let b : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg S.Y.q a 2))) K (Hdg S.Y.q a 2) := fun a =>
    haveI := (P.fin S.Y S.smY a 2).1
    Module.finBasis K _
  let b' : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg S.Y.q a (2 * d)))) K (Hdg S.Y.q a (2 * d)) := fun a =>
    haveI := (P.fin S.Y S.smY a (2 * d)).1
    Module.finBasis K _
  have key : ∀ (a a' : ℕ) (ha : a + a' = A), ∑ s, ∑ s', P.h S.Y a 2 (S.Y.toV _ v) ((b a).coord s) *
      P.h S.Y a' (2 * d) (S.Y.toV _ w) ((b' a').coord s') *
        kC K (φ (cupH S.Y.q ha rfl (b a s) (b' a' s'))) = 0 := by
    intro a a' ha
    by_cases h1 : a = 1
    · subst h1
      simp_rw [hc1.1]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s' _ => ?_
      have hs := esum (kC K) (b 1) (φ ∘ₗ (cupL hC S.Y.q (i := 2) (j := 2 * d) ha rfl).flip (b' a' s')) e
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply] at hs
      rw [hφg a' ha, map_zero] at hs
      calc ∑ s, kC K ((b 1).coord s e) * P.h S.Y a' (2 * d) (S.Y.toV _ w) ((b' a').coord s') *
            kC K (φ (cupH S.Y.q ha rfl (b 1 s) (b' a' s')))
          = P.h S.Y a' (2 * d) (S.Y.toV _ w) ((b' a').coord s') *
            ∑ s, kC K ((b 1).coord s e) * kC K (φ (cupH S.Y.q ha rfl (b 1 s) (b' a' s'))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
        _ = 0 := by rw [hs, mul_zero]
    · refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
      rw [hc1.2 a h1, zero_mul, zero_mul]
  rw [← hφf, ← P.nat S.Y S.P S.π S.hπ S.smY S.smP A (2 + 2 * d) (S.P.toV _ c) φ, pullV_toV, hcz,
    P.cup S.Y S.smY v w z hz b b' A φ]
  exact Finset.sum_eq_zero fun p _ => key _ _ _

end CrystallineSemistableComparison.Onto

end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.SurjOfCore
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem surj_of_core (hC : CupLaws) (P : HTPre l K) (M : Model l K) (n : ℕ)
    (h : ∀ a' (x : Hdg M.q a' n), ∃ N : ℚ_[l], N ≠ 0 ∧ tgt hC x N ∈ Sp P M n) : Surj P M n := by
  intro m b z hz a' ha'
  funext s0
  let L : GF M n →ₗ[ℂ_[l]] ℂ_[l] :=
    { toFun := fun g => ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * g a ((b a).coord s)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
        ring }
  have hL : Sp P M n ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, rfl⟩
    exact hz v
  obtain ⟨N, hN, hmem⟩ := h a' (b a' s0)
  have h0 : L (tgt hC (b a' s0) N) = 0 := hL hmem
  have hGe : ∀ s, Gx hC (b a' s0) ((b a').coord s) (oneH M.q) = (b a').coord s (b a' s0) := by
    intro s
    unfold Gx
    rw [dite_eq_left (Nat.zero_add a')]
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
    rw [(hC _ _ M.q).2.2.2.1]
  have hGn : ∀ a, a ≠ a' → ∀ s, Gx hC (b a' s0) ((b a).coord s) (oneH M.q) = 0 := by
    intro a ha s
    unfold Gx
    rw [dite_eq_right (by omega)]
    rfl
  have hv : L (tgt hC (b a' s0) N) = z a' s0 * qC l N := by
    show ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * (qC l N * kC K (Gx hC (b a' s0) ((b a).coord s) (oneH M.q))) = _
    rw [Finset.sum_eq_single a']
    · simp only [hGe, Module.Basis.coord_apply, Module.Basis.repr_self]
      rw [Finset.sum_eq_single s0]
      · simp
      · intro s _ hs
        simp [Ne.symm hs]
      · simp
    · intro a _ ha
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hGn a ha]
      simp
    · intro ha
      exact absurd (Finset.mem_range.2 (by omega)) ha
  rw [hv] at h0
  have hq : qC l N ≠ 0 := (map_ne_zero (qC l)).2 hN
  simpa [hq] using h0

end CrystallineSemistableComparison.Onto

end
end

