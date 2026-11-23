module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTotalMassLeGenericMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMassStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsFullLattice K L → ENNReal.ofReal (mass h L) = orbMass (isom h) (genus h L) ∧ 0 < mass h L ∧ Stable (isom h) (genus h L) ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → Finite (MulAction.stabilizer (isom h) M)) ∧ ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), Formalism.ThetaLiftIndependence.IsClassReps h L s → (∀ (g : isom h) M, N (g • M) = N M) → ∑ M ∈ s, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M = orbSum (isom h) (genus h L) N := by
  first
  | exact @GlobalTheory.Mass.GenusOrb.main
  | intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL
    obtain ⟨a, b, c, d, e⟩ := GlobalTheory.Mass.GenusOrb.main K V h hK hs hp L hL.toIsLattice
    exact ⟨a, b, c, fun M hM => d M hM.toIsLattice, e⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalSumsEqConstMulCoordinateSumsStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLocalSums_eq_const_mul_coordinateSums : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ LocNG.sumSq R d0 (LocNG.BBne (H := H)) = ENNReal.ofReal κ * S.ampSq (fun d Λ => ¬ S.BBzero d Λ) ∧ LocNG.sumSq R d0 (fun t => ¬ LocNG.BBne (H := H) t) = ENNReal.ofReal κ * S.ampSq S.BBzero ∧ LocNG.sumSq R d0 (fun _ => True) = ENNReal.ofReal κ * S.ampSq (fun _ _ => True) ∧ LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
  first | exact @GlobalTheory.HL.CoordSq.sums_eq | exact GlobalTheory.HL.CoordSq.sums_eq | (intros; apply GlobalTheory.HL.CoordSq.sums_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTotalMassLeGenericMassStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_total_mass_le_generic_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 d₁ : LocNG.Datum P) (t₁ : Term V M r), LocNG.IsTermOver P d₁ t₁ → ∀ Cl : Term V M r → Prop, (∀ t, Cl t ↔ ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t.f j = ∑ i, A i j • s (t₁.f i)) ∧ ∀ j, t.f' j = ∑ i, A' i j • s (t₁.f' i)) → ∀ g : ℝ≥0∞, g = ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : {t // t ∈ R.RT d.1 ∧ ¬ LocNG.BBne (H := H) t ∧ Cl t}, ENNReal.ofReal (LocNG.mu P t.1) → g ≠ ⊤ ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ ((∃ t', LocNG.IsTermOver P d0 t') → g ≠ 0) := by
  first | exact @GlobalTheory.HL.AbsGenMass.total_le_generic | exact GlobalTheory.HL.AbsGenMass.total_le_generic | (intros; apply GlobalTheory.HL.AbsGenMass.total_le_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapCompNeg
section
open Formalism.HermitianLatticeCounting.S6

namespace GlobalTheory.RowStab

theorem gen_comp_gen_neg {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K)
    (he : ∀ a b, H.B (e a) (e b) = 0) (hρe : ∀ a b, H.B (ρ a) (e b) = 0)
    (hc : ∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) (v : V) :
    gen H J e ρ c (gen H J e (-ρ) c' v) = v := by
  have heρ : ∀ a b, H.B (e a) (ρ b) = 0 := fun a b => by rw [← H.herm, hρe, star_zero]
  set u := gen H J e (-ρ) c' v with hu
  have hue : ∀ b, H.B u (e b) = H.B v (e b) := by
    intro b
    rw [hu, gen_apply]
    simp [LinearMap.sum_apply, he, hρe]
  have huρ : ∀ b, H.B u (ρ b) = H.B v (ρ b) - ∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b) := by
    intro b
    rw [hu, gen_apply]
    simp [LinearMap.sum_apply, heρ, sub_eq_add_neg]
  have h4 : ∑ b ∈ J, (∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b)) • e b =
      ∑ b ∈ J, ∑ a ∈ J, (H.B (ρ b) (ρ a) * H.B v (e b)) • e a := by
    simp_rw [Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  have key : (∑ b ∈ J, ∑ a ∈ J, (c' a b * H.B v (e b)) • e a) +
      (∑ b ∈ J, (∑ d ∈ J, H.B v (e d) * H.B (ρ d) (ρ b)) • e b) +
      ∑ b ∈ J, ∑ a ∈ J, (c a b * H.B v (e b)) • e a = 0 := by
    rw [h4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← add_smul, ← add_smul, ← add_mul, ← add_mul,
      show c' a b + H.B (ρ b) (ρ a) + c a b = 0 by linear_combination hc a b, zero_mul, zero_smul]
  rw [gen_apply H J e ρ c u]
  simp only [hue, huρ]
  rw [hu, gen_apply H J e (-ρ) c' v]
  simp only [map_neg, Pi.neg_apply, neg_smul, smul_neg, sub_smul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  linear_combination (norm := module) key

end GlobalTheory.RowStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapIsometry
section
open Formalism.HermitianLatticeCounting.S6

namespace GlobalTheory.RowStab

theorem gen_isometry {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K) (hee : ∀ a b, H.B (e a) (e b) = 0) (hρe : ∀ a b, H.B (ρ a) (e b) = 0) (hc : ∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) (u v : V) : H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by
  have heρ : ∀ a b, H.B (e a) (ρ b) = 0 := fun a b => by rw [← H.herm, hρe, star_zero]
  have hX : ∀ w y, H.B (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) y = ∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y) := by
    intro w y
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, LinearMap.sum_apply, mul_assoc]
  have hXr : ∀ w y, H.B y (∑ b ∈ J, (H.B w (e b) • ρ b - H.B w (ρ b) • e b + ∑ a ∈ J, (c a b * H.B w (e b)) • e a)) = star (∑ b ∈ J, (H.B w (e b) * H.B (ρ b) y - H.B w (ρ b) * H.B (e b) y + ∑ a ∈ J, c a b * H.B w (e b) * H.B (e a) y)) := by
    intro w y; rw [← H.herm, hX]
  have hρv : ∀ b, H.B (ρ b) v = star (H.B v (ρ b)) := fun b => (H.herm _ _).symm
  have hev : ∀ b, H.B (e b) v = star (H.B v (e b)) := fun b => (H.herm _ _).symm
  have hρu : ∀ b, H.B (ρ b) u = star (H.B u (ρ b)) := fun b => (H.herm _ _).symm
  have heu : ∀ b, H.B (e b) u = star (H.B u (e b)) := fun b => (H.herm _ _).symm
  rw [GlobalTheory.RowStab.gen_apply, GlobalTheory.RowStab.gen_apply]
  simp only [map_add (f := _), LinearMap.add_apply, hX, hXr, hee, heρ, hρe, mul_zero, sub_zero, add_zero, Finset.sum_const_zero, star_zero, hρv, hev, hρu, heu, star_sum, star_add, star_sub, star_mul', star_star]
  have hρρ : ∀ a b, star (H.B (ρ a) (ρ b)) = H.B (ρ b) (ρ a) := fun a b => H.herm _ _
  simp only [hρρ]
  have h2 : ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) = ∑ x ∈ J, ∑ x1 ∈ J, star (c x x1) * star (H.B v (e x1)) * H.B u (e x) := Finset.sum_comm
  have hS : ∑ x ∈ J, ∑ x1 ∈ J, c x1 x * H.B u (e x) * star (H.B v (e x1)) + ∑ x ∈ J, ∑ x1 ∈ J, star (c x1 x) * star (H.B v (e x)) * H.B u (e x1) + ∑ x ∈ J, H.B u (e x) * ∑ x1 ∈ J, star (H.B v (e x1)) * H.B (ρ x) (ρ x1) = 0 := by
    rw [h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x1 _
    linear_combination (H.B u (e x) * star (H.B v (e x1))) * hc x x1
  have hA : ∑ x ∈ J, star (H.B v (ρ x)) * H.B u (e x) = ∑ x ∈ J, H.B u (e x) * star (H.B v (ρ x)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hB : ∑ x ∈ J, star (H.B v (e x)) * H.B u (ρ x) = ∑ x ∈ J, H.B u (ρ x) * star (H.B v (e x)) := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination hS - hA + hB

end GlobalTheory.RowStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdxSupRight
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Compl

section General

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem idx_sup_right (X B : Submodule R W) : idx (X ⊔ B) B = idx X B :=
  DelScale.idx_sup le_rfl

theorem idx_glue (M U U' : Submodule R W) :
    idx (U ⊓ (M ⊔ U')) (M ⊓ U) = idx ((M ⊔ U) ⊓ (M ⊔ U')) M := by
  rw [sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), sup_comm M (U ⊓ _), idx_sup_right,
    ← DelScale.idx_inf_left, ← DelScale.idx_inf_left _ M]
  congr 1
  exact le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans inf_le_left)))

theorem gidx_glue (M U U' : Submodule R W) :
    gidx (U ⊓ (M ⊔ U')) (M ⊓ U) = idx ((M ⊔ U) ⊓ (M ⊔ U')) M := by
  have : idx (M ⊓ U) (U ⊓ (M ⊔ U')) = 1 :=
    AddSubgroup.relIndex_eq_one.2 fun x hx => ⟨hx.2, Submodule.mem_sup_left hx.1⟩
  rw [gidx, this, idx_glue]
  simp

theorem gen_glue (M U U' : Submodule R W) (t : Finset W)
    (h : U ⊓ (M ⊔ U') = (M ⊓ U) ⊔ Submodule.span R (t : Set W)) :
    ∃ t' : Finset W, t'.card ≤ t.card ∧ U' ⊓ (M ⊔ U) = (M ⊓ U') ⊔ Submodule.span R (t' : Set W) := by
  have h1 : ∀ x : W, ∃ y : W, x ∈ t → y ∈ U' ∧ x - y ∈ M := by
    intro x
    by_cases hx : x ∈ t
    · have : x ∈ U ⊓ (M ⊔ U') := h ▸ Submodule.mem_sup_right (Submodule.subset_span hx)
      obtain ⟨m, hm, y, hy, e⟩ := Submodule.mem_sup.1 this.2
      exact ⟨y, fun _ => ⟨hy, by rw [← e]; simpa using hm⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose f hf using h1
  refine ⟨t.image f, Finset.card_image_le, ?_⟩
  have a : Submodule.span R (t.image f : Set W) ≤ U' := by
    rw [Submodule.span_le]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact (hf x hx).1
  have b : M ⊔ Submodule.span R (t : Set W) = M ⊔ Submodule.span R (t.image f : Set W) := by
    apply le_antisymm
    · refine sup_le le_sup_left (Submodule.span_le.2 fun x hx => ?_)
      exact Submodule.mem_sup.2 ⟨_, (hf x hx).2, f x,
        Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx)), by abel⟩
    · refine sup_le le_sup_left (Submodule.span_le.2 fun y hy => ?_)
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact Submodule.mem_sup.2 ⟨_, M.neg_mem (hf x hx).2, x, Submodule.subset_span hx, by abel⟩
  have c : (M ⊔ U) ⊓ (M ⊔ U') = M ⊔ Submodule.span R (t.image f : Set W) := by
    rw [sup_inf_assoc_of_le U (le_sup_left : M ≤ M ⊔ U'), h, ← sup_assoc, sup_inf_self, b]
  have d : U' ⊓ (M ⊔ U) = ((M ⊔ U) ⊓ (M ⊔ U')) ⊓ U' := by
    rw [inf_assoc, inf_comm U', inf_eq_right.2 (le_sup_right : U' ≤ M ⊔ U')]
  rw [d, c, sup_comm M, sup_inf_assoc_of_le M a, sup_comm]

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in
theorem exists_mult {M : Submodule (𝓞 K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ c : K, c ≠ 0 ∧ c • v ∈ M := by
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (M : Set V) v hv
  rw [Submodule.span_eq] at hs
  refine ⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_⟩
  rw [algebraMap_smul]
  exact hs

omit [StarRing K] [FiniteDimensional K V] in
theorem span_inf {M : Submodule (𝓞 K) V} {T : Submodule K V} (hT : T ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ rs (𝓞 K) T : Submodule (𝓞 K) V) : Set V) = T := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun x hx => hx.2
  · intro v hv
    obtain ⟨c, hc, h⟩ := exists_mult (hT hv)
    rw [← Submodule.smul_mem_iff _ hc]
    exact Submodule.subset_span ⟨h, T.smul_mem c hv⟩

theorem key (H : HermSpace K V) {M : Submodule (𝓞 K) V} {S I : Submodule K V} (hIS : I ≤ S)
    (hrad : ∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) (hM : IsUnimodMod H M S I)
    {T : Submodule K V} (hIT : I ≤ T) (hTS : T ≤ S) :
    dual H (M ⊓ rs (𝓞 K) T) = rs (𝓞 K) T ⊓ (M ⊔ rs (𝓞 K) (S ⊓ perp H T)) ∧
      S ⊓ perp H (S ⊓ perp H T) = T := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective I.subtype (Submodule.ker_subtype I)
  have hr' : ∀ x (hx : x ∈ I), (r x : V) = x := fun x hx =>
    congrArg Subtype.val (LinearMap.congr_fun hr ⟨x, hx⟩)
  set p : V →ₗ[K] V := LinearMap.id - I.subtype ∘ₗ r with hp
  have hpx : ∀ x, p x = x - r x := fun x => rfl
  set C : Submodule K V := S ⊓ LinearMap.ker r with hCd
  have hCS : C ≤ S := inf_le_left
  have hpC : ∀ x ∈ S, p x ∈ C := fun x hx => ⟨S.sub_mem hx (hIS (r x).2), by
    change r (p x) = 0
    rw [hpx, map_sub, sub_eq_zero]
    exact (Subtype.ext (hr' _ (r x).2)).symm⟩
  have hpI : ∀ x, x - p x ∈ I := fun x => by rw [hpx]; simp
  have hI : ∀ x ∈ I, p x = 0 := fun x hx => by rw [hpx, hr' x hx, sub_self]
  have hC : ∀ x ∈ C, p x = x := fun x hx => by
    have : r x = 0 := hx.2
    rw [hpx, this]; simp
  have o1 : ∀ i ∈ I, ∀ y ∈ S, H.B i y = 0 := fun i hi => (hrad i (hIS hi)).2 hi
  have o2 : ∀ i ∈ I, ∀ y ∈ S, H.B y i = 0 := fun i hi y hy => by rw [← H.herm, o1 i hi y hy, star_zero]
  have o3 : ∀ y ∈ S, ∀ x, H.B y (p x) = H.B y x := fun y hy x => by
    rw [hpx, map_sub, o2 _ (r x).2 y hy, sub_zero]
  have o4 : ∀ y ∈ S, ∀ x, H.B (p x) y = H.B x y := fun y hy x => by
    rw [← H.herm, o3 y hy, H.herm]
  have hpT : ∀ x ∈ T, p x ∈ T := fun x hx => T.sub_mem hx (hIT (r x).2)
  let HC : HermSpace K C :=
    { B := H.B.domRestrict₁₂ C C
      herm := fun x y => H.herm x y
      nondeg := fun x hx => by
        have : (x : V) ∈ I := (hrad x (hCS x.2)).1 fun y hy => by
          rw [← o3 x (hCS x.2)]; exact hx ⟨_, hpC y hy⟩
        exact Subtype.ext ((hC x x.2).symm.trans (hI x this)) }
  have hB : ∀ x y : C, HC.B x y = H.B x y := fun _ _ => rfl
  obtain ⟨a, b⟩ := DelScale.le_of_latMod hM.1
  have hpM : ∀ x ∈ M, p x ∈ M := fun x hx => M.sub_mem hx (a (r x).2)
  have L := DelScale.latIn_isFullLattice p hCS hpC hpI hI hC hM.1
  have hMd : ∀ y, y ∈ M ↔ y ∈ S ∧ ∀ x ∈ M, H.B y x ∈ (1 : Submodule (𝓞 K) K) := fun y => by
    rw [← hM.1.2, ← mem_dual_iff, hM.2]
  have hU : IsUnimod HC (GlobalTheory.Mass.latIn C M) := by
    refine ⟨(isLatMod_top_bot_iff _).2 ⟨L.toIsLattice.fg, L.span_eq_top⟩, ?_⟩
    ext y
    rw [mem_dual_iff, L.span_eq_top]
    change _ ↔ (y : V) ∈ M
    rw [hMd]
    refine ⟨fun hy => ⟨hCS y.2, fun x hx => ?_⟩, fun hy => ⟨trivial, fun x hx => hy.2 x hx⟩⟩
    rw [← o3 y (hCS y.2)]
    exact hy.2 ⟨p x, hpC x (b hx)⟩ (hpM x hx)
  constructor
  · ext d
    rw [mem_dual_iff, span_inf (hM.1.2 ▸ hTS)]
    constructor
    · rintro ⟨hd, hdM⟩
      refine ⟨hd, ?_⟩
      have hx : ∀ x : ↥(GlobalTheory.Mass.latIn C M ⊓ rs (𝓞 K) (T.comap C.subtype)),
          IsIntegral ℤ (H.B ((x : C) : V) d) := by
        intro x
        rw [← UnimodQuot.mem_one_iff, ← H.herm]
        exact UnimodQuot.star_mem_one (hdM _ ⟨x.2.1, x.2.2⟩)
      let φ : ↥(GlobalTheory.Mass.latIn C M ⊓ rs (𝓞 K) (T.comap C.subtype)) →ₗ[𝓞 K] 𝓞 K :=
        { toFun := fun x => ⟨H.B ((x : C) : V) d, hx x⟩
          map_add' := fun a b => by
            apply RingOfIntegers.ext
            show H.B (((a : C) : V) + (b : C)) d = H.B (a : C) d + H.B (b : C) d
            simp
          map_smul' := fun a b => by
            apply RingOfIntegers.ext
            show H.B (a • ((b : C) : V)) d = algebraMap (𝓞 K) K a * H.B (b : C) d
            rw [← algebraMap_smul K a, map_smul]
            rfl }
      obtain ⟨y, hy, h'⟩ := UnimodQuot.exists_lattice_rep HC hU (T.comap C.subtype) φ
      refine Submodule.mem_sup.2 ⟨y, hy, d - y, ⟨S.sub_mem (hTS hd) (hCS y.2), ?_⟩, by abel⟩
      refine (mem_perp_iff H T _).2 fun x hx => ?_
      obtain ⟨c, hc, h⟩ := exists_mult (M := M) (v := x) (hM.1.2 ▸ hTS hx)
      have hcT := T.smul_mem c hx
      have h1 : H.B (p (c • x)) y = H.B (p (c • x)) d :=
        h' ⟨⟨p (c • x), hpC _ (hTS hcT)⟩, hpM _ h, hpT _ hcT⟩
      rw [o4 _ (hCS y.2), o4 _ (hTS hd), map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at h1
      rw [← H.herm, map_sub, smul_right_injective K hc h1, sub_self, star_zero]
    · rintro ⟨hd, hdM⟩
      refine ⟨hd, fun x hx => ?_⟩
      obtain ⟨m, hm, u, hu, rfl⟩ := Submodule.mem_sup.1 hdM
      rw [map_add (f := _), LinearMap.add_apply, (mem_perp_iff H T u).1 hu.2 x hx.2, add_zero]
      exact ((hMd m).1 hm).2 x hx.1
  · apply le_antisymm
    · rintro s ⟨hs, hs'⟩
      have h1 : (⟨p s, hpC s hs⟩ : C) ∈ T.comap C.subtype := by
        apply UnimodQuot.mem_of_perp_perp HC
        intro x hx
        rw [hB]
        change H.B x (p s) = 0
        rw [o3 _ (hCS x.2), ← H.herm, (mem_perp_iff H _ s).1 hs' x ⟨hCS x.2, ?_⟩, star_zero]
        refine (mem_perp_iff H T _).2 fun z hz => ?_
        rw [← o3 _ (hCS x.2)]
        exact (mem_perp_iff HC _ x).1 hx ⟨p z, hpC z (hTS hz)⟩ (hpT z hz)
      have h2 : p s ∈ T := h1
      simpa using T.add_mem h2 (hIT (hpI s))
    · intro x hx
      refine ⟨hTS hx, (mem_perp_iff H _ _).2 fun y hy => ?_⟩
      rw [← H.herm, (mem_perp_iff H T y).1 hy.2 x hx, star_zero]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (M : Submodule (𝓞 K) V) (S I U : Submodule K V), I ≤ U → U ≤ S → (∀ x ∈ S, (∀ y ∈ S, H.B x y = 0) ↔ x ∈ I) → (∀ x ∈ U, (∀ y ∈ U, H.B x y = 0) ↔ x ∈ I) → IsUnimodMod H M S I → del H (M ⊓ rs (𝓞 K) U) = del H (M ⊓ rs (𝓞 K) (S ⊓ perp H U)) ∧ ∀ e : ℕ, GenBy (dual H (M ⊓ rs (𝓞 K) U)) (M ⊓ rs (𝓞 K) U) e → GenBy (dual H (M ⊓ rs (𝓞 K) (S ⊓ perp H U))) (M ⊓ rs (𝓞 K) (S ⊓ perp H U)) e := by
  intro K V _ _ _ _ _ _ _ _ H _ M S I U hIU hUS hrad _ hM
  have hIS := hIU.trans hUS
  obtain ⟨h1, h2⟩ := key H hIS hrad hM hIU hUS
  have hI' : I ≤ S ⊓ perp H U := fun i hi =>
    ⟨hIS hi, (mem_perp_iff H U i).2 fun x hx => (hrad i (hIS hi)).2 hi x (hUS hx)⟩
  obtain ⟨h3, -⟩ := key H hIS hrad hM hI' inf_le_left
  rw [h2] at h3
  constructor
  · rw [del, del, h1, h3, gidx_glue, gidx_glue, inf_comm]
  · rintro e ⟨t, ht, h⟩
    rw [h1] at h
    obtain ⟨t', ht', h'⟩ := gen_glue _ _ _ t h
    exact ⟨t', ht'.trans ht, h3.trans h'⟩

end GlobalTheory.DegCnt.Compl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassDefectOrderLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DefectShare

theorem mass_defect_order_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal ((4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β hβ
  by_cases hex : ∃ d Λ, S.IsTerm d Λ
  swap
  · have h0 : (S.sumData fun d => S.mass d fun Λ => S.be d Λ = β) = 0 := by
      have : ∀ d Λ, ¬ S.IsTerm d Λ := fun d Λ h => hex ⟨d, Λ, h⟩
      simp [Frames.sumData, Frames.mass, this]
    rw [h0]; exact zero_le
  obtain ⟨d0, Λ0, h0⟩ := hex
  obtain ⟨-, -, -, hq, -⟩ := _root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d0 Λ0 h0
  have hconst : 4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹ ≤
      (4 * S.Hp ^ (4 * (r + 1))) * ((β : ℝ) ^ (k - 1))⁻¹ := by
    have e : (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) = ((S.q : ℝ) ^ S.a) ^ (4 * (r + 1)) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e]
    have hn : (0 : ℝ) ≤ (S.q : ℝ) ^ S.a := zpow_nonneg (Nat.cast_nonneg _) _
    gcongr
  have s1 := (_root_.GlobalTheory.HL.sumData_mass_eq_sumCls L r k S (fun d Λ => S.be d Λ = β) (fun h hh d Λ hT hP => by
    have := (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.1
    exact this.trans hP)).1
  have s2 := (_root_.GlobalTheory.HL.sumData_mass_eq_sumCls L r k S (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)).1
  unfold Frames.nn
  rw [s1, s2]
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with hC
  · rw [mul_left_comm]
    refine mul_le_mul_right ?_ _
    refine (GlobalTheory.T.hermitianFrames_defectOrder_share_le L r k S hk _ hC.1 β hβ).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) ?_
    unfold Frames.sumData
    refine ENNReal.tsum_le_tsum fun o' => mul_le_mul' le_rfl ?_
    unfold Frames.nT
    exact ENat.toENNReal_le.mpr (Set.encard_le_encard fun Λ h => ⟨h.1, trivial, h.2.2⟩)
  · exact zero_le

end GlobalTheory.DefectShare
end

