module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Formalism.HermitianLattices.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProd
public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianLatticesGluedAlongLine
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.LineGlue

theorem sup_span_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (B : Submodule R W) {y z : W} (hyz : y - z ∈ B) :
    B ⊔ Submodule.span R {y} = B ⊔ Submodule.span R {z} := by
  have key : ∀ {y z : W}, y - z ∈ B → B ⊔ Submodule.span R {y} ≤ B ⊔ Submodule.span R {z} := by
    intro y z hyz
    refine sup_le le_sup_left ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
    have := add_mem (Submodule.mem_sup_left hyz : y - z ∈ B ⊔ Submodule.span R {z})
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))
    simpa using this
  exact le_antisymm (key hyz) (key (by simpa using B.neg_mem hyz))

section Line

variable {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem exists_gen (h1 : Module.finrank K W = 1) {B C : Submodule (𝓞 K) W}
    (hB : Submodule.IsFullLattice K B) (hBC : B ≤ C) (hC : C.FG) :
    ∃ y, C = B ⊔ Submodule.span (𝓞 K) {y} := by
  letI : StarRing K := starRingOfComm
  obtain ⟨t, ht, e⟩ := (LatticeGens.gens_and_count K W B C hBC
    (DiscOrder.idxN_ne_zero hB hC)).1 hC
  rw [h1] at ht
  obtain ⟨y, hy⟩ := Finset.card_le_one_iff_subset_singleton.1 ht
  rcases Finset.subset_singleton_iff.1 hy with rfl | rfl
  · exact ⟨0, by simpa using e⟩
  · exact ⟨y, by simpa using e⟩

theorem encard_between (h1 : Module.finrank K W = 1) {B : Submodule (𝓞 K) W}
    (hB : Submodule.IsFullLattice K B) (T : 𝓞 K) (hT : T ≠ 0) :
    {C : Submodule (𝓞 K) W | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B}.encard ≤
      ((Ideal.absNorm (Ideal.span {T}) : ℕ) : ℕ∞) := by
  set D : Submodule (𝓞 K) W := B.comap (LinearMap.lsmul (𝓞 K) W T) with hD
  have hTK : algebraMap (𝓞 K) K T ≠ 0 := by simpa using hT
  have hinj : Function.Injective (LinearMap.lsmul (𝓞 K) W T) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have : algebraMap (𝓞 K) K T • x = 0 := by rw [algebraMap_smul]; exact hx
    exact (smul_eq_zero.1 this).resolve_left hTK
  have hDfg : D.FG :=
    Submodule.fg_of_fg_map_injective _ hinj (hB.fg.of_le (Submodule.map_comap_le _ _))
  obtain ⟨y, hy⟩ := exists_gen h1 hB (fun x hx => B.smul_mem T hx : B ≤ D) hDfg
  have hyD : T • y ∈ B := by
    have : y ∈ D := by
      rw [hy]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    exact this
  let Φ : (𝓞 K ⧸ Ideal.span {T}) → Submodule (𝓞 K) W := fun q =>
    B ⊔ Submodule.span (𝓞 K) {(Quotient.out q : 𝓞 K) • y}
  have hsub : {C : Submodule (𝓞 K) W | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B} ⊆ Φ '' Set.univ := by
    rintro C ⟨hBC, hC⟩
    have hCD : C ≤ D := hC
    obtain ⟨c, hc⟩ := exists_gen h1 hB hBC (hDfg.of_le hCD)
    have hcD : c ∈ B ⊔ Submodule.span (𝓞 K) {y} := by
      rw [← hy]
      apply hCD
      rw [hc]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
    obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hcD
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨Ideal.Quotient.mk _ r, trivial, ?_⟩
    rw [hc]
    apply sup_span_congr
    have : Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) - r ∈ Ideal.span {T} := by
      rw [← Ideal.Quotient.eq]
      exact Ideal.Quotient.mk_out _
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 this
    have e : Quotient.out (Ideal.Quotient.mk (Ideal.span {T}) r) • y - (a + r • y) =
        k • (T • y) - a := by
      rw [smul_smul, hk, sub_smul]; abel
    rw [e]
    exact sub_mem (B.smul_mem k hyD) ha
  have hn : Ideal.absNorm (Ideal.span {T}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hT
  have hcard : Nat.card (𝓞 K ⧸ Ideal.span {T}) = Ideal.absNorm (Ideal.span {T}) :=
    (Ideal.absNorm_eq_natCard _).symm
  have : Finite (𝓞 K ⧸ Ideal.span {T}) := Nat.finite_of_card_ne_zero (by rwa [hcard])
  calc _ ≤ (Φ '' Set.univ).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set (𝓞 K ⧸ Ideal.span {T})).encard := Set.encard_image_le _ _
    _ = _ := by rw [Set.encard_univ, ENat.card_eq_coe_natCard, hcard]

end Line

theorem nondeg_of_pd {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hpd : PD h) : h.Nondegenerate := by
  have ha : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra h0
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpd τ x h0
    simp [hx] at this
  exact ⟨fun x hx => ha x (hx x), fun x hx => ha x (hx x)⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U) (B : Submodule (𝓞 K) (perp h U)) (T : 𝓞 K), T ≠ 0 → Module.finrank K (perp h U) = 1 → IsIntLat (hRes h U) A → IsIntLat (hRes h (perp h U)) B → {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧ latIn U L = A ∧ latIn (perp h U) L = B}.encard ≤ ((Ideal.absNorm (Ideal.span {T}) * discN (hRes h U) A : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hpd U A B T hT h1 hA hB
  obtain ⟨hc, hsU, hpU, -⟩ := (Witt.witt_definite K V h hK hs hpd).2 U
  obtain ⟨-, hsW, hpW, -⟩ := (Witt.witt_definite K V h hK hs hpd).2 (perp h U)
  have hd0 : discN (hRes h U) A ≠ 0 :=
    (DiscOrder.main K U (hRes h U) hK hsU (nondeg_of_pd _ hpU) A hA).1
  have dl := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K (perp h U) (hRes h (perp h U)) hsW (nondeg_of_pd _ hpW)
    star_algebraMap_ringOfIntegers_mem_range
  have horth : ∀ (u : U) (w : perp h U), h (u : V) (w : V) = 0 :=
    fun u w => (Witt.mem_perp h U w).1 w.2 u u.2
  have hdec : ∀ v : V, ∃ (u : U) (w : perp h U), v = u + w := by
    intro v
    have hv : v ∈ U ⊔ perp h U := by rw [hc.sup_eq_top]; trivial
    obtain ⟨u, hu, w, hw, e⟩ := Submodule.mem_sup.1 hv
    exact ⟨⟨u, hu⟩, ⟨w, hw⟩, e.symm⟩

  have hg : ∀ C : Submodule (𝓞 K) (perp h U), ∃ y : perp h U, B ≤ C → C.FG →
      C = B ⊔ Submodule.span (𝓞 K) {y} := by
    intro C
    by_cases hh : B ≤ C ∧ C.FG
    · obtain ⟨y, hy⟩ := exists_gen h1 hB.1 hh.1 hh.2
      exact ⟨y, fun _ _ => hy⟩
    · exact ⟨0, fun a b => absurd ⟨a, b⟩ hh⟩
  choose g hg using hg
  set Ad : Submodule (𝓞 K) U := dual (hRes h U) A with hAd
  let M : Submodule (𝓞 K) V := A.map (U.subtype.restrictScalars (𝓞 K)) ⊔
    B.map ((perp h U).subtype.restrictScalars (𝓞 K))
  let Φ : Submodule (𝓞 K) (perp h U) × (Ad ⧸ A.comap Ad.subtype) → Submodule (𝓞 K) V := fun p =>
    M ⊔ Submodule.span (𝓞 K) {(((Quotient.out p.2 : Ad) : U) : V) +
      (g (dual (hRes h (perp h U)) p.1) : V)}
  let S : Set (Submodule (𝓞 K) (perp h U)) := {C | B ≤ C ∧ ∀ x ∈ C, T • x ∈ B}
  have hsub : {L : Submodule (𝓞 K) V | IsIntLat h L ∧ (∀ x ∈ dual h L, T • x ∈ L) ∧
      latIn U L = A ∧ latIn (perp h U) L = B} ⊆ Φ '' (S ×ˢ Set.univ) := by
    rintro L ⟨hL, hTL, hLA, hLB⟩
    have mA : ∀ u : U, u ∈ A ↔ (u : V) ∈ L := fun u => by rw [← hLA]; rfl
    have mB : ∀ w : perp h U, w ∈ B ↔ (w : V) ∈ L := fun w => by rw [← hLB]; rfl
    let π : V →ₗ[𝓞 K] perp h U :=
      (Submodule.projectionOnto (perp h U) U hc.symm).restrictScalars (𝓞 K)
    have hπ : ∀ (u : U) (w : perp h U), π ((u : V) + (w : V)) = w := by
      intro u w
      simp only [π, LinearMap.restrictScalars_apply, map_add (f := _)]
      rw [Submodule.projectionOnto_apply_right, Submodule.projectionOnto_apply_left, zero_add]
    set B' := L.map π with hB'
    have mB' : ∀ w : perp h U, w ∈ B' ↔ ∃ u : U, (u : V) + (w : V) ∈ L := by
      intro w
      constructor
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨u, w, rfl⟩ := hdec v
        exact ⟨u, by rw [hπ]; exact hv⟩
      · rintro ⟨u, hu⟩
        exact ⟨_, hu, hπ u w⟩
    have hBB' : B ≤ B' := fun w hw => (mB' w).2 ⟨0, by simpa using (mB w).1 hw⟩
    have hB'fg : B'.FG := hL.1.fg.map π
    have hB'l : Submodule.IsFullLattice K B' := by
      letI := hB.1
      exact Submodule.IsFullLattice.of_le_of_fg K hBB' hB'fg
    have mC : ∀ x : perp h U, x ∈ dual (hRes h (perp h U)) B' ↔ (x : V) ∈ dual h L := by
      intro x
      rw [dualBasic_mem_dual, dualBasic_mem_dual]
      constructor
      · intro H v hv
        obtain ⟨u, w, rfl⟩ := hdec v
        have := H w ((mB' w).2 ⟨u, hv⟩)
        rw [map_add (f := _), LinearMap.add_apply, horth, zero_add]
        exact this
      · intro H w hw
        obtain ⟨u, hu⟩ := (mB' w).1 hw
        have := H _ hu
        rw [map_add (f := _), LinearMap.add_apply, horth, zero_add] at this
        exact this
    have hgen := hg B' hBB' hB'fg
    obtain ⟨a, ha⟩ := (mB' (g B')).1
      (hgen.ge (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
    have haA : a ∈ Ad := by
      rw [hAd, dualBasic_mem_dual]
      intro u hu
      have := hL.2 _ ((mA u).1 hu) _ ha
      rw [map_add (f := _), horth, add_zero] at this
      exact this
    refine ⟨(dual (hRes h (perp h U)) B', Submodule.Quotient.mk ⟨a, haA⟩), ⟨⟨?_, ?_⟩, trivial⟩, ?_⟩
    · intro w hw
      rw [mC, dualBasic_mem_dual]
      exact fun v hv => hL.2 v hv _ ((mB w).1 hw)
    · intro x hx
      rw [mB]
      exact hTL _ ((mC x).1 hx)
    · have hML : M ≤ L := by
        refine sup_le ?_ ?_
        · rintro _ ⟨u, hu, rfl⟩; exact (mA u).1 hu
        · rintro _ ⟨u, hu, rfl⟩; exact (mB u).1 hu
      have e1 : L = M ⊔ Submodule.span (𝓞 K) {(a : V) + (g B' : V)} := by
        refine le_antisymm ?_ (sup_le hML ((Submodule.span_singleton_le_iff_mem _ _).2 ha))
        intro v hv
        obtain ⟨u, w, rfl⟩ := hdec v
        obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.1 (hgen.le ((mB' w).2 ⟨u, hv⟩))
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
        have e : (u : V) + ((b + r • g B' : perp h U) : V) =
            (((u - r • a : U) : V) + (b : V)) + r • ((a : V) + (g B' : V)) := by
          simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul_of_tower, smul_add]
          abel
        have hu : u - r • a ∈ A := by
          rw [mA]
          have := sub_mem (sub_mem hv (L.smul_mem r ha)) ((mB b).1 hb)
          rw [e] at this
          simpa using this
        rw [e]
        exact add_mem (Submodule.mem_sup_left (add_mem (Submodule.mem_sup_left ⟨_, hu, rfl⟩)
          (Submodule.mem_sup_right ⟨_, hb, rfl⟩)))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      simp only [Φ]
      rw [(dl B' hB'l).2.1, e1]
      apply sup_span_congr
      have hq : Quotient.out (Submodule.Quotient.mk ⟨a, haA⟩ : Ad ⧸ A.comap Ad.subtype) - ⟨a, haA⟩ ∈
          A.comap Ad.subtype := by
        rw [← Submodule.Quotient.eq]
        exact Submodule.Quotient.mk_out _
      rw [add_sub_add_right_eq_sub]
      exact Submodule.mem_sup_left ⟨_, hq, rfl⟩
  have hcard : Nat.card (Ad ⧸ A.comap Ad.subtype) = discN (hRes h U) A := rfl
  have : Finite (Ad ⧸ A.comap Ad.subtype) := Nat.finite_of_card_ne_zero (by rwa [hcard])
  calc _ ≤ (Φ '' (S ×ˢ Set.univ)).encard := Set.encard_le_encard hsub
    _ ≤ (S ×ˢ (Set.univ : Set (Ad ⧸ A.comap Ad.subtype))).encard := Set.encard_image_le _ _
    _ = S.encard * (discN (hRes h U) A : ℕ) := by
      rw [Set.encard_prod, Set.encard_univ, ENat.card_eq_coe_natCard, hcard]
    _ ≤ _ := by
      rw [Nat.cast_mul]
      gcongr
      exact encard_between h1 hB.1 T hT

end GlobalTheory.Mass.LineGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSublatticesQuotientProdDegreeOnePrimesStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_sublattices_quotient_prod_degree_one_primes : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), Submodule.IsFullLattice K M → ∀ (T : ℕ) (s : Finset (Ideal (𝓞 K))), T.Prime → (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) → {L : Submodule (𝓞 K) V | L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))}.encard = (((∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  first
  | exact @GlobalTheory.SublatCount.main
  | intro K V _ _ _ _ _ _ _ M hM T s hT hs
    exact GlobalTheory.SublatCount.main K V M hM.toIsLattice T s hT hs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolumeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ Λ, IsLat L Λ → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧ (S.St ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.K0 ≠ 0 ∧ ∀ h ∈ S.St, S.mu (h • Λ) = S.mu Λ) ∧ ∀ C, S.IsCls C → S.K0.relIndex (S.St ⊓ MulAction.stabilizer S.GLV C) ≠ 0 ∧ (S.St ⊓ MulAction.stabilizer S.GLV C).relIndex S.K0 ≠ 0 ∧ 1 ≤ S.wC C ∧ ∀ h ∈ S.St, S.wC (h • C) = S.wC C := by
  first | exact @GlobalTheory.HL.volSt | exact GlobalTheory.HL.volSt | (intros; apply GlobalTheory.HL.volSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DedekindZetaResidueLeSixteenLogRootDiscrPow
section
open MeasureTheory NumberField Finset

namespace GlobalTheory

theorem residue_rankin_numeric (x : ℝ) (hx : (3 / 2 : ℝ) ≤ x) (f : ℕ) :
    0 < Real.log x ∧
    (2 * Real.pi) ^ f * ((x ^ f) ^ (1 + 1 / Real.log x) *
      ((1 + 1 / Real.log x) / ((1 + 1 / Real.log x) - 1)) ^ (2 * f))
      ≤ (16 * Real.log x) ^ (2 * f) * x ^ f := by
  have hx0 : 0 < x := by linarith
  have hL : (2 / 5 : ℝ) ≤ Real.log x := by
    have h1 := Real.le_log_one_add_of_nonneg (x := (1 / 2 : ℝ)) (by norm_num)
    have h2 : Real.log (1 + 1 / 2) ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    norm_num at h1 h2 ⊢
    linarith
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  refine ⟨hL0, ?_⟩
  have e1 : (1 + 1 / L) / ((1 + 1 / L) - 1) = 1 + L := by
    rw [add_sub_cancel_left]; field_simp; ring
  have e2 : (x ^ f) ^ (1 + 1 / L) = x ^ f * Real.exp 1 ^ f := by
    rw [Real.rpow_add (pow_pos hx0 f), Real.rpow_one, Real.rpow_def_of_pos (pow_pos hx0 f),
      Real.log_pow, ← hLdef, ← Real.exp_nat_mul]
    congr 2
    field_simp
  rw [e1, e2, pow_mul, pow_mul]
  have hb : 2 * Real.pi * Real.exp 1 * (1 + L) ^ 2 ≤ (16 * L) ^ 2 := by
    have hpi := Real.pi_lt_d2
    have he := Real.exp_one_lt_d9
    have hp0 := Real.pi_pos
    have he0 := Real.exp_pos 1
    have h3 : 2 * Real.pi * Real.exp 1 ≤ 18 := by nlinarith
    have h4 : (1 + L) ^ 2 ≤ (7 / 2 * L) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    calc 2 * Real.pi * Real.exp 1 * (1 + L) ^ 2 ≤ 18 * (7 / 2 * L) ^ 2 :=
          mul_le_mul h3 h4 (by positivity) (by norm_num)
      _ ≤ (16 * L) ^ 2 := by nlinarith [sq_nonneg L]
  have hc := pow_le_pow_left₀ (by positivity) hb f
  calc (2 * Real.pi) ^ f * (x ^ f * Real.exp 1 ^ f * ((1 + L) ^ 2) ^ f)
      = (2 * Real.pi * Real.exp 1 * (1 + L) ^ 2) ^ f * x ^ f := by
        rw [mul_pow (2 * Real.pi * Real.exp 1), mul_pow (2 * Real.pi)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

theorem dedekindZeta_residue_le_log_rootDiscr_pow :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      0 < dedekindZeta_residue K ∧ dedekindZeta_residue K ≤
        (16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv K)) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  intro K _ _ hK
  refine ⟨dedekindZeta_residue_pos K, ?_⟩
  obtain ⟨hn, -, hx, hd⟩ := _root_.GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex K hK
  obtain ⟨hL0, hnum⟩ := residue_rankin_numeric _ hx (Formalism.HermitianLatticesTheory.fDeg K)
  set x := 2 * Formalism.HermitianLatticesTheory.vInv K with hxdef
  have hx0 : 0 < x := by linarith
  have hHR := _root_.GlobalTheory.classNumber_mul_regulator_le_sqrt_discr_rpow K hK (1 + 1 / Real.log x) (by
    have : 0 < 1 / Real.log x := by positivity
    linarith)
  have hr : InfinitePlace.nrRealPlaces K = 0 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have hc : InfinitePlace.nrComplexPlaces K = Formalism.HermitianLatticesTheory.fDeg K := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  have hw : (1 : ℝ) ≤ (Units.torsionOrder K : ℝ) := by
    exact_mod_cast Units.torsionOrder_pos K
  rw [hn, hd] at hHR
  rw [dedekindZeta_residue_def, hr, hc, hd, div_le_iff₀ (by positivity)]
  have hp : 0 < (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  have hq : 0 ≤ (16 * Real.log x) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) * x ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  calc (2 : ℝ) ^ 0 * (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K * Units.regulator K * (classNumber K : ℝ)
      = (2 * Real.pi) ^ Formalism.HermitianLatticesTheory.fDeg K * ((classNumber K : ℝ) * Units.regulator K) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hHR hp.le
    _ ≤ _ := hnum
    _ ≤ _ := by nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteUnitaryStabilizerSubspaceProdStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_unitary_stabilizer_subspace_prod : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ U : Submodule K V, ∃ φ : MulAction.stabilizer (isom h) U ≃* isom (hRes h U) × isom (hRes h (perp h U)), ∀ (γ : MulAction.stabilizer (isom h) U) (L : Submodule (𝓞 K) V), latIn U (γ • L) = (φ γ).1 • latIn U L ∧ latIn (perp h U) (γ • L) = (φ γ).2 • latIn (perp h U) L := by
  first | exact @GlobalTheory.Mass.StabSplit.main | exact GlobalTheory.Mass.StabSplit.main | (intros; apply GlobalTheory.Mass.StabSplit.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIdealCoprimeConjMulEqSpanSingleton
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_ideal_coprime_conj_mul_eq_spanSingleton :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
      Formalism.BasicNotions.CMData F E → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 →
      ∀ N : 𝓞 E, N ≠ 0 → ∃ P : Ideal (𝓞 E), P ≠ ⊥ ∧
        P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) = ⊤ ∧
        (∃ t : 𝓞 E, ∃ p ∈ P, t * N + p = 1) ∧
        ∃ α : E, (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) α := by
  intro F E _ _ _ _ _ _ hcm c hc N hN
  obtain ⟨a, hac, hQ, hp⟩ := _root_.GlobalTheory.exists_mem_fractionalIdeal_primitive_local_generator F E hcm.deg2 c hc N hN

  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨p, hpm⟩ := Ideal.exists_maximal (𝓞 F)
    exact hp p hpm (Submodule.zero_mem _)

  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a * c⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hc]
    exact mul_le_mul' (FractionalIdeal.spanSingleton_le_iff_mem.mpr hac) le_rfl
  obtain ⟨P, hP⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hPc : (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a := by
    rw [hP, mul_assoc, inv_mul_cancel₀ hc, mul_one]

  have key : ∀ Q : Ideal (𝓞 E), P ≤ Q → a ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
    intro Q hPQ
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← hPc]
    exact mul_le_mul' ((FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hPQ) le_rfl
  have hσσ : ∀ x : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E)
      (RingOfIntegers.mapRingHom (starRingEnd E) x) = x := by
    intro x
    ext
    simp
  refine ⟨P, ?_, ?_, ?_, a, hPc⟩
  · rintro rfl
    apply ha
    rw [FractionalIdeal.coeIdeal_bot, zero_mul, eq_comm,
      FractionalIdeal.spanSingleton_eq_zero_iff] at hPc
    exact hPc
  · by_contra htop
    obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
    have h1 : P ≤ Q := le_sup_left.trans hPQ
    have h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E)) := by
      intro x hx
      apply hPQ (Ideal.mem_sup_right _)
      show RingOfIntegers.mapRingHom (starRingEnd E) (RingOfIntegers.mapRingHom (starRingEnd E) x) ∈ P
      rw [hσσ]
      exact hx
    have h3 := GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData F E hcm P Q hQm h1 h2
    have hpm : (Q.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := 𝓞 F) Q
    exact hp _ hpm (key _ h3)
  · have htop : P ⊔ Ideal.span {N} = ⊤ := by
      by_contra htop
      obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
      exact hQ Q hQm (hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self N)))
        (key Q (le_sup_left.trans hPQ))
    have h1 : (1 : 𝓞 E) ∈ P ⊔ Ideal.span {N} := htop ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact ⟨t, y, hy, by rw [add_comm]; exact hyz⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMovesKernelCommonStabilizerSmulEqStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMovesKernel_commonStabilizer_smul_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (β J βJ : ℕ) (Λ₁ : Submodule L.O S.V), ∀ h ∈ S.St, S.kern β J βJ d (h • Λ) (h • Λ₁) = S.kern β J βJ d Λ Λ₁ := by
  first | exact @GlobalTheory.HL.kern_smul_eq | exact GlobalTheory.HL.kern_smul_eq | (intros; apply GlobalTheory.HL.kern_smul_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → discN h M ≠ 0 ∧ (discN h M = 1 ↔ IsUnimodular h M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → idxN M' M ≠ 0 ∧ discN h M = discN h M' * idxN M' M ^ 2) ∧ (∀ N ∈ genus h M, IsIntLat h N ∧ discN h N = discN h M) ∧ (∀ P : Ideal (𝓞 K), P.IsMaximal → ((discN h M : ℕ) : 𝓞 K) ∉ P → IsUnimodularAt h P M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P M → loc (K := K) P M = loc (K := K) P M') := by
  first | exact @GlobalTheory.Mass.DiscOrder.main | exact GlobalTheory.Mass.DiscOrder.main | (intros; apply GlobalTheory.Mass.DiscOrder.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminanStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalHermitianLattice_local_structure_discriminant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → (badP h M).Finite ∧ discN h M = ∏ᶠ P ∈ badP h M, Ideal.absNorm P ∧ Nonempty ((↥(dual h M) ⧸ M.comap (dual h M).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ᶠ P ∈ badP h M, P)) ∧ ∀ P ∈ badP h M, conjIdeal (K := K) P = P ∧ 2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2 ∧ ∃ x ∈ M, (∃ a : 𝓞 K, (a : K) = h x x ∧ a ∈ P ∧ a ∉ P ^ 2) ∧ ∀ y ∈ loc (K := K) P (dual h M), ∃ c ∈ locR (K := K) P, y - (c * (h x x)⁻¹) • x ∈ loc (K := K) P M := by
  first | exact @GlobalTheory.MaxLatStruct.main | exact GlobalTheory.MaxLatStruct.main | (intros; apply GlobalTheory.MaxLatStruct.main <;> assumption)
end

