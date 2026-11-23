module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverRelationUniqueness
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassPairingClassBounds
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem tsum_subtype_and_eq_ite {α : Type*} (S : Set α) (p q : α → Prop) (f : α → ℝ≥0∞)
    (h : ∀ t ∈ S, p t ↔ q t) :
    (∑' t : {t // t ∈ S ∧ p t}, f t.1) = ∑' t : S, (if q t.1 then f t.1 else 0) := by

  have hL : (∑' t : {t // t ∈ S ∧ p t}, f t.1) = ∑' t, ({t | t ∈ S ∧ p t} : Set α).indicator f t :=
    tsum_subtype {t | t ∈ S ∧ p t} f
  have hR : (∑' t : S, (if q t.1 then f t.1 else 0)) =
      ∑' t, S.indicator (fun t => if q t then f t else 0) t :=
    tsum_subtype S (fun t => if q t then f t else 0)
  rw [hL, hR]
  refine tsum_congr fun t => ?_
  by_cases hS : t ∈ S
  · have hpq := h t hS
    rw [Set.indicator_of_mem hS]
    by_cases hq : q t
    · rw [if_pos hq, Set.indicator_of_mem (show t ∈ {t | t ∈ S ∧ p t} from ⟨hS, hpq.2 hq⟩)]
    · rw [if_neg hq]
      exact Set.indicator_apply_eq_zero.mpr (fun (hm : t ∈ {t | t ∈ S ∧ p t}) =>
        absurd (hpq.1 hm.2) hq)
  · rw [Set.indicator_apply_eq_zero.mpr (fun (hm : t ∈ {t | t ∈ S ∧ p t}) =>
      absurd hm.1 hS), Set.indicator_apply_eq_zero.mpr (fun (hm : t ∈ S) => absurd hm hS)]

theorem mass_pairingClass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), (∃ t0 : Term V M r, LocNG.IsTermOver P d0 t0) → ∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat t.f t.f' ∈ c1 → ∀ g : ℝ≥0∞, g = (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) → 0 < g ∧ g ≠ ⊤ ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hdim hrel R d0 hd0 d t hdt Y0 c1 hc1 ht g hg
  obtain ⟨t0, ht0⟩ := hd0

  let Cl : Term V M r → Prop := fun t' => ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t'.f j = ∑ i, A i j • s (t.f i)) ∧ ∀ j, t'.f' j = ∑ i, A' i j • s (t.f' i)

  have hCl : ∀ (d' : LocNG.Datum P) (t' : Term V M r), LocNG.IsTermOver P d' t' →
      (H.Zhat t'.f t'.f' ∈ c1 ↔ Cl t') := fun d' t' h' =>
    _root_.GlobalTheory.HL.PairingClass.mem_class_iff M hM H r k P hdim hrel d d' t t' hdt h' Y0 c1 hc1 ht

  have hg' : g = ∑' d' : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d'.1) *
      ∑' t' : {t' // t' ∈ R.RT d'.1 ∧ ¬ LocNG.BBne (H := H) t' ∧ Cl t'},
        ENNReal.ofReal (LocNG.mu P t'.1) := by
    rw [hg]
    refine tsum_congr fun d' => ?_
    congr 1
    have e := tsum_subtype_and_eq_ite (R.RT d'.1) (fun t' => ¬ LocNG.BBne (H := H) t' ∧ Cl t')
      (fun t' => ¬ LocNG.BBne (H := H) t' ∧ H.Zhat t'.f t'.f' ∈ c1)
      (fun t' => ENNReal.ofReal (LocNG.mu P t'))
      (fun t' ht' => and_congr_right fun _ => (hCl d'.1 t' ((R.hRT d'.1).1 ht')).symm)
    convert e.symm
  obtain ⟨hne, hle, hprime, hpos⟩ :=
    GlobalTheory.T.hermitian_total_mass_le_generic_mass M hM H r k P hk hdim hrel R d0 d t hdt Cl (fun _ => Iff.rfl) g hg'
  exact ⟨pos_iff_ne_zero.mpr (hpos ⟨t0, ht0⟩), hne, hprime, hle⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitStabilizerMassSubspaceCyclicDiscriminantLe
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.FixedSub

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_def' (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) :
    g • L = gmap (g : V ≃ₗ[K] V) L := rfl

theorem isIntLat_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V)
    (hL : IsIntLat h L) : IsIntLat h (g • L) := by
  have H := isomAct (𝓞 K) K V h g g.2 L
  refine ⟨{ toIsLattice := H.2.2.2.2.2 hL.1.toIsLattice, span_eq_top := ?_ },
    H.2.2.1.2 hL.2⟩
  change Submodule.span K ((g : V ≃ₗ[K] V).toLinearMap '' (L : Set V)) = ⊤
  rw [← Submodule.map_span, hL.1.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem dual_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) :
    dual h (g • L) = g • dual h L := (isomAct (𝓞 K) K V h g g.2 L).1

theorem discN_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) :
    discN h (g • L) = discN h L := by
  unfold discN
  rw [dual_smul]
  unfold idxN
  exact AddSubgroup.relIndex_map_map_of_injective (f := ((g : V ≃ₗ[K] V) : V →+ V))
    L.toAddSubgroup (dual h L).toAddSubgroup (g : V ≃ₗ[K] V).injective

theorem stable_latsDisc (h : V →ₗ⋆[K] V →ₗ[K] K) (n : ℕ) :
    Stable (isom h) (latsDisc (R := 𝓞 K) h n) := fun g L hL =>
  ⟨isIntLat_smul h g L hL.1, (discN_smul h g L).trans hL.2⟩

theorem gens_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule (𝓞 K) V) (e : ℕ)
    (H : ∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V)) :
    ∃ t : Finset V, t.card ≤ e ∧ dual h (g • L) = g • L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  obtain ⟨t, ht, H⟩ := H
  refine ⟨t.image (g : V ≃ₗ[K] V), Finset.card_image_le.trans ht, ?_⟩
  rw [dual_smul, H, smul_def', smul_def']
  unfold gmap
  rw [Submodule.map_sup, Submodule.map_span, Finset.coe_image]
  rfl

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem hRes_symm (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (U : Submodule K V) :
    (hRes h U).IsSymm := ⟨fun x y => hs.eq (x : V) (y : V)⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem hRes_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) (U : Submodule K V) :
    PD (hRes h U) := fun τ x hx => hp τ (x : V) (fun e => hx (Subtype.ext e))

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem pd_nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  constructor
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this
  · intro x hx
    by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

omit [NumberField K] in
theorem star_int (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K r)) :=
    (RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨_, this⟩, rfl⟩

theorem gens_rank [FiniteDimensional K V] (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (hp : PD h) (L : Submodule (𝓞 K) V) (hL : IsIntLat h L) :
    ∃ t : Finset V, t.card ≤ Module.finrank K V ∧
      dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  have hnd := pd_nondeg h hp
  have h0 := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd L hL).1
  have hle : L ≤ dual h L := fun x hx => (isomAct_mem_dual h L x).2 fun y hy => hL.2 y hy x hx
  exact (_root_.GlobalTheory.Mass.LatticeGens.gens_and_count K V L (dual h L) hle h0).1
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs hnd star_int L hL.1).1.fg

end

theorem orbMass_stabilizer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (U : Submodule K V) (n N₀ : ℕ), orbMass (MulAction.stabilizer (isom h) U) {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧ (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧ discN (hRes h U) (latIn U L) = n} ≤ orbMass (isom (hRes h U)) (latsDisc (R := 𝓞 K) (hRes h U) n) * (∑ n' ∈ Finset.Icc 1 (n * N₀), orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n')) * (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp U n N₀
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.definite_unitary_stabilizer_subspace_prod K V h hK hs hp U
  have hs1 := hRes_symm h hs U
  have hp1 := hRes_pd h hp U
  have hs2 := hRes_symm h hs (perp h U)
  have hp2 := hRes_pd h hp (perp h U)
  letI act : MulAction (MulAction.stabilizer (isom h) U)
      (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)) :=
    { smul := fun γ p => ((φ γ).1 • p.1, (φ γ).2 • p.2)
      one_smul := fun p => by
        change ((φ 1).1 • p.1, (φ 1).2 • p.2) = p
        simp
      mul_smul := fun a b p => by
        change ((φ (a * b)).1 • p.1, (φ (a * b)).2 • p.2) =
          ((φ a).1 • ((φ b).1 • p.1), (φ a).2 • ((φ b).2 • p.2))
        simp [mul_smul] }
  have hact : ∀ (γ : MulAction.stabilizer (isom h) U)
      (p : Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U)),
      γ • p = ((φ γ).1 • p.1, (φ γ).2 • p.2) := fun _ _ => rfl
  set X : Set (Submodule (𝓞 K) V) := {L : Submodule (𝓞 K) V | IsIntLat h L ∧ discN h L = N₀ ∧
    (∃ t : Finset V, t.card ≤ 1 ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) ∧
    discN (hRes h U) (latIn U L) = n} with hX
  set A : Set (Submodule (𝓞 K) U) := latsDisc (R := 𝓞 K) (hRes h U) n with hA
  set B : Set (Submodule (𝓞 K) (perp h U)) :=
    ⋃ n' ∈ Finset.Icc 1 (n * N₀), latsDisc (R := 𝓞 K) (hRes h (perp h U)) n' with hB
  have memB : ∀ M, M ∈ B ↔ IsIntLat (hRes h (perp h U)) M ∧
      1 ≤ discN (hRes h (perp h U)) M ∧ discN (hRes h (perp h U)) M ≤ n * N₀ := by
    intro M
    simp only [hB, Set.mem_iUnion, Finset.mem_Icc, latsDisc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, h1, rfl⟩
      exact ⟨h1, hi⟩
    · rintro ⟨h1, hi⟩
      exact ⟨_, hi, h1, rfl⟩
  have sA : Stable (isom (hRes h U)) A := stable_latsDisc _ n
  have sB : Stable (isom (hRes h (perp h U))) B := by
    intro g M hM
    rw [memB] at hM ⊢
    rw [discN_smul]
    exact ⟨isIntLat_smul _ g M hM.1, hM.2⟩
  have fA : ∀ M ∈ A, Finite (MulAction.stabilizer (isom (hRes h U)) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K U (hRes h U) hK hs1 hp1 M hM.1.1).2.2.2.1 M hM.1.1
  have fB : ∀ M ∈ B, Finite (MulAction.stabilizer (isom (hRes h (perp h U))) M) := fun M hM =>
    (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K (perp h U) (hRes h (perp h U)) hK hs2 hp2 M ((memB M).1 hM).1.1).2.2.2.1 M
      ((memB M).1 hM).1.1
  have sX : Stable (MulAction.stabilizer (isom h) U) X := by
    rintro γ L ⟨h1, h2, h3, h4⟩
    refine ⟨isIntLat_smul h γ.1 L h1, (discN_smul h γ.1 L).trans h2, gens_smul h γ.1 L 1 h3, ?_⟩
    rw [(hφ γ L).1, discN_smul, h4]
  have sY : Stable (MulAction.stabilizer (isom h) U) (A ×ˢ B) := by
    rintro γ p ⟨h1, h2⟩
    exact ⟨sA _ _ h1, sB _ _ h2⟩
  have mp : Set.MapsTo (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) X (A ×ˢ B) := by
    rintro L ⟨h1, h2, h3, h4⟩
    obtain ⟨k1, k2, k3, -⟩ := _root_.GlobalTheory.Mass.PrimDisc.main K V h hK hs hp L U 1 h1 h3
    refine ⟨⟨k1, h4⟩, (memB _).2 ⟨k2, ?_, ?_⟩⟩
    · exact Nat.one_le_iff_ne_zero.2
        (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K (perp h U) _ hK hs2 (pd_nondeg _ hp2) _ k2).1
    · rw [h2, h4] at k3
      exact k3
  have fY : ∀ p ∈ A ×ˢ B, Finite (MulAction.stabilizer (MulAction.stabilizer (isom h) U) p) := by
    rintro p ⟨h1, h2⟩
    haveI := fA _ h1
    haveI := fB _ h2
    refine Finite.of_injective
      (β := MulAction.stabilizer (isom (hRes h U)) p.1 ×
        MulAction.stabilizer (isom (hRes h (perp h U))) p.2)
      (fun γ => (⟨(φ γ.1).1, congrArg Prod.fst γ.2⟩, ⟨(φ γ.1).2, congrArg Prod.snd γ.2⟩)) ?_
    intro a b e
    apply Subtype.ext
    apply φ.injective
    exact Prod.ext (congrArg (fun q => q.1.1) e) (congrArg (fun q => q.2.1) e)
  have e1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (MulAction.stabilizer (isom h) U) _ _ X (A ×ˢ B)
    (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L))
    (fun γ L => Prod.ext (hφ γ L).1 (hφ γ L).2) sX sY mp fY
  have e2 := _root_.GlobalTheory.Mass.ProdMass.orbMass_prod (MulAction.stabilizer (isom h) U) _ _ _ _ φ A B hact sA sB fA fB
  have e3 : orbMass (isom (hRes h (perp h U))) B ≤ ∑ n' ∈ Finset.Icc 1 (n * N₀),
      orbMass (isom (hRes h (perp h U))) (latsDisc (R := 𝓞 K) (hRes h (perp h U)) n') :=
    (_root_.GlobalTheory.Mass.OrbMono.main (isom (hRes h (perp h U))) (Submodule (𝓞 K) (perp h U))).2.2.1 ℕ _ B _ _ subset_rfl
  obtain ⟨m1, m2, -⟩ := _root_.GlobalTheory.Mass.OrbMono.main (MulAction.stabilizer (isom h) U)
    (Submodule (𝓞 K) U × Submodule (𝓞 K) (perp h U))
  rw [e1]
  refine (m1 _ (A ×ˢ B) _
    (fun _ => (((n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) : ℕ) : ℝ≥0∞))
    subset_rfl ?_).trans ?_
  · rintro ⟨M, M'⟩ ⟨h1, h2⟩
    rcases (X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹'
      {(M, M')}).eq_empty_or_nonempty with h0 | ⟨L, ⟨l1, l2, l3, l4⟩, hL⟩
    · simp [h0]
    · have eM : latIn U L = M := congrArg Prod.fst hL
      obtain ⟨b1, b2, b3⟩ := (memB M').1 h2
      have g1 := (_root_.GlobalTheory.Mass.PrimDisc.main K V h hK hs hp L U 1 l1 l3).2.2.2
      rw [eM] at g1
      have g2 := gens_rank hK _ hs2 hp2 M' b1
      have cnt := GlobalTheory.T.card_hermitianLattices_glued_subspace_complement K V h hK hs hp U M M' _ _ h1.1 b1 g1 g2
      have sub : X ∩ (fun L : Submodule (𝓞 K) V => (latIn U L, latIn (perp h U) L)) ⁻¹' {(M, M')} ⊆
          {L : Submodule (𝓞 K) V | IsIntLat h L ∧ latIn U L = M ∧ latIn (perp h U) L = M'} :=
        fun N hN => ⟨hN.1.1, congrArg Prod.fst hN.2, congrArg Prod.snd hN.2⟩
      have le : (discN (hRes h U) M * discN (hRes h (perp h U)) M') ^
          (Module.finrank K (perp h U) + 1 + Module.finrank K (perp h U)) ≤
          (n * (n * N₀)) ^ (2 * Module.finrank K (perp h U) + 1) := by
        have e : discN (hRes h U) M = n := h1.2
        rw [e, show Module.finrank K (perp h U) + 1 + Module.finrank K (perp h U) =
          2 * Module.finrank K (perp h U) + 1 by ring]
        exact Nat.pow_le_pow_left (Nat.mul_le_mul_left n b3) _
      have fin := ((Set.encard_le_encard sub).trans cnt).trans (Nat.cast_le.2 le)
      have := ENat.toENNReal_le.2 fin
      rwa [ENat.toENNReal_coe] at this
  · rw [m2, e2, mul_comm]
    gcongr

end GlobalTheory.Mass.FixedSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedDegreeOneOfNcardPlacesOver
section
open NumberField IsDedekindDomain

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.splitPrime_liesOver_span_iff {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] :
    P.LiesOver (Ideal.span {(p : ℤ)}) ↔ ((p : ℕ) : 𝓞 E) ∈ P := by
  rw [Ideal.liesOver_iff]
  constructor
  · intro h
    have hmem : (p : ℤ) ∈ Ideal.under ℤ P := h ▸ Ideal.subset_span rfl
    simpa [Ideal.under, Ideal.mem_comap] using hmem
  · intro h
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine hmax.eq_of_le (inferInstance : (Ideal.under ℤ P).IsPrime).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa [Ideal.under, Ideal.mem_comap] using h


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.unramified_degree_one_of_ncard_placesOver (E : Type) [Field E] [NumberField E] (p : ℕ)
    (hp : p.Prime) (h : (_root_.Formalism.BasicNotions.placesOver E p).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∈ _root_.Formalism.BasicNotions.placesOver E p) :
    ((p : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 ∧ v.asIdeal.ramificationIdx ℤ = 1 ∧
      v.asIdeal.inertiaDeg ℤ = 1 := by
  set q : Ideal ℤ := Ideal.span {(p : ℤ)} with hq
  haveI hqmax : q.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hqbot : q ≠ ⊥ := by
    rw [hq, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmemv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
    unfold _root_.Formalism.BasicNotions.placesOver at hv
    exact hv
  haveI : v.asIdeal.LiesOver q := (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp v.asIdeal).2 hmemv
  have hcard : (IsDedekindDomain.primesOverFinset q (𝓞 E)).card = Module.finrank ℚ E := by
    rw [← h, ← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hqbot]
    have himage : (fun w : HeightOneSpectrum (𝓞 E) => w.asIdeal) '' _root_.Formalism.BasicNotions.placesOver E p =
        q.primesOver (𝓞 E) := by
      ext P
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hw' : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
          unfold _root_.Formalism.BasicNotions.placesOver at hw
          exact hw
        exact ⟨w.isPrime, (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp w.asIdeal).2 hw'⟩
      · rintro ⟨hPp, hPl⟩
        have hPmem : ((p : ℕ) : 𝓞 E) ∈ P := (_root_.GlobalTheory.splitPrime_liesOver_span_iff hp P).1 hPl
        have hPbot : P ≠ ⊥ := by
          intro hb
          rw [hb, Ideal.mem_bot] at hPmem
          exact hp.ne_zero (by exact_mod_cast hPmem)
        refine ⟨⟨P, hPp, hPbot⟩, ?_, rfl⟩
        unfold _root_.Formalism.BasicNotions.placesOver
        exact hPmem
    rw [← himage, Set.ncard_image_of_injective _ (fun a b hab => HeightOneSpectrum.ext hab)]
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) ℚ E (p := q) hqbot
  rw [← hcard, Finset.card_eq_sum_ones] at hsum
  have hpos : ∀ P ∈ IsDedekindDomain.primesOverFinset q (𝓞 E),
      1 ≤ q.ramificationIdx' P * q.inertiaDeg' P := by
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff hqbot] at hP
    obtain ⟨hPp, hPl⟩ := hP
    haveI := hPp
    haveI := hPl
    have he : q.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hqbot
    have hf : 0 < q.inertiaDeg' P := Ideal.inertiaDeg'_pos' q P
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero he hf.ne')
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 hsum.symm
  have hvmem : v.asIdeal ∈ IsDedekindDomain.primesOverFinset q (𝓞 E) := by
    rw [IsDedekindDomain.mem_primesOverFinset_iff hqbot]
    exact ⟨v.isPrime, inferInstance⟩
  obtain ⟨he, hf⟩ := mul_eq_one.1 (hall _ hvmem).symm
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  refine ⟨?_, ?_, ?_⟩
  · intro hsq
    have hle : Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ 2 := by
      rw [hq, Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
      simpa using hsq
    unfold Ideal.ramificationIdx' at he
    by_cases hb : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ n}
    · have h2 := le_csSup hb (show 2 ∈ {n | Ideal.map (algebraMap ℤ (𝓞 E)) q ≤ v.asIdeal ^ n}
        from hle)
      omega
    · rw [Nat.sSup_of_not_bddAbove hb] at he
      exact zero_ne_one he
  · rw [← Ideal.ramificationIdx'_eq_ramificationIdx q v.asIdeal hqbot]
    exact he
  · rw [← Ideal.inertiaDeg'_eq_inertiaDeg q v.asIdeal]
    exact hf

end GlobalTheory
end

