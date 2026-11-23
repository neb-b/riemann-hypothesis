module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentMulOfMapsToParabolicInduction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContinuousCocyclesRestrictLattice
section
noncomputable section

namespace GlobalTheory.NL.RightExactKs

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.NL

section Generic

theorem dvd_pow_of_not_isUnit {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {p : O} (hp : ¬ IsUnit p) {a : O} (ha : a ≠ 0) : ∃ n : ℕ, a ∣ p ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hp
  exact ⟨n, hn.dvd.trans (pow_dvd_pow_of_dvd h1 n)⟩

variable {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {LL : Type} [Field LL]
  {O : Type} [CommRing O] [Algebra O LL] [IsDomain O] [IsDiscreteValuationRing O]
  [IsFractionRing O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] {ρ : Representation LL G V}
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
  {ρ' : Representation LL G V'}

theorem lift_integral {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L')
    (hT : IsOpen (L.T : Set V)) {p : ℕ} (hp : ¬ IsUnit (p : O)) (c' : ↥(latticeCocycles L')) (c : G → V)
    (hc : c ∈ continuousCocycles ρ) (v : V') (hv : ∀ g, F.f (c g) - (c' : G → V') g = ρ' g v - v) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles L)), (∀ g, (c₁ : G → V) g = ((p : LL) ^ n) • c g) ∧
      F.H1map (Submodule.Quotient.mk c₁) = (p ^ n : ℕ) • (Submodule.Quotient.mk c' : LatticeCohomology L') := by
  obtain ⟨a, ha, h⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_fun_mem L hT c hc.1
  obtain ⟨b, hb, h'⟩ := GlobalTheory.H1fGeneratorBoundAlt.exists_smul_mem L' v
  obtain ⟨n, d, hd⟩ := dvd_pow_of_not_isUnit hp (mul_ne_zero ha hb)
  have h1 : (p : O) ^ n • c ∈ latticeCocycles L := by
    refine ⟨Submodule.smul_mem ((continuousCocycles ρ).restrictScalars O) _ hc, fun g _ => ?_⟩
    change (p : O) ^ n • c g ∈ L.T
    rw [hd, mul_assoc, mul_comm, mul_smul]
    exact L.T.smul_mem _ (h g)
  have h2 : (p : O) ^ n • v ∈ L'.T := by
    rw [hd, mul_comm, ← mul_assoc, mul_smul]
    exact L'.T.smul_mem _ h'
  refine ⟨n, ⟨_, h1⟩, fun g => ?_, ?_⟩
  · change (p : O) ^ n • c g = _
    rw [← algebraMap_smul LL, map_pow, map_natCast]
  · rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul]
    refine (Submodule.Quotient.eq _).2 ⟨_, h2, ?_⟩
    funext g
    change ρ' g ((p : O) ^ n • v) - (p : O) ^ n • v =
      F.f ((p : O) ^ n • c g) - ((p ^ n : ℕ) : O) • (c' : G → V') g
    rw [Nat.cast_pow, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, ← smul_sub,
      ← smul_sub, hv]

end Generic

theorem lift_integral_res {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] (hO : GoodO (Qp := Qp) LL O) (H : Subgroup G) [CompactSpace ↥H]
    (T₁ T₂ : LocLat G Qp LL O) (π : LatHom T₁.L T₂.L) {p : ℕ} (hp : ¬ IsUnit (p : O))
    (c₂ : ↥(latticeCocycles (resLat T₂ H))) (κ₂ : LatticeCohomology (resLat T₂ H)) (hκ : Submodule.Quotient.mk c₂ = κ₂)
    (c : ↥H → T₁.V) (hc : c ∈ continuousCocycles (T₁.ρ.comp H.subtype)) (v : T₂.V)
    (hv : ∀ g : ↥H, π.f (c g) - (c₂ : ↥H → T₂.V) g = T₂.ρ (g : G) v - v) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles (resLat T₁ H))) (κ₁ : LatticeCohomology (resLat T₁ H)),
      Submodule.Quotient.mk c₁ = κ₁ ∧ (∀ g, (c₁ : ↥H → T₁.V) g = ((p : LL) ^ n) • c g) ∧
      (resHom π H).H1map κ₁ = (p ^ n : ℕ) • κ₂ := by
  obtain ⟨hD, hDVR, hF⟩ := hO.1
  obtain ⟨n, c₁, h1, h2⟩ := lift_integral (resHom π H) (GlobalTheory.Cyc.locLat_isOpen hO T₁) hp c₂ c hc v hv
  exact ⟨n, c₁, _, rfl, h1, hκ ▸ h2⟩

theorem mem_continuousCocycles_restrictLattice {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) (H : Subgroup G) (c : ↥(latticeCocycles (resLat T H))) :
    (c : ↥H → T.V) ∈ continuousCocycles (T.ρ.comp H.subtype) := c.2.1

theorem smul_coboundary {Qp LL V B : Type} [Field Qp] [Field LL] [Algebra Qp LL] [AddCommGroup V]
    [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [CommRing B] [Algebra Qp B]
    (f : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B) (a : LL) {y y' : V} {x : V ⊗[Qp] B} (h : y' = a • y)
    (hx : y ⊗ₜ[Qp] (1 : B) = f x - x) : y' ⊗ₜ[Qp] (1 : B) = f (a • x) - a • x := by
  rw [h, map_smul, ← smul_sub, ← hx]
  rfl

variable {l : ℕ} [Fact l.Prime]

theorem not_isUnit_l (P : LocPrime l) (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  have h1 : ((l : ℕ) : ↥LL.1) * (u : ↥LL.1) = 1 := by
    have := congrArg (algebraMap ↥(OL LL) ↥LL.1) hu
    rwa [map_mul, map_natCast, map_one] at this
  have h2 := congrArg (P.v LL) h1
  rw [AddValuation.map_mul, AddValuation.map_one, P.v_l] at h2
  have h3 : 0 ≤ P.v LL (u : ↥LL.1) := (P.v_O LL _).2 u.2
  have h4 : (1 : WithTop ℚ) ≤ 0 := h2 ▸ le_add_of_nonneg_right h3
  exact absurd h4 (by simp)

theorem continuous_incl {K E : FinExt l} (hle : K.1 ≤ E.1) :
    Continuous (Subgroup.inclusion (GK_le hle)) :=
  continuous_subtype_val.subtype_mk _

def resRep {K LL : FinExt l} (E : FinExt l) (hle : K.1 ≤ E.1) (T : Lt K LL) :
    GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := T.V
  ρ := T.ρ.comp (Subgroup.inclusion (GK_le hle))
  cont x := (T.cont x).comp (continuous_incl hle)


set_option maxHeartbeats 1600000 in
theorem lift_rational (P : LocPrime l) (AI : LocAinf l P) (hP : LocTied l P AI) {K LL : FinExt l}
    (E : FinExt l) (hle : K.1 ≤ E.1) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (hπ : Function.Surjective π.f) (h₁ : IsCrys (P.PD K) T₁.ρ) (h₂ : IsCrys (P.PD K) T₂.ρ)
    (c₂ : ↥H → T₂.V) (hc₂ : c₂ ∈ continuousCocycles (T₂.ρ.comp H.subtype))
    (x₂ : T₂.V ⊗[ℚ_[l]] P.R.B)
    (hx₂ : ∀ g : ↥H, c₂ g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) T₂.ρ (g : ↥(GK K)) x₂ - x₂) :
    ∃ c₁ ∈ continuousCocycles (T₁.ρ.comp H.subtype),
      (∃ x₁ : T₁.V ⊗[ℚ_[l]] P.R.B,
        ∀ g : ↥H, c₁ g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) T₁.ρ (g : ↥(GK K)) x₁ - x₁) ∧
      ∃ v : T₂.V, ∀ g : ↥H, π.f (c₁ g) - c₂ g = T₂.ρ (g : ↥(GK K)) v - v := by
  let a : ↥(GK E) → ↥H := fun g => ⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩
  let b : ↥H → ↥(GK E) := fun g => ⟨((g : ↥(GK K)) : GQ l), (hH _).1 g.2⟩
  have ha : Continuous a := (continuous_incl hle).subtype_mk _
  have hb : Continuous b := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hres := fun (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) =>
    (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l P AI hP K E LL hle T.V T.ρ).1 hT
  have hc' : c₂ ∘ a ∈ finiteCocycles (P.PD E) (resRep E hle T₂).ρ := by
    refine ⟨⟨hc₂.1.comp ha, fun g h => hc₂.2 (a g) (a h)⟩, x₂, fun g => ?_⟩
    exact (hx₂ (a g)).trans (congrArg (fun f : T₂.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T₂.V ⊗[ℚ_[l]] P.R.B => f x₂ - x₂)
      (GlobalTheory.Cyc.actVB_inclusion P K E LL hle T₂ g).symm)
  obtain ⟨c, ⟨hc, x, hx⟩, v, hv⟩ := _root_.GlobalTheory.BKRightExact.bkARightExact_of_tied l P AI hP E ↥LL.1 ↥(OL LL)
    (GlobalTheory.LocalIntegers.good_integers l LL).1 (resRep E hle T₁) (resRep E hle T₂) π.f
    (fun g y => π.equiv _ y) hπ (hres T₁ h₁) (hres T₂ h₂) _ hc'
  refine ⟨c ∘ b, ⟨hc.1.comp hb, fun g h => hc.2 (b g) (b h)⟩, ⟨x, fun g => ?_⟩, v, fun g => ?_⟩
  · let x' : T₁.V ⊗[ℚ_[l]] P.R.B := x
    exact (hx (b g)).trans (congrArg (fun f : T₁.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T₁.V ⊗[ℚ_[l]] P.R.B => f x' - x')
      (GlobalTheory.Cyc.actVB_inclusion P K E LL hle T₁ (b g)))
  · exact (congrFun hv (b g)).symm

theorem compactSpace_sub {K E : FinExt l} (hle : K.1 ≤ E.1) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) : CompactSpace ↥H := by
  have := GlobalTheory.H1fGeneratorBoundAlt.compactSpace_GK E
  let a : ↥(GK E) → ↥H := fun g => ⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩
  have ha : Continuous a := (continuous_incl hle).subtype_mk _
  have hs : Function.Surjective a := fun g => ⟨⟨((g : ↥(GK K)) : GQ l), (hH _).1 g.2⟩, rfl⟩
  exact hs.compactSpace ha

theorem mem_GKs_iff (P : LocPrime l) {K LL : FinExt l} {s m : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) m) (hs : W.s = s) (x : ↥(GK K)) :
    x ∈ W.GKs ↔ (x : GQ l) ∈ GK (GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) := by
  rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, hs]
  rfl


set_option maxHeartbeats 1600000 in
theorem lift_cocycle (P : LocPrime l) (AI : LocAinf l P) (hP : LocTied l P AI) {K LL : FinExt l}
    {s m : ℕ} (hK : K.1 ≤ Ks K s) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) m) (hs : W.s = s)
    (T₁ T₂ : Lt K LL) (π : LatHom T₁.L T₂.L)
    (hπ : Function.Surjective π.f) (h₁ : IsCrys (P.PD K) T₁.ρ) (h₂ : IsCrys (P.PD K) T₂.ρ)
    (c₂ : ↥(latticeCocycles (resLat T₂ W.GKs))) (κ₂ : LatticeCohomology (resLat T₂ W.GKs))
    (hκ : Submodule.Quotient.mk c₂ = κ₂) (x₂ : T₂.V ⊗[ℚ_[l]] P.R.B)
    (hx₂ : ∀ g : ↥W.GKs, (c₂ : ↥W.GKs → T₂.V) g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
      actVB (P.PD K) T₂.ρ (g : ↥(GK K)) x₂ - x₂) :
    ∃ (n : ℕ) (c₁ : ↥(latticeCocycles (resLat T₁ W.GKs))) (κ₁ : LatticeCohomology (resLat T₁ W.GKs)),
      Submodule.Quotient.mk c₁ = κ₁ ∧
      (∃ x₁ : T₁.V ⊗[ℚ_[l]] P.R.B, ∀ g : ↥W.GKs, (c₁ : ↥W.GKs → T₁.V) g ⊗ₜ[ℚ_[l]] (1 : P.R.B) =
        actVB (P.PD K) T₁.ρ (g : ↥(GK K)) x₁ - x₁) ∧
      (resHom π W.GKs).H1map κ₁ = (l ^ n : ℕ) • κ₂ := by
  have hH := mem_GKs_iff P W hs
  have := compactSpace_sub (E := GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) hK W.GKs hH
  refine (lift_rational P AI hP (GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants.KsFin K s) hK W.GKs hH T₁ T₂ π hπ h₁ h₂ _
    (mem_continuousCocycles_restrictLattice T₂ W.GKs c₂) x₂ hx₂).elim fun c hc => hc.2.1.elim fun x hx =>
      hc.2.2.elim fun v hv => ?_
  refine (lift_integral_res (GlobalTheory.LocalIntegers.good_integers l LL).1
    W.GKs T₁ T₂ π (not_isUnit_l P LL) c₂ κ₂ hκ c hc.1 v hv).elim fun n h => h.elim fun c₁ h =>
      h.elim fun κ₁ h => ?_
  exact ⟨n, c₁, κ₁, h.1, ⟨((l : ↥LL.1) ^ n) • x, fun g => smul_coboundary _ _ (h.2.1 g) (hx g)⟩,
    h.2.2⟩

end GlobalTheory.NL.RightExactKs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismComparisonMatrixPowSmulBoundedOnDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem comparisonMatrix_bounded : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀), ht.Rel (BK.hf f X) f g ε → ∃ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A), x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε := by
  intro l _ K bk d ρ τ s ht hper B f g ι tb ε hrel
  have hnorm := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f g
  let Φ : Disc l (BK.hf f X) bk.ρ₀ →+* Disc l (BK.hf f X) bk.ρ₀ := Disc.map B.D.φ hnorm.2
  have hΦ : IsDiscMap (l := _) (u := _) (ρ := _) B.D.φ Φ := isDiscMap_map _ _
  have hreg := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f) ι tb
  have hpair := _root_.GlobalTheory.BSP.hf_E_pair l K bk B f g
  have heq := GlobalTheory.T.comparisonMatrix_frobenius_disc l K bk d ρ τ s ht hper B f hreg.2.1 f g ε hrel Φ hΦ
  have hQ : ht.A.map (BK.hf g) * ht.A'.map (BK.hf g) =
      BK.hf g bk.E ^ ht.b • (1 : Matrix (Fin d) (Fin d) B.A) := by
    rw [← Matrix.map_mul (f := BK.hf g), ht.A_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  obtain ⟨h, c, hc⟩ := _root_.GlobalTheory.BSP.matrix_phi_eq_family B.A (Disc l (BK.hf f X) bk.ρ₀) (toDisc l (BK.hf f X) bk.ρ₀) Φ
    (BK.hf f bk.E) (BK.hf g bk.E) hpair.2.1 d d (ht.a + s.N) (ht.a + s.N) ht.b (ht.A.map (BK.hf f))
    (ht.A.map (BK.hf g)) (ht.A'.map (BK.hf g)) hQ ε heq
  have hφX : B.D.φ (BK.hf f X) = BK.hf f X ^ l := by
    have h1 : B.D.φ (f.f X) = f.f (bk.prism.D.φ X) := (f.f_φ X).symm
    have h2 : bk.prism.D.φ X = X ^ l := frobS_X l bk.a
    exact h1.trans ((congrArg f.f h2).trans (map_pow f.f _ l))
  have key := GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk B.A (BK.hf f) ι tb B.D.φ hφX Φ hΦ (Fin d × Fin d) c
    (fun _ _ => Set.toFinite _) h (fun j => ε j.1 j.2)
  have htend : Filter.Tendsto (fun j : Fin d × Fin d => ε j.1 j.2) Filter.cofinite
      (nhds (0 : Disc l (BK.hf f X) bk.ρ₀)) := by
    simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]
  have hsum : ∀ j : Fin d × Fin d, HasSum (fun i => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
      (toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2) := fun j => by
    have hs := hasSum_fintype (fun i : Fin d × Fin d => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
    have e : toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2 =
        ∑ k : Fin d × Fin d, Φ (ε k.1 k.2) * toDisc l (BK.hf f X) bk.ρ₀ (c k j) := hc j
    convert hs using 1
  have k2 := key htend hsum
  obtain ⟨k, v, hv, -⟩ := k2
  refine ⟨k, Matrix.of fun i j => v (i, j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact hv (i, j)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAdelicRationalPointsCommStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_adelicRationalPoints_comm : ∀ (E : Type) [Field E] [NumberField E] (ι κ : Type) [Fintype ι] [Fintype κ] (Φ : (ι → Ad E) × (κ → Ad E) → ℂ), Per ((ratV E ι).prod (ratV E κ)) Φ → avg (ratV E ι) (fun x => avg (ratV E κ) (fun y => Φ (x, y))) = avg (ratV E κ) (fun y => avg (ratV E ι) (fun x => Φ (x, y))) := by
  first | exact @GlobalTheory.CuspGeneric.avg_comm | exact GlobalTheory.CuspGeneric.avg_comm | (intros; apply GlobalTheory.CuspGeneric.avg_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ
open scoped ComplexConjugate

namespace GlobalTheory.ZEul


open Classical in
def rsTerm (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : ℂ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    schurAt (fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)
  else 0

theorem rsTerm_zero (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) : rsTerm q α β x 0 = 1 := by
  have h : (fun _ : Fin n => (0 : ℕ)) = fun i => ((0 : Fin n → ℤ) i).toNat := by funext i; simp
  have hs : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) α = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  have hs' : schurAt (fun i => ((0 : Fin n → ℤ) i).toNat) β = 1 := by
    rw [← h, schurAt, schur_zero]; simp
  rw [rsTerm, if_pos ⟨fun i => le_rfl, antitone_const⟩, hs, hs']
  simp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ}

def lastRow (g : GA E (m + 1)) : Fin (m + 1) → Ad E := fun j => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j

def uInt (φ φ' : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ) (g : GA E (m + 1)) : ℂ :=
  whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i))) *
    conj (whit φ' (g * infGL E (m + 1) (secInv fun i => pInf E (lastRow g i)))) *
    Φ (fun i => pInf E (lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (lastRow g i)) * (detPow E (m + 1) x g : ℂ)

end GlobalTheory.ZEul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDieudonneModuleSpansTensorPeriodRing
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem Dst_spans_tensor_Bst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → ∀ v : V, ∃ (k : ℕ) (a : Fin k → Bst P) (x : Fin k → V ⊗[ℚ_[l]] Bst P), (∀ i, x i ∈ Dst P ρ) ∧ v ⊗ₜ[ℚ_[l]] (1 : Bst P) = ∑ i, onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] (a i)) (x i) := by
  intro l _ P AI T K V _ _ _ ρ hS v
  set b := Module.finBasis ℚ_[l] V with hb
  obtain ⟨Q, hQ⟩ := _root_.GlobalTheory.PMon.exists_periodMatrix_of_isSst l P AI T (Fin (finrank ℚ_[l] V)) K V b ρ hS
  obtain ⟨e, he1, he2, he3⟩ := _root_.GlobalTheory.tensorBasisCoords ℚ_[l] (Bst P) V (Fin (finrank ℚ_[l] V)) b

  have hst : ∀ g : ↥(GK K), (stRep P ρ g : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P) =
      TensorProduct.map (ρ g) (actSt P (g : GQ l)).toLinearMap := by
    intro g; apply TensorProduct.ext'; intro w c; rfl
  have hon : ∀ f : End ℚ_[l] (Bst P), (onB P ℚ_[l] V f : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P) =
      TensorProduct.map LinearMap.id f := by
    intro f; apply TensorProduct.ext'; intro w c; rfl
  set w : Fin (finrank ℚ_[l] V) → Bst P := fun i => algebraMap ℚ_[l] (Bst P) (b.repr v i) with hw
  let Qm : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P) := Q.1
  let Qi : Matrix (Fin (finrank ℚ_[l] V)) (Fin (finrank ℚ_[l] V)) (Bst P) := (Q⁻¹).1
  refine ⟨finrank ℚ_[l] V, Matrix.mulVec Qi w, fun j => e.symm (fun i => Qm i j), ?_, ?_⟩
  · intro j
    rw [mem_Dst]
    intro g
    apply e.injective
    rw [hst g, he3, LinearEquiv.apply_symm_apply]
    have h : ∀ i, (((LinearMap.toMatrix b b) (ρ g)).map ⇑(algebraMap ℚ_[l] (Bst P)) * (Q.1).map ⇑((actSt P) ↑g)) i j = Qm i j :=
      fun i => congrFun (congrFun (hQ g) i) j
    funext i
    rw [← h i]
    rfl
  · apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    funext i
    rw [he1, Finset.sum_apply]
    have key : ∀ j, e (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] ((Matrix.mulVec Qi w) j)) (e.symm (fun i => Qm i j))) i =
        (Matrix.mulVec Qi w) j * Qm i j := by
      intro j
      rw [hon, he3, LinearEquiv.apply_symm_apply, LinearMap.toMatrix_id, Matrix.map_one (algebraMap ℚ_[l] (Bst P)) (map_zero _) (map_one _), Matrix.one_mulVec]
      rfl
    simp_rw [key]
    have hQQ : Qm * Qi = 1 := by
      show (Q * Q⁻¹).1 = 1
      rw [mul_inv_cancel]; rfl
    have := congrFun (congrArg (fun M => Matrix.mulVec M w) hQQ) i
    simp only [Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at this
    rw [Algebra.smul_def, mul_one]
    refine this.symm.trans ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.Pst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodPowDvdByBasisAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.BKLim.WHeightSprime

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ K bk τ hτ d ρ hρ s Y hY hP
  obtain ⟨ι, TB, k, v, Z, hnull, hWZ, hsum⟩ := GlobalTheory.T.exists_bounded_semistable_periods_null_family l K bk τ hτ d ρ hρ s
  have hcol : ∀ i (b : Fin d), ∃ c : Fin d → bk.S, (fun a => v i a b) = Y *ᵥ fun a => bk.ev (c a) := by
    intro i b
    refine (hP _).1 ⟨fun a => Z i a b, fun j hj => ?_⟩
    funext a
    have h := congrFun (congrFun (hWZ j hj i) a) b
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  choose σc hσc using hcol
  set σ : ι → Matrix (Fin d) (Fin d) bk.S := fun i => Matrix.of fun a b => σc i b a with hσdef
  have hv : ∀ i, v i = Y * (σ i).map bk.ev := by
    intro i
    refine Matrix.ext fun a b => ?_
    have h := congrFun (hσc i b) a
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, σ] using h
  have hσn := _root_.GlobalTheory.NullOverS.null_of_mul_null l K bk ι TB d Y hY σ (fun n a b => by simpa only [← hv] using hnull n a b)
  have hL : ∀ c b : Fin d, ∃ L : Ainf l, ∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G →
      L - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i ∈ (bk.J ^ n).map bk.ev :=
    fun c b => _root_.GlobalTheory.BSP.exists_sum_null_ev l K bk ι TB (fun i => σ i c b) (fun n => hσn n c b)
  choose L hL using hL
  refine ⟨k, Matrix.of L, ?_⟩
  refine Matrix.ext fun a b => ?_
  refine _root_.GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic l K bk ι TB (fun i => v i a b * TB.b i) _ _ ?_ ?_
  · simpa [Matrix.smul_apply, Matrix.one_apply] using hsum a b
  · classical
    intro n
    choose F hF using fun c => hL c b n
    refine ⟨Finset.univ.biUnion F, fun G hG => ?_⟩
    have e : (Y * Matrix.of L) a b - ∑ i ∈ G, v i a b * TB.b i =
        ∑ c, Y a c * (L c b - ∑ i ∈ G, bk.ev (σ i c b) * TB.b i) := by
      simp only [hv, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _
      (hF c G ((Finset.subset_biUnion_of_mem F (Finset.mem_univ c)).trans hG))
end GlobalTheory.BKLim.WHeightSprime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentMulOfMapsToParabolicInductionStatement
section
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesIdempotent_mul_of_maps_to_parabolicInduction : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'), IsIrrRep π → MapsToProd π σ ρ → ∀ F, Has S π F → ∃ f f', Has S σ f ∧ Has S ρ f' ∧ F = f * f' := by
  first | exact @GlobalTheory.SerSys.Prod.series_of_mapsToProd | exact GlobalTheory.SerSys.Prod.series_of_mapsToProd | (intros; apply GlobalTheory.SerSys.Prod.series_of_mapsToProd <;> assumption)
end

