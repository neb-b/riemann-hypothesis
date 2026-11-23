module

public import Mathlib
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeQuotientsNondegenerate
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import GroundTheory.LocalFields.Examples
public import GroundTheory.LocalFields.Bundle0002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCocycleCupNotCoboundaryFiniteLevel
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualFin

theorem ko_torsion : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ), (p : O) ∈ IsLocalRing.maximalIdeal O → ∀ a : KO O, ∃ r : ℕ, (p : O) ^ r • a = 0 := by
  intro O _ _ _ p hp a
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨o, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hs) hϖ
  obtain ⟨t, ht⟩ : ϖ ∣ (p : O) := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq ▸ hp)
  have hinj := IsFractionRing.injective O (FractionRing O)
  have hπ : algebraMap O (FractionRing O) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have hu0 : algebraMap O (FractionRing O) (u : O) ≠ 0 := (map_ne_zero_iff _ hinj).2 u.ne_zero
  refine ⟨m, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨o * t ^ m * ((u⁻¹ : Oˣ) : O), ?_⟩
  rw [Algebra.smul_def, hu, ht]
  simp only [map_mul, map_pow]
  have hui : algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = (algebraMap O (FractionRing O) (u : O))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [hui]
  field_simp
  ring


open GlobalTheory.TateFin GlobalTheory.TateTop GlobalTheory.Cyc.TwistLift ReciprocityTheory.Neutral.Bridge in
theorem exists_cocycle_cup_not_cob : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G], FiniteDimensional ℚ_[p] K → IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (D : LatData O G VT VT'), (∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧ ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → IsLatticeIn D.T → PerfectRight D.bT → ContAction D.ρT → IsOpen (D.T : Set VT) → T2Space VT → T2Space VT' → ContinuousConstSMul (FractionRing O) VT → ContinuousConstSMul (FractionRing O) VT' → ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Z1 D.ρA, c ∉ B1 D.ρA → ∀ r : ℕ, (∀ g, ϖ ^ r • c g = 0) → ∀ n : ℕ, r ≤ n → ∃ z ∈ Z1 (quotRep D.ρTl' ϖ n), cupMod D c ϖ n z ∉ B2 (twist D.ε (KO O)) := by
  intro hTate p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ hK hOr hOc hOt hOa hpm hp0
    hemb i D hcyc hlat hperf hcontT hTo hT2 hT2' hcs hcs' ϖ hϖ c hc hcB r hr n hrn
  by_contra H
  push_neg at H
  apply hcB
  haveI : CompactSpace G := i.toHomeomorph.symm.compactSpace
  haveI : ContinuousMul G := ⟨by
    have h := i.symm.continuous.comp
      ((i.continuous.comp continuous_fst).mul (i.continuous.comp continuous_snd))
    refine h.congr fun q => ?_
    show i.symm (i q.1 * i q.2) = q.1 * q.2
    rw [← map_mul, ContinuousMulEquiv.symm_apply_apply]⟩
  let χ : G →* ℤ_[p]ˣ := ((cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p))).comp (i : G →* Formalism.GaloisCohomology.GK p K)
  have hχ : Continuous fun g => (χ g : ℤ_[p]) :=
    Units.continuous_val.comp ((cyclotomicCharacter.continuous p K (PadicAlgCl p)).comp i.continuous)
  have hT' : ∀ (k : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (p ^ (k + 1))) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (p ^ (k + 1))) G M)
      (hrho : ContAction rho), DualityFor (redChar χ (k + 1)) rho hrho := by
    intro k M _ _ _ _ _ rho hrho
    refine DualityFor.of_comp i.symm _ hrho ?_
    have h1 : (redChar χ (k + 1)).comp (i.symm : Formalism.GaloisCohomology.GK p K →* G) = Formalism.GaloisCohomology.cycK p K (k + 1) :=
      MonoidHom.ext fun g => congrArg (Formalism.GaloisCohomology.cycK p K (k + 1)) (i.apply_symm_apply g)
    rw [h1]
    exact hTate p K hK (k + 1) M _ (Nat.succ_pos _) (contAction_comp i.symm hrho)
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.ZpHomAdic.zp_ringHom hOr hOc hOt hOa hpm
  have hspan : Ideal.span {(p : O)} ≠ ⊤ := fun h =>
    (IsLocalRing.mem_maximalIdeal _).1 hpm (Ideal.span_singleton_eq_top.1 h)
  have hkrull : ∀ a b : O, (∀ k : ℕ, a - b ∈ Ideal.span {(p : O) ^ k}) → a = b := by
    intro a b h
    have h0 := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {(p : O)}) hspan
    have h1 : a - b ∈ ⨅ k, Ideal.span {(p : O)} ^ k :=
      Ideal.mem_iInf.2 fun k => by rw [Ideal.span_singleton_pow]; exact h k
    rw [h0, Ideal.mem_bot, sub_eq_zero] at h1
    exact h1
  have hιε : ∀ g, ι (χ g : ℤ_[p]) = (D.ε g : O) := by
    intro g
    refine hkrull _ _ fun k => ?_
    obtain ⟨ζ, hζ, hζa⟩ := _root_.GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr K (i g) k
    obtain ⟨a, ha, hεa⟩ := hcyc g k ζ hζ
    have e1 : (a : ZMod (p ^ k)) = PadicInt.toZModPow k (χ g : ℤ_[p]) := hζa a ha
    have e2 := hι (χ g : ℤ_[p]) k
    rw [← e1, ZMod.val_natCast] at e2
    have e3 : ((a : ℕ) : O) - ((a % p ^ k : ℕ) : O) ∈ Ideal.span {(p : O) ^ k} := by
      have h : ((a : ℕ) : O) = ((a / p ^ k : ℕ) : O) * (p : O) ^ k + ((a % p ^ k : ℕ) : O) := by
        have h' := congrArg (Nat.cast : ℕ → O) (Nat.div_add_mod' a (p ^ k)).symm
        push_cast at h'
        exact h'
      exact Ideal.mem_span_singleton'.2 ⟨((a / p ^ k : ℕ) : O), by rw [h]; ring⟩
    have e4 : ι (χ g : ℤ_[p]) - (D.ε g : O) = (ι (χ g : ℤ_[p]) - ((a % p ^ k : ℕ) : O)) -
        (((a : ℕ) : O) - ((a % p ^ k : ℕ) : O)) - ((D.ε g : O) - (a : O)) := by ring
    rw [e4]
    exact sub_mem (sub_mem e2 e3) hεa
  letI : Module ℤ_[p] (KO O) := Module.compHom (KO O) ι
  have hsmul : ∀ (u : ℤ_[p]) (y : KO O), u • y = ι u • y := fun _ _ => rfl
  have htor : ∀ a : KO O, ∃ r : ℕ, (p : ℤ_[p]) ^ r • a = 0 := fun a => by
    obtain ⟨r, hr⟩ := ko_torsion p hpm a
    exact ⟨r, by rw [hsmul, map_pow, map_natCast]; exact hr⟩
  have hKOd : DiscreteTopology (KO O) :=
    QuotientAddGroup.discreteTopology (N := (1 : Submodule O (FractionRing O)).toAddSubgroup) (by
      have : ((1 : Submodule O (FractionRing O)).toAddSubgroup : Set (FractionRing O)) =
          Set.range (algebraMap O (FractionRing O)) := by
        ext x; simp [Submodule.mem_one, eq_comm]
      rw [this]; exact hemb.isOpen_range)
  have hVd : DiscreteTopology (VT ⧸ D.T) :=
    QuotientAddGroup.discreteTopology (N := D.T.toAddSubgroup) hTo
  have hclc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hc.1
  set X := LinearMap.ker (LinearMap.lsmul O (VT ⧸ D.T) (ϖ ^ n)) with hXdef
  have memX : ∀ x : VT ⧸ D.T, x ∈ X ↔ ϖ ^ n • x = 0 := fun x => by
    rw [hXdef, LinearMap.mem_ker, LinearMap.lsmul_apply]
  haveI : Finite X := GlobalTheory.T.finite_pow_smul_torsion_lattice_quotient D.T hOr hOc hOa hlat ϖ hϖ n
  obtain ⟨hcT', hopen, -⟩ := GlobalTheory.T.dualLattice_compact_powSmul_nhds_basis D hOc hemb hlat hperf hT2' ϖ hϖ
  haveI : CompactSpace ↥D.T' := hcT'
  haveI : Finite (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    AddSubgroup.quotient_finite_of_isOpen (powSub (M := ↥D.T') ϖ n).toAddSubgroup (hopen n)
  haveI hNd : DiscreteTopology (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    QuotientAddGroup.discreteTopology (N := (powSub (M := ↥D.T') ϖ n).toAddSubgroup) (hopen n)
  obtain ⟨t, ht⟩ : ϖ ∣ (p : O) := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq ▸ hpm)
  have hpow : ∀ {M : Type} [AddCommGroup M] [Module O M] (y : M), p ^ n • y = t ^ n • ϖ ^ n • y :=
    fun y => by rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ht, mul_pow, mul_comm, mul_smul]
  have hX : ∀ x : X, p ^ n • x = 0 := fun x => Subtype.ext (by
    rw [AddSubmonoidClass.coe_nsmul, hpow, (memX _).1 x.2, smul_zero]; rfl)
  have hN : ∀ y : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ n, p ^ n • y = 0 := fun y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [hpow, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_comm]
    exact smul_mem_powSub ϖ n _
  let a : G → X → X := fun g x => ⟨D.ρA g x, by rw [memX, ← map_smul, (memX _).1 x.2, map_zero]⟩
  let a' : G → (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) :=
    fun g => (quotRep D.ρTl' ϖ n g).toAddMonoidHom
  have h1 : ∀ y, a' 1 y = y := fun y => by
    show quotRep D.ρTl' ϖ n 1 y = y
    rw [map_one]; rfl
  have hm : ∀ g h y, a' (g * h) y = a' g (a' h y) := fun g h y => by
    show quotRep D.ρTl' ϖ n (g * h) y = quotRep D.ρTl' ϖ n g (quotRep D.ρTl' ϖ n h y)
    rw [map_mul]; rfl
  have hlc : ∀ y, IsLocallyConstant fun g => a' g y := fun y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [IsLocallyConstant.iff_continuous]
    show Continuous fun g => (Submodule.Quotient.mk (D.ρTl' g t0) : ↥D.T' ⧸ powSub (M := ↥D.T') ϖ n)
    exact continuous_quot_mk.comp ((sub_contAction D.contT' D.T' D.stT').comp
      (continuous_id.prodMk continuous_const))
  let βf : X → (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ KO O := fun x =>
    ((powSub (M := ↥D.T') ϖ n).liftQ (pairKO D.bT D.T (x : VT ⧸ D.T)) (fun t0 ht0 => by
      rw [LinearMap.mem_ker]; exact pairKO_eq_zero_of_mem D ((memX _).1 x.2) ht0)).toAddMonoidHom
  let β : X →+ (↥D.T' ⧸ powSub (M := ↥D.T') ϖ n) →+ KO O := AddMonoidHom.mk' βf (fun x x' => by
    ext y
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show pairKO D.bT D.T ((x + x' : X) : VT ⧸ D.T) t0 =
      pairKO D.bT D.T (x : VT ⧸ D.T) t0 + pairKO D.bT D.T (x' : VT ⧸ D.T) t0
    rw [Submodule.coe_add, map_add (f := _), LinearMap.add_apply])
  have he : ∀ g x y, β (a g x) (a' g y) = (χ g : ℤ_[p]) • β x y := fun g x y => by
    obtain ⟨t0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    show pairKO D.bT D.T (D.ρA g x) (D.ρTl' g t0) = ι (χ g : ℤ_[p]) • pairKO D.bT D.T (x : VT ⧸ D.T) t0
    rw [D.pairKO_equiv, twist_apply, hιε]
  have hs : toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) ≠ 0 := by
    intro h0
    rw [toKO, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at h0
    obtain ⟨o, ho⟩ := h0
    apply hϖ.not_isUnit
    have hinj := IsFractionRing.injective O (FractionRing O)
    have hπ : algebraMap O (FractionRing O) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    refine IsUnit.of_mul_eq_one (b := o) (hinj ?_)
    rw [map_mul, ho, map_one, mul_inv_cancel₀ hπ]
  have hβ1 : ∀ x : X, x ≠ 0 → ∃ y, β x y = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
    intro x hx
    obtain ⟨f, hf⟩ := GlobalTheory.T.exists_dualLattice_pairing_eq_inv_uniformizer D hlat hperf ϖ hϖ (x : VT ⧸ D.T) (fun h => hx (Subtype.ext h))
    exact ⟨Submodule.Quotient.mk f, hf⟩
  have hβ2 : ∀ y, y ≠ 0 → ∃ x : X, β x y = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
    intro y hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hf : f ∉ powSub (M := ↥D.T') ϖ n := fun h => hy ((Submodule.Quotient.mk_eq_zero _).2 h)
    obtain ⟨x, hx1, hx2⟩ := GlobalTheory.T.exists_torsion_pairing_eq_inv_uniformizer D ϖ hϖ n f hf
    exact ⟨⟨x, (memX x).2 hx1⟩, hx2⟩
  have hcX : ∀ g, c g ∈ X := fun g => (memX _).2 (by
    rw [← Nat.sub_add_cancel hrn, pow_add, mul_smul, hr, smul_zero])
  let c₀ : G → X := fun g => ⟨c g, hcX g⟩
  obtain ⟨x, hx⟩ := (nondeg_torsion hχ hT' htor hX hN a a' h1 hm hlc β he hs hβ1 hβ2).1 c₀
    (IsLocallyConstant.desc _ Subtype.val hclc Subtype.val_injective)
    (fun g h => Subtype.ext (hc.2 g h)) (by
      intro c' hc'l hc'c
      obtain ⟨b, hbc, hbe⟩ := (separated_dvr_second_cohomology_mem _ _).1 (H c' ⟨hc'l.continuous, fun g h => hc'c g h⟩)
      refine ⟨b, (IsLocallyConstant.iff_continuous b).2 hbc, fun q => ?_⟩
      obtain ⟨g, h⟩ := q
      have e := congrFun hbe (g, h)
      have e2 : β (c₀ g) (a' g (c' h)) = cupMod D c ϖ n c' (g, h) := by
        conv_lhs => rw [← mk_qlift (c' h)]
        rfl
      rw [e2, ← e]
      show _ = ι (χ g : ℤ_[p]) • b h - b (g * h) + b g
      rw [hιε]
      rfl)
  exact (mem_coboundaries1 _ _).2 ⟨x, fun g => congrArg Subtype.val (hx g)⟩

end GlobalTheory.LocDualFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrameOfTorsionInvariants
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.RedFun

theorem exists_invariant_basis {F₀ F R M D : Type} [Field F₀] [Field F] [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype D] (κ : F →+* R) (ι : F₀ →+* F) (σ : D → (F →+* F)) (t : D → (M →+ M)) (V : AddSubgroup M)
    (hV : ∀ c, ∀ y ∈ V, κ c • y ∈ V) {m : ℕ} (u : Fin m → M)
    (hu : ∀ y ∈ V, ∃ c : Fin m → F, y = ∑ j, κ (c j) • u j) (hσ : Function.Injective σ)
    (hsl : ∀ d c y, t d (κ c • y) = κ (σ d c) • t d y) (hst : ∀ d, ∀ y ∈ V, t d y ∈ V)
    (hav : ∀ d, ∀ y ∈ V, t d (∑ d', t d' y) = ∑ d', t d' y) (hid : ∃ d, ∀ y ∈ V, t d y = y)
    (hfix : ∀ c, (∀ d, σ d c = c) → ∃ c₀, ι c₀ = c) :
    ∃ s, s ≤ m ∧ ∃ w : Fin s → M, (∀ j, w j ∈ V) ∧ (∀ j d, t d (w j) = w j) ∧
      (∀ c : Fin s → F, ∑ j, κ (c j) • w j = 0 → c = 0) ∧
      (∀ y ∈ V, ∃ c : Fin s → F, y = ∑ j, κ (c j) • w j) ∧
      (∀ y ∈ V, (∀ d, t d y = y) → ∃ c : Fin s → F₀, y = ∑ j, κ (ι (c j)) • w j) := by
  classical
  let : Module F M := Module.compHom M κ
  have hs : ∀ (c : F) (y : M), c • y = κ c • y := fun _ _ => rfl
  let V' : Submodule F M := { V with smul_mem' := fun c y hy => hV c y hy }
  have h1 := GlobalTheory.stable_le_span_invariants_of_semilinear_family F M D σ t V' hσ (fun d c y _ => hsl d c y)
    hst hav hid
  obtain ⟨b, hb, hsp, hli⟩ := exists_linearIndependent F {y | y ∈ V' ∧ ∀ d, t d y = y}
  have hle : V' ≤ Submodule.span F (Set.range u) := by
    intro y hy
    obtain ⟨c, rfl⟩ := hu y hy
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ (c j) (Submodule.subset_span ⟨j, rfl⟩)
  have hbu : Set.range ((↑) : b → M) ≤ Submodule.span F (Set.range u) := by
    rintro _ ⟨x, rfl⟩
    exact hle (hb x.2).1
  have : Finite b := by
    have : Module.Finite F (Submodule.span F (Set.range u)) := Module.Finite.span_of_finite F (Set.finite_range u)
    have h0 : LinearIndependent F fun x : b => (⟨x.1, hbu ⟨x, rfl⟩⟩ : Submodule.span F (Set.range u)) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    exact h0.finite
  have : Fintype b := Fintype.ofFinite b
  have hc := (linearIndependent_le_span_aux' _ hli (Set.range u) hbu).trans (Fintype.card_range_le u)
  rw [Fintype.card_fin] at hc
  let e := (Fintype.equivFin b).symm
  have hli' : LinearIndependent F (fun j => (e j : M)) := hli.comp e e.injective
  have hind : ∀ c : Fin (Fintype.card b) → F, ∑ j, κ (c j) • (e j : M) = 0 → c = 0 := fun c hc =>
    funext (Fintype.linearIndependent_iff.1 hli' c hc)
  have hgen : ∀ y ∈ V, ∃ c : Fin (Fintype.card b) → F, y = ∑ j, κ (c j) • (e j : M) := by
    intro y hy
    have h2 : y ∈ Submodule.span F (Set.range fun j => (e j : M)) := by
      have h3 : (Set.range fun j => (e j : M)) = b := by
        ext x
        constructor
        · rintro ⟨j, rfl⟩; exact (e j).2
        · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩
      rw [h3, hsp]
      exact h1 hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 h2
    exact ⟨c, hc.symm⟩
  refine ⟨_, hc, fun j => e j, fun j => (hb (e j).2).1, fun j => (hb (e j).2).2, hind, hgen, ?_⟩
  intro y hy hinv
  obtain ⟨c, rfl⟩ := hgen y hy
  have h4 : ∀ j d, σ d (c j) = c j := by
    intro j d
    have h5 := hinv d
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h5
    simp only [hsl, fun j => (hb (e j).2).2 d] at h5
    have h6 := hind (fun j => σ d (c j) - c j) (by
      simp only [map_sub, sub_smul, Finset.sum_sub_distrib, h5, sub_self])
    exact sub_eq_zero.1 (congrFun h6 j)
  choose c₀ hc₀ using fun j => hfix (c j) (h4 j)
  exact ⟨c₀, by simp only [hc₀]⟩

theorem exists_frame_of_invariants : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk) (a : G → (Rk →ₐ[k] Rk)) (ι : k⸨X⸩ →+* k⸨X⸩) (σ : {δ // δ ∈ W.DelF} → (k⸨X⸩ →+* k⸨X⸩)), IsRed E ρ (k := k) lam κ → IsDel E ρ κ a ι σ → ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∀ i, (∃ u : Fin A.m → W.DD T, ∀ x, ∃ c : Fin A.m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) → ∃ β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k), IsFrame (κ.comp ι) (eps E ρ i) β ∧ ∀ y, (∃ x, β x = y) ↔ ∃ x : ↥(DΔ W T), y = eps E ρ i • J E ρ T q x := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W RA RW _ _ _ _ inclR φR gR πA
    E k _ _ Rk _ _ _ _ ρ lam κ a ι σ hR hD T A q hq i hu
  classical
  obtain ⟨u, hu⟩ := hu
  set ε := eps E ρ i with hε
  have hεε : ε * ε = ε := eps_idem E ρ i
  choose g hg using fun δ : {δ // δ ∈ W.DelF} => W.resΓ_onto δ.1
  let f : W.DD T →+ Rk ⊗[k] (Fin A.m → k) := (DistribSMul.toAddMonoidHom _ ε).comp (J E ρ T q)
  have hf : ∀ x, f x = ε • J E ρ T q x := fun _ => rfl
  let t : {δ // δ ∈ W.DelF} → (Rk ⊗[k] (Fin A.m → k) →+ Rk ⊗[k] (Fin A.m → k)) :=
    fun δ => (Act a A (g δ)).toAddMonoidHom
  have ht : ∀ δ x, t δ (f x) = f (W.γD T δ.1 x) := by
    intro δ x
    change Act a A (g δ) (ε • J E ρ T q x) = _
    rw [Act_smul, hD.a_eps, ← J_act E ρ hD.a_ρ T A q hq, hg, hf]
  have hsum : ∀ x, ∑ δ, t δ (f x) = f (∑ δ ∈ W.DelF, W.γD T δ x) := by
    intro x
    simp only [ht]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_coe_sort W.DelF (fun δ => f (W.γD T δ x))]
  have hinv : ∀ x ∈ DΔ W T, ∀ δ, t δ (f x) = f x := by
    intro x hx δ
    rw [ht, hx δ.1 δ.2]
  have hV : ∀ c, ∀ y ∈ f.range, κ c • y ∈ f.range := by
    rintro c _ ⟨x, rfl⟩
    obtain ⟨e, he⟩ := hR.κ_of i c
    refine ⟨e • x, ?_⟩
    rw [hf, hf, J_smul, smul_smul, smul_smul, ← he, mul_comm]
  have hsl : ∀ d c y, t d (κ c • y) = κ (σ d c) • t d y := by
    intro d c y
    change Act a A (g d) (κ c • y) = κ (σ d c) • Act a A (g d) y
    rw [Act_smul, hD.a_κ _ d (hg d)]
  obtain ⟨s, hs, w, hwV, hwi, hind, hgen, hgen₀⟩ := exists_invariant_basis κ ι σ t f.range hV
    (fun j => f (u j)) (by rintro _ ⟨x, rfl⟩; exact hu x) hD.σ_inj hsl
    (by rintro d _ ⟨x, rfl⟩; exact ⟨_, (ht d x).symm⟩)
    (by rintro d _ ⟨x, rfl⟩; rw [hsum]; exact hinv _ (sum_mem_DΔ T x) d)
    ⟨⟨1, (W.DelF_def 1).2 ⟨1, one_pos, one_pow 1⟩⟩, by rintro _ ⟨x, rfl⟩; rw [ht, W.γD_one]⟩
    (fun c => (hD.σ_fix c).1)
  have hspan : ∀ y : Fin A.m → k, ε ⊗ₜ[k] y ∈ Submodule.span Rk (Set.range w) := by
    intro y
    obtain ⟨x, rfl⟩ := hq.1 y
    have key : ∀ z ∈ Submodule.span Rk (Set.range (J E ρ T q)), ε • z ∈ Submodule.span Rk (Set.range w) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        obtain ⟨c, hc⟩ := hgen _ ⟨x, rfl⟩
        rw [← hf, hc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
      | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ _ hy
    have := key _ (J_span E ρ T q x)
    rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this
  have hm : A.m ≤ s := card_le_of_span (eps_idem E ρ i) (hR.eps_ne i) w (Pi.basisFun k (Fin A.m))
    (Pi.basisFun k (Fin A.m)).linearIndependent (fun j => hspan _)
  obtain rfl : s = A.m := le_antisymm hs hm
  let β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k) :=
    { toFun := fun c => ∑ j, κ (ι (c j)) • w j
      map_zero' := by simp
      map_add' := fun c c' => by simp [add_smul, Finset.sum_add_distrib] }
  have hβ : ∀ c, β c = ∑ j, κ (ι (c j)) • w j := fun _ => rfl
  have hβV : ∀ c, β c ∈ f.range := fun c => by
    rw [hβ]; exact AddSubgroup.sum_mem _ fun j _ => hV _ _ (hwV j)
  refine ⟨β, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    have := hind (fun j => ι (c j)) hc
    funext j
    exact (map_eq_zero ι).1 (congrFun this j)
  · intro c x
    simp [hβ, Finset.smul_sum, smul_smul]
  · intro c
    obtain ⟨x, hx⟩ := hβV c
    rw [← hx, hf, smul_smul, hεε]
  · intro y
    refine Submodule.span_mono ?_ (hspan y)
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, ?_⟩
    rw [hβ, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
  · intro y
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨x, hx⟩ := hβV c
      have hi : ∀ δ, t δ (β c) = β c := by
        intro δ
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hβ, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsl, hwi, (hD.σ_fix _).2 ⟨_, rfl⟩]
      obtain ⟨r, hr⟩ := hR.res_surj ((W.DelF.card : k)⁻¹)
      refine ⟨⟨r • ∑ δ ∈ W.DelF, W.γD T δ x, ?_⟩, ?_⟩
      · intro δ hδ
        rw [map_smul, sum_mem_DΔ T x δ hδ]
      · change _ = ε • J E ρ T q (r • _)
        rw [J_smulO, smul_comm, ← hf, ← hsum, hx, hr, algebraMap_smul]
        simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
        rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hD.card_ne, one_smul]
    · rintro ⟨x, rfl⟩
      obtain ⟨c, hc⟩ := hgen₀ _ ⟨x.1, rfl⟩ (hinv x.1 x.2)
      exact ⟨c, hc.symm⟩

end GlobalTheory.RedFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisKerLeRange
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_galois_ker_le_range (l : ℕ) [Fact l.Prime] (U : Subgroup (GQ l)) (S : Set (Om l))
    (hU : IsOpen (U : Set (GQ l))) (hS : S.Finite) :
    ∃ (L : Type) (_ : Field L) (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : IsNonarchimedeanLocalField L)
      (_ : Algebra ℚ_[l] L) (_ : ValuativeExtension ℚ_[l] L) (_ : FiniteDimensional ℚ_[l] L)
      (_ : IsGalois ℚ_[l] L) (_ : Algebra L (Om l)) (_ : IsScalarTower ℚ_[l] L (Om l)),
      (AlgEquiv.restrictNormalHom L : GQ l →* (L ≃ₐ[ℚ_[l]] L)).ker ≤ U ∧
        S ⊆ Set.range (algebraMap L (Om l)) := by
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) (U : Set (GQ l))).mp
    (hU.mem_nhds U.one_mem)
  haveI := hS.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let F : IntermediateField ℚ_[l] (Om l) := E ⊔ IntermediateField.adjoin ℚ_[l] S
  let M : IntermediateField ℚ_[l] (Om l) := IntermediateField.normalClosure ℚ_[l] F (Om l)
  haveI : FiniteDimensional ℚ_[l] M := inferInstance
  haveI : Normal ℚ_[l] M := inferInstance
  haveI : IsGalois ℚ_[l] M := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have hFM : F ≤ M := IntermediateField.le_normalClosure F
  obtain ⟨vr, top, hloc, hext⟩ := exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] M
  refine ⟨M, inferInstance, vr, top, hloc, inferInstance, hext, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · rw [IntermediateField.restrictNormalHom_ker]
    intro σ hσ
    apply hEU
    exact (IntermediateField.fixingSubgroup_le (le_trans le_sup_left hFM)) hσ
  · intro x hx
    have : x ∈ M := hFM (le_sup_right (a := E) (IntermediateField.subset_adjoin ℚ_[l] S hx))
    exact ⟨⟨x, this⟩, rfl⟩

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltration
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_initialSegment_not_inf_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G), Antitone R →
      (∃ m, R m = ⊥) → ∃ n : ℕ, ∀ t, t < n ↔ ¬ A ⊓ R t ≤ B := by
  intro G _ R A B hR hm
  classical
  obtain ⟨m, hm⟩ := hm
  have h : ∃ t, A ⊓ R t ≤ B := ⟨m, by rw [hm]; simp⟩
  refine ⟨Nat.find h, fun t => ⟨fun ht => Nat.find_min h ht, fun hn => ?_⟩⟩
  by_contra hc
  push_neg at hc
  exact hn (le_trans (inf_le_inf_left A (hR hc)) (Nat.find_spec h))

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMutuallyDualStableLattices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.StableDual

theorem cyc_integral (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) (g : ↥(GK K)) :
    ∃ a : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL a := by
  obtain ⟨_, _, hmod, _, hopen⟩ := hO
  have hn : ‖(P.χQ (g : GQ l) : ℚ_[l])‖ ≤ 1 := ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).1 _).le
  have hmem := GlobalTheory.GoodCoeff.padicInt_mem (algebraMap O LL).range
    (by rw [RingHom.coe_range]; exact hopen) (⟨_, hn⟩ : ℤ_[l])
  obtain ⟨a, ha⟩ := RingHom.mem_range.1 hmem
  refine ⟨a, ?_⟩
  rw [ha]
  simp [cycLL, LocPrime.PD_χ]

theorem stable_dual_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ), IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m hm
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : CompactSpace ↥(GK K) :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  obtain ⟨LA⟩ := GlobalTheory.T.exists_stable_lattice_compact_group hO A
  obtain ⟨LA', h⟩ := GlobalTheory.T.dualLattice_stable_twisted_pairing l P K LL O hO A A' m LA hm (cyc_integral l P K LL O hO)
  exact ⟨LA, LA', h⟩

end GlobalTheory.StableDual
end

