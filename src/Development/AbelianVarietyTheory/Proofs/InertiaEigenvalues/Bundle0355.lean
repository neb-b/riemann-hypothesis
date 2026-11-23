module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedFiniteCohomologyQuotients
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.KerToDivisible

theorem torsion_finite_and_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ℓ : O) (hℓ0 : ℓ ≠ 0) (hℓ : ¬ IsUnit ℓ) (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ n}))
    (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Finite ↥(Submodule.torsion O M) ∧ ∃ k : ℕ, ∀ x ∈ Submodule.torsion O M, ℓ ^ k • x = 0 := by
  have hdvd : ∀ y : O, y ≠ 0 → ∃ n : ℕ, y ∣ ℓ ^ n := by
    intro y hy
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ
    have he : e ≠ 0 := by
      rintro rfl; apply hℓ; rw [hv, pow_zero, mul_one]; exact v.isUnit
    refine ⟨n, ?_⟩
    rw [hu, hv, mul_pow, Units.mul_left_dvd]
    apply Dvd.dvd.mul_left
    rw [← pow_mul]
    exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero he))
  haveI : Module.Finite O ↥(Submodule.torsion O M) :=
    Module.Finite.iff_fg.2 (IsNoetherian.noetherian _)
  obtain ⟨y, hy, hy0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    (Submodule.torsion_isTorsion (R := O) (M := M))
  obtain ⟨k, t, ht⟩ := hdvd y (nonZeroDivisors.ne_zero hy0)
  have hk : ∀ x : ↥(Submodule.torsion O M), ℓ ^ k • x = 0 := by
    intro x
    rw [ht, mul_comm, mul_smul, Submodule.mem_annihilator.1 hy x Submodule.mem_top, smul_zero]
  refine ⟨?_, k, fun x hx => congrArg Subtype.val (hk ⟨x, hx⟩)⟩
  have hT : Module.IsTorsionBy O ↥(Submodule.torsion O M) (ℓ ^ k) := fun x => hk x
  letI := hT.module
  haveI := hfin k
  haveI : IsScalarTower O (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) :=
    Module.IsTorsionBySet.isScalarTower ((Module.isTorsionBySet_span_singleton_iff _).mpr hT)
  haveI : Module.Finite (O ⧸ Ideal.span {ℓ ^ k}) ↥(Submodule.torsion O M) :=
    Module.Finite.of_restrictScalars_finite O _ _
  exact Module.finite_of_finite (O ⧸ Ideal.span {ℓ ^ k})

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
  [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
  {ρ : Representation LL G V}

theorem redT_mem_BQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    (a : ↥(latticeCocycles L)) (ha : (Submodule.Quotient.mk a : LatticeCohomology L) = 0) : redT L I a ∈ BQ L I hI := by
  rw [Submodule.Quotient.mk_eq_zero] at ha
  obtain ⟨x, hx, hxa⟩ := ha
  refine ⟨I.mkQ ⟨x, hx⟩, ?_⟩
  funext g
  have h1 : evT L g a = actT L g ⟨x, hx⟩ - ⟨x, hx⟩ := Subtype.ext (congrFun hxa g).symm
  show actQ L I hI g (I.mkQ ⟨x, hx⟩) - I.mkQ ⟨x, hx⟩ = I.mkQ (evT L g a)
  rw [h1, map_sub]
  rfl


omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] in
theorem exists_smul_mem [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ) (w : V) :
    ∃ b : O, b ≠ 0 ∧ b • w ∈ L.T := by
  first
  | exact @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarLattice.exists_ne_zero_smul_mem ..)

theorem exists_torsion_lift [IsDomain O] [IsFractionRing O LL] (L : Lattice (O := O) ρ)
    (hρ : ∀ m, Continuous fun g => ρ g m) (s : O) (σ : LL) (hs : algebraMap O LL s = σ) (hσ : σ ≠ 0)
    (c : G → ↥L.T ⧸ (Ideal.span {s} • ⊤ : Submodule O ↥L.T))
    (hc : (fun g => (Submodule.Quotient.mk (σ⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g)) : V ⧸ L.T)) ∈ BD L) :
    ∃ a : ↥(latticeCocycles L), (Submodule.Quotient.mk a : LatticeCohomology L) ∈ Submodule.torsion O (LatticeCohomology L) ∧
      redT L _ a = c := by
  obtain ⟨vb, hvb⟩ := hc
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ vb
  have h1 : ∀ g, (ρ g v - v) - σ⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∈ L.T := by
    intro g
    rw [← Submodule.Quotient.eq, ← congrFun hvb g, Submodule.Quotient.mk_sub]
    rfl
  have hspec : ∀ g, ∃ y : ↥L.T, (y : V) = Formalism.MainNotions.LocalSituation.liftQ L _ (c g) ∧
      Submodule.Quotient.mk y = c g := fun g =>
    ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (c g)).choose_spec⟩
  choose y hy hyc using hspec
  set w : V := σ • v with hw
  have h2 : ∀ g, ρ g w - w = (y g : V) + s • ((⟨_, h1 g⟩ : ↥L.T) : V) := by
    intro g
    rw [← algebraMap_smul LL s, hs, hy, hw, map_smul]
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hσ, one_smul]
    abel
  have h3 : ∀ g, ρ g w - w ∈ L.T := fun g => by
    rw [h2]; exact L.T.add_mem (y g).2 (L.T.smul_mem _ (h1 g))
  have hZ : (fun g => ρ g w - w) ∈ latticeCocycles L := by
    refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => h3 g⟩
    · simp_rw [sub_eq_add_neg]
      exact (hρ w).add continuous_const
    · simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
  refine ⟨⟨_, hZ⟩, ?_, ?_⟩
  · obtain ⟨b, hb, hbw⟩ := exists_smul_mem L w
    refine ⟨⟨b, mem_nonZeroDivisors_of_ne_zero hb⟩, ?_⟩
    show b • (Submodule.Quotient.mk ⟨_, hZ⟩ : LatticeCohomology L) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨b • w, hbw, ?_⟩
    funext g
    show ρ g (b • w) - b • w = b • (ρ g w - w)
    rw [smul_sub, LinearMap.map_smul_of_tower]
  · funext g
    rw [← hyc g]
    show (Submodule.Quotient.mk (evT L g ⟨_, hZ⟩) : ↥L.T ⧸ _) = _
    rw [Submodule.Quotient.eq, GlobalTheory.TateOrth.mem_span_smul_top]
    refine ⟨⟨_, h1 g⟩, Subtype.ext ?_⟩
    show (ρ g w - w) - y g = _
    rw [h2, add_sub_cancel_left]
    rfl

theorem exists_finset_red (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I)
    [Finite ↥(Submodule.torsion O (LatticeCohomology L))] :
    ∃ F : Finset (QuotientCohomology L I hI), F.card ≤ Nat.card ↥(Submodule.torsion O (LatticeCohomology L)) ∧
      ∀ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)),
        (Submodule.Quotient.mk a : LatticeCohomology L) ∈ Submodule.torsion O (LatticeCohomology L) → redT L I a = c →
        (Submodule.Quotient.mk c : QuotientCohomology L I hI) ∈ F := by
  classical
  letI := Fintype.ofFinite ↥(Submodule.torsion O (LatticeCohomology L))
  have key : ∀ t : ↥(Submodule.torsion O (LatticeCohomology L)), ∃ x : QuotientCohomology L I hI,
      ∀ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t →
        redT L I a = c → (Submodule.Quotient.mk c : QuotientCohomology L I hI) = x := by
    intro t
    by_cases h : ∃ (c : ↥(quotientCocycles L I hI)) (a : ↥(latticeCocycles L)), (Submodule.Quotient.mk a : LatticeCohomology L) = t ∧
        redT L I a = c
    · obtain ⟨c0, a0, h0, h0'⟩ := h
      refine ⟨Submodule.Quotient.mk c0, fun c a h1 h1' => ?_⟩
      rw [Submodule.Quotient.eq]
      have := redT_mem_BQ L I hI (a - a0) (by rw [Submodule.Quotient.mk_sub, h0, h1, sub_self])
      rw [map_sub, h0', h1'] at this
      exact this
    · exact ⟨0, fun c a h1 h1' => absurd ⟨c, a, h1, h1'⟩ h⟩
  choose ψ hψ using key
  refine ⟨Finset.univ.image ψ, ?_, fun c a ha hac => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Nat.card_eq_fintype_card, Finset.card_univ]
  · exact Finset.mem_image.2 ⟨⟨_, ha⟩, Finset.mem_univ _, (hψ ⟨_, ha⟩ c a rfl hac).symm⟩

theorem ker_bounded_gen [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
    (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (hfg : Module.Finite O (LatticeCohomology L))
    (ℓ : O) (σ : LL) (hs : algebraMap O LL ℓ = σ) (hσ : σ ≠ 0) (hℓ : ¬ IsUnit ℓ)
    (hfin : ∀ n : ℕ, Finite (O ⧸ Ideal.span {ℓ ^ n})) :
    ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI : StableSub L (Ideal.span {ℓ ^ r} • ⊤ : Submodule O ↥L.T)),
      ∃ F : Finset (QuotientCohomology L _ hI), F.card ≤ C0 ∧ ∀ c : ↥(quotientCocycles L _ hI),
        (fun g => (Submodule.Quotient.mk ((σ ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _
          ((c : G → ↥L.T ⧸ (Ideal.span {ℓ ^ r} • ⊤ : Submodule O ↥L.T)) g)) : V ⧸ L.T)) ∈ BD L →
        (Submodule.Quotient.mk c : QuotientCohomology L _ hI) ∈ F ∧
          (ℓ ^ k0) • (Submodule.Quotient.mk c : QuotientCohomology L _ hI) = 0 := by
  have hℓ0 : ℓ ≠ 0 := fun h => hσ (by rw [← hs, h, map_zero])
  obtain ⟨hF, k, hk⟩ := torsion_finite_and_killed ℓ hℓ0 hℓ hfin (LatticeCohomology L)
  refine ⟨Nat.card ↥(Submodule.torsion O (LatticeCohomology L)), k, fun r hI => ?_⟩
  obtain ⟨F, hFc, hFm⟩ := exists_finset_red L _ hI
  refine ⟨F, hFc, fun c hc => ?_⟩
  obtain ⟨a, ha, hac⟩ := exists_torsion_lift L hρ (ℓ ^ r) (σ ^ r)
    (by rw [map_pow, hs]) (pow_ne_zero _ hσ) _ hc
  refine ⟨hFm c a ha hac, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have := redT_mem_BQ L _ hI (ℓ ^ k • a)
    (by rw [Submodule.Quotient.mk_smul]; exact hk _ ha)
  rw [map_smul, hac] at this
  exact this

end Gen

theorem ker_bounded : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ), ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ F : Finset (QuotientCohomology LA' _ hI'), F.card ≤ C0 ∧ ∀ c' : ↥(quotientCocycles LA' _ hI'), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ BD LA' → (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') ∈ F ∧ (((l : ℕ) : O) ^ k0) • (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') = 0 := by
  intro hT l _ P K LL _ _ _ O _ _ hO A' LA'
  have hgc := GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO
  have hfg : Module.Finite O (LatticeCohomology LA') := GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'
  letI hD : IsDomain O := hO.1.choose
  haveI : IsDiscreteValuationRing O := hO.1.choose_spec.1
  haveI : IsFractionRing O LL := hO.1.choose_spec.2
  have hlLL : ((l : ℕ) : LL) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have hℓu : ¬ IsUnit ((l : ℕ) : O) :=
    GlobalTheory.DoubleAnnihilator.not_isUnit_of_adicComplete _ hgc.2.2.2
  exact ker_bounded_gen (G := ↥(GK K)) (LL := LL) (O := O) (V := A'.V) (ρ := A'.ρ) LA' A'.cont hfg
    ((l : ℕ) : O) ((l : ℕ) : LL) (map_natCast (algebraMap O LL) l) hlLL hℓu hgc.2.2.1

end GlobalTheory.KerToDivisible
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopesAdicTopologicalBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem envelopes_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X))
    (En₂ : Env bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)),
    Nonempty (TopBasis (BK.hf En.inl) bk.J (Digits l)) ∧
      ∃ ι : Type, Nonempty (TopBasis (BK.hf (En₂.inl.comp En.inl)) bk.J ι) := by
  intro l _ K bk En En₂
  have h1 : bk.J.map (BK.hf En.inl) =
      Ideal.span {(BK.hf En.inl) (l : bk.S)} ⊔ Ideal.span {(BK.hf En.inl) bk.E} := by
    simp only [BK.J, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have h2 : (BK.hf En.inl) (l : bk.S) = (l : En.Q.A) := map_natCast (BK.hf En.inl) l
  have h3 : En.Q.I = Ideal.span {(BK.hf En.inl) bk.E} := En.I_eq
  have hI : Ideal.span {(l : En.Q.A)} ⊔ En.Q.I = bk.J.map (BK.hf En.inl) :=
    (h1.trans (congrArg₂ (· ⊔ ·) (congrArg (fun x => Ideal.span {x}) h2) h3.symm)).symm
  have T₁ : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have T₂ : TopBasis En₂.inl.f (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) := En₂.tb
  have key := _root_.GlobalTheory.BSP.topBasis_comp_exists bk.S En.Q.A (BK.hf En.inl) bk.J (Digits l) T₁ En₂.Q.A En₂.inl.f
    (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) T₂ hI
  exact ⟨⟨T₁⟩, Digits l × Digits l, key.elim fun TC _ => ⟨TC⟩⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomImageXDeltaZeroLiftsUniformizer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem hf_X_δ_and_str : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (C : Obj l ↥(OL K)) (g : Hom bk.prism C),
    C.D.δ (BK.hf (bk := bk) g X) = 0 ∧
      Ideal.Quotient.mk C.I (BK.hf (bk := bk) g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  intro l _ K bk C g
  have hδX : (deltaS l bk.a).δ (X : (Wq l bk.a)⟦X⟧) = 0 := by
    have h := (deltaS l bk.a).φ_eq (X : (Wq l bk.a)⟦X⟧)
    have h2 : (deltaS l bk.a).φ (X : (Wq l bk.a)⟦X⟧) = X ^ l := frobS_X l bk.a
    rw [h2] at h
    have h3 : (l : (Wq l bk.a)⟦X⟧) * (deltaS l bk.a).δ X = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h3).resolve_left (l_ne_zero l bk.a)
  refine ⟨?_, ?_⟩
  · have h := g.f_δ (X : (Wq l bk.a)⟦X⟧)
    change C.D.δ (g.f X) = 0
    rw [← h]
    change g.f ((deltaS l bk.a).δ X) = 0
    rw [hδX]
    exact g.f.map_zero
  · refine g.f_str (bk.str.symm (Ideal.Quotient.mk _ X)) X ?_
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str (bk.str.symm (Ideal.Quotient.mk _ X))
    rw [RingEquiv.apply_symm_apply]

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameCocyclesLinked
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.LinkCocycle

theorem dvd_of_inclW {l : ℕ} [Fact l.Prime] (n : ℕ) : ∀ (a : Ainf l) (w : WCb l),
    inclW l a = (l : WCb l) ^ n * w → (l : Ainf l) ^ n ∣ a := by
  induction n with
  | zero => intro a w _; exact ⟨a, by simp⟩
  | succ n ih =>
    intro a w h
    obtain ⟨a₁, ha₁⟩ := GlobalTheory.HWL.TensorWitt.ainf_saturated_in_tiltWitt_prime a ((l : WCb l) ^ n * w) (by rw [h]; ring)
    obtain ⟨c, hc⟩ := ih a₁ w ha₁
    have h1 : a = (l : Ainf l) * a₁ := GlobalTheory.HWL.TensorWitt.inclW_injective (by
      rw [map_mul, map_natCast, ha₁, h]; ring)
    exact ⟨c, by rw [h1, hc]; ring⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N d ρ) (F' : Frame bk N' d' ρ') (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ (g : ↥(GK K)) i j, (l : Ainf l) ^ n ∣ (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g) i j := by
  intro l _ K bk N N' d d' n ρ ρ' F F' Pi R hPi hR g i j
  classical
  choose M hM using hPi g
  choose D hD using hR
  set c : WCb l := (l : WCb l) ^ n with hc
  set σ : WCb l →+* WCb l := ((galW l (g : GQ l) : WCb l ≃ₐ[ℤ_[l]] WCb l) : WCb l →+* WCb l) with hσ
  set T := F.T
  set T' := F'.T
  set P := zW Pi
  set A := zW (ρ g)
  set A' := zW (ρ' g)
  set Rw := (R.map bk.ev).map (inclW l)
  set Rgw := ((R.map bk.ev).map (Per.σA (g : GQ l))).map (inclW l)
  set E := (F.ε g).map (inclW l)
  set E' := (F'.ε g).map (inclW l)
  set Ds : Matrix (Fin d) (Fin d') (WCb l) := Matrix.of D
  set Mw : Matrix (Fin d) (Fin d') (WCb l) := zW (Matrix.of M)
  have e1 : A * T.map σ = T * E := F.gal g
  have e2 : A' * T'.map σ = T' * E' := F'.gal g
  have e3 : P * T' - T * Rw = c • Ds := Matrix.ext fun i j => by
    simpa [Ds, Rw, BK.evW, Matrix.map_map] using hD i j
  have e4 : P * T'.map σ - T.map σ * Rgw = c • Ds.map σ := by
    have hP : P.map σ = P := Matrix.ext fun i j => by simp [P, zW, σ]
    have hRg : Rw.map σ = Rgw := Matrix.ext fun i j => by simp [Rw, Rgw, σ, galW_inclW]
    have : (P * T' - T * Rw).map σ = (c • Ds).map σ := by rw [e3]
    rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul] at this
    rw [hP, hRg] at this
    rw [this]; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc, map_pow, map_natCast]
  have e5 : P * A' - A * P = c • Mw := by
    have hM' : Pi * ρ' g - ρ g * Pi = ((l : ℤ_[l]) ^ n) • Matrix.of M := Matrix.ext fun i j => by simpa using hM i j
    have : (Pi * ρ' g - ρ g * Pi).map (algebraMap ℤ_[l] (WCb l)) = (((l : ℤ_[l]) ^ n) • Matrix.of M).map (algebraMap ℤ_[l] (WCb l)) := by rw [hM']
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul] at this
    rw [this]; ext i j; simp [Mw, zW, c]
  have key : T * (E * Rgw - Rw * E') = (c • Ds) * E' - (c • Mw) * T'.map σ - A * (c • Ds.map σ) := by
    rw [← e3, ← e4, ← e5]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc T E, ← e1, ← e2]
    simp only [Matrix.mul_assoc]
    abel
  have key2 : T * (E * Rgw - Rw * E') = c • (Ds * E' - Mw * T'.map σ - A * Ds.map σ) := by
    rw [key, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_sub]
  have hT : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T ((Matrix.isUnit_iff_isUnit_det T).mp F.unit)
  have hX : E * Rgw - Rw * E' = c • (T⁻¹ * (Ds * E' - Mw * T'.map σ - A * Ds.map σ)) := by
    rw [← Matrix.mul_smul, ← key2, ← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hY : (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g).map (inclW l) =
      E * Rgw - Rw * E' := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]
  refine dvd_of_inclW n _ ((T⁻¹ * (Ds * E' - Mw * T'.map σ - A * Ds.map σ)) i j) ?_
  have := congrFun (congrFun (hY.trans hX) i) j
  simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hc] using this
end GlobalTheory.BKLim.LinkCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.OEmod

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

def ψ : bk.S →+* Cb l := (WittVector.constantCoeff (p := l) (R := Cb l)).comp bk.evW

theorem ψ_apply (s : bk.S) : ψ bk s = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
  simp [ψ, BK.evW, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem ψ_X : ψ bk X = algebraMap (OCb l) (Cb l) bk.flat := by
  rw [ψ_apply, bk.ev_X, WittVector.teichmuller_coeff_zero]

theorem cc_evW_X : WittVector.constantCoeff (bk.evW X) = algebraMap (OCb l) (Cb l) bk.flat := ψ_X bk

theorem cc_l_mul (y : WCb l) : WittVector.constantCoeff ((l : WCb l) * y) = 0 := by
  rw [WittVector.constantCoeff_apply, mul_comm]
  exact WittVector.mul_charP_coeff_zero y

theorem evW_X_eq : bk.evW X = WittVector.teichmuller l (algebraMap (OCb l) (Cb l) bk.flat) := by
  simp [BK.evW, bk.ev_X, inclW, WittVector.map_teichmuller]

theorem l_dvd_of_not_isUnit (a : ℕ) [NeZero a] (x : Wq l a) (h : ¬ IsUnit x) : (l : Wq l a) ∣ x := by
  by_cases h0 : x = 0
  · exact h0 ▸ dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero => exact absurd (by simpa using WittVector.isUnit_of_coeff_zero_ne_zero b hb) h
  | succ m => exact Dvd.intro _ (by rw [pow_succ', mul_assoc])

theorem exists_unit (s : bk.S) (hs : ψ bk s ≠ 0) :
    ∃ (k : ℕ) (s₁ : bk.S), IsUnit s₁ ∧ ψ bk s = ψ bk X ^ k * ψ bk s₁ := by
  have hex : ∃ i, IsUnit (coeff i s) := by
    by_contra hno
    push_neg at hno
    have hd : ∀ i, (l : Wq l bk.a) ∣ coeff i s := fun i => l_dvd_of_not_isUnit bk.a _ (hno i)
    choose c hc using hd
    have : s = (l : bk.S) * PowerSeries.mk c := by
      ext i
      rw [← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, hc i]
    apply hs
    rw [this, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  classical
  let k := Nat.find hex
  have hk : IsUnit (coeff k s) := Nat.find_spec hex
  have hlt : ∀ i < k, (l : Wq l bk.a) ∣ coeff i s := fun i hi =>
    l_dvd_of_not_isUnit bk.a _ (Nat.find_min hex hi)
  choose! c hc using hlt
  let s₁ : bk.S := PowerSeries.mk fun i => coeff (i + k) s
  let s₂ : bk.S := PowerSeries.mk fun i => if i < k then c i else 0
  have hs₁ : IsUnit s₁ := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
    exact hk
  have hsplit : s = X ^ k * s₁ + (l : bk.S) * s₂ := by
    ext i
    rw [map_add (f := _), coeff_X_pow_mul', ← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, coeff_mk]
    by_cases hi : i < k
    · rw [if_neg (by omega), if_pos hi, zero_add, hc i hi]
    · rw [if_pos (by omega), if_neg hi, mul_zero, add_zero, Nat.sub_add_cancel (by omega)]
  refine ⟨k, s₁, hs₁, ?_⟩
  conv_lhs => rw [hsplit]
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]

end GlobalTheory.BSP.OEmod

open GlobalTheory.BSP.OEmod in
theorem GlobalTheory.BSP.oe_mod_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S), algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)) ∧ (∀ s : bk.S, bk.evW s ∈ bk.OE) ∧ IsUnit (bk.evW X) ∧ (∀ w : WCb l, bk.evW X * w ∈ bk.OE → w ∈ bk.OE) ∧ ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), y⁻¹ ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  intro l _ K bk
  have hflat : bk.flat ≠ 0 := (_root_.GlobalTheory.BSP.AinfDiv.main l K bk).2.2.2.1
  have hf : algebraMap (OCb l) (Cb l) bk.flat ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hflat
  have hunit : IsUnit (bk.evW X) := by
    rw [evW_X_eq]
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [WittVector.teichmuller_coeff_zero]
    exact hf
  have h1 : ∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S),
      algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
    intro y
    rw [Subring.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨m, s, z, h⟩ := hw 1
      refine ⟨m, s, ?_⟩
      have := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) h
      rw [map_mul, map_pow, map_add (f := _), pow_one, cc_l_mul, add_zero, cc_evW_X] at this
      rw [this, ← ψ_apply]
      rfl
    · rintro ⟨m, s, h⟩
      obtain ⟨u, hu⟩ := hunit
      refine ⟨(↑(u⁻¹) : WCb l) ^ m * bk.evW s, fun n => ⟨m, s, 0, ?_⟩, ?_⟩
      · rw [mul_zero, add_zero, ← mul_assoc, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_mul]
      · have hc : WittVector.constantCoeff (bk.evW X) * WittVector.constantCoeff ((↑(u⁻¹) : WCb l)) = 1 := by
          rw [← map_mul, ← hu, Units.mul_inv, map_one]
        rw [cc_evW_X] at hc
        rw [map_mul, map_pow]
        have hs : WittVector.constantCoeff (bk.evW s) = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := ψ_apply bk s
        rw [hs, ← h, ← mul_assoc, ← mul_pow, mul_comm _ (algebraMap (OCb l) (Cb l) bk.flat), hc, one_pow, one_mul]
  refine ⟨h1, fun s n => ⟨0, s, 0, by simp⟩, hunit, fun w hw n => ?_, fun y hy => ?_⟩
  · obtain ⟨m, s, z, h⟩ := hw n
    exact ⟨m + 1, s, z, by rw [pow_succ, mul_assoc, h]⟩
  · by_cases hy0 : y = 0
    · rw [hy0, inv_zero]; exact Subring.zero_mem _
    obtain ⟨m, s, h⟩ := (h1 y).1 hy
    rw [← ψ_apply] at h
    have hs : ψ bk s ≠ 0 := by rw [← h]; exact mul_ne_zero (pow_ne_zero _ hf) hy0
    obtain ⟨k, s₁, ⟨t, rfl⟩, hk⟩ := exists_unit bk s hs
    rw [h1]
    refine ⟨k, ((X : bk.S) ^ m * ↑(t⁻¹) : bk.S), ?_⟩
    rw [← ψ_apply, map_mul, map_pow, ψ_X]
    rw [hk, ψ_X] at h
    have ht : ψ bk ↑t * ψ bk ↑(t⁻¹) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have ht0 : ψ bk ↑t ≠ 0 := left_ne_zero_of_mul_eq_one ht
    have hinv : ψ bk ↑(t⁻¹) = (ψ bk ↑t)⁻¹ := eq_inv_of_mul_eq_one_right ht
    rw [hinv]
    field_simp
    linear_combination -h
end
end

