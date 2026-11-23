module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HausdorffOfModuleTopologyFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocalLatticeRepresentationSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankIotaLetter
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.NL.IotaLetterRank

theorem finrank_iota_letter : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ c : ZMod (finrank ℚ_[l] ↥(K0 K)), finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) = finrank ↥LL.1 T.V := by
  intro D HW F Cm l _ K LL hG T hV c
  unfold Formalism.MainNotions.DeltaInvariantLattices.ιDi
  rw [← (Submodule.equivMapOfInjective _ (GlobalTheory.NL.PhiD.iota_injective _) _).finrank_eq]
  exact (GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).2 _ hV

end GlobalTheory.NL.IotaLetterRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstAdmissibilityAtOfParts
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem firstAdmissibilityAt_of_parts : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HodgeL bkP i s → (∀ v, NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v) → NegCount bkP i s → IsotypicValuationAtRing bkP i s := by
  intro D bkP i s h1 h2 h3 h4
  exact ⟨h1, h2, fun v => (h3 v).1, fun v => (h3 v).2, h4⟩

end GlobalTheory.TripleGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.Decompl

theorem fontaine_and_decompletion :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm9 D HW F :=
  fun D HW F l _ K s LL h =>
    ⟨GlobalTheory.Cyc.FontW.main D HW F l K s LL h, GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBounds
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.FontaineAdm

theorem fontaine_bounds : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm8 D := by
  intro D l _ K LL T
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.dcris_finite_le_of_tied (D.locT l) K LL T.V T.ρ
  refine ⟨⟨h1, h2⟩, fun τ => ?_⟩
  obtain ⟨hd, -⟩ := GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ
  exact ⟨(hd τ).1, (hd τ).2.1⟩

end GlobalTheory.Per.FontaineAdm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepTupleRelationMemPowSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepTuple_relation_mem_pow_span : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (c N : ℕ) (cs : Fin m → Om l), (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∀ G : Γ →₀ ℤ_[l], (G.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = 0 → ∃ f' : Γ →₀ ℤ_[l], (G.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ N • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) := by
  first | (exact @GlobalTheory.CovKer.kerB) | (exact GlobalTheory.CovKer.kerB) | (intros; apply GlobalTheory.CovKer.kerB  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepTupleSpanSaturationBoundStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepTuple_span_saturation_bound : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∃ u : ℕ, ∀ N M : ℕ, N + u ≤ M → ∀ H : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) ∈ GlobalTheory.TraceConjugationCover.latL t M → ∃ H' : Γ →₀ ℤ_[l], (H.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) = (l : Om l) ^ N • (H'.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) := by
  first | (exact @GlobalTheory.CovSat.satA) | (exact GlobalTheory.CovSat.satA) | (intros; apply GlobalTheory.CovSat.satA  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesPairStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenbergWiles_pair_alt : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1) → ∀ (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ C : Set (H1 ρ'), (∀ y : Z1 ρ', Submodule.Quotient.mk y ∈ C ↔ (∀ v ∉ S, ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧ ∀ v ∈ S, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) → Finite C ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card W ^ InfinitePlace.nrComplexPlaces F = Nat.card C * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  first | exact @GlobalTheory.PairFormula.greenbergWiles_pair | exact GlobalTheory.PairFormula.greenbergWiles_pair | (intros; apply GlobalTheory.PairFormula.greenbergWiles_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesGoodPart
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.HkGoodStable

theorem hkF_mem_V0 : ∀ (D : D7), CommG D → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
    ∀ x ∈ V0 D.nexp i j b, D.nexp.hkF i j b k P x ∈ V0 D.nexp i j b := by
  intro D hC i hi j hj b k P hk x hx
  have hc : ∀ g z, D.nexp.actG i j b g (D.nexp.hkF i j b k P z) = D.nexp.hkF i j b k P (D.nexp.actG i j b g z) :=
    fun g z => LinearMap.congr_fun (hC i hi b j hj g k P hk) z
  have hcomm : ∀ a, Commute (MonoidAlgebra.lift (FractionRing (D.ntw.O i))
      (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) a) (D.nexp.hkF i j b k P) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      rw [MonoidAlgebra.lift_of]
      exact LinearMap.ext fun z => hc g z
    | add a a' ha ha' => rw [map_add (f := _)]; exact ha.add_left ha'
    | smul c a ha => rw [map_smul]; exact ha.smul_left c
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  refine Submodule.mem_map.mpr ⟨D.nexp.hkF i j b k P y, ?_, ?_⟩
  · simp only [Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe] at hy ⊢
    intro u
    have h := hy u
    rw [sub_eq_zero] at h ⊢
    rw [hc, h, map_smul]
  · exact LinearMap.congr_fun (hcomm (D.nexp.eAlg i b)) y

end GlobalTheory.HkGoodStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrAAndNatural
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.HerrFull

theorem fontaine_decompletion (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    adm9 D HW F := fun l _ K s LL h =>
  ⟨GlobalTheory.Cyc.FontW.main D HW F l K s LL h, GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

theorem herr_a_and_natural :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime]
      (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      HerrAat (sit D.loc HW l (D.locA l) K s LL h) ∧
        HerrAsat (sit D.loc HW l (D.locA l) K s LL h) ∧ ((HW l).W K s LL h).ClNat := by
  intro D HW F l _ K s LL h
  have h9 := fontaine_decompletion D HW F
  have h1 := GlobalTheory.HerrClass.herr_a D HW F h9 l K s LL h
  exact ⟨h1.1, h1.2, GlobalTheory.HerrNatural.clNat D HW F h9 l K s LL h⟩

end GlobalTheory.HerrFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrClassOfCocycleValues
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.HerrClassUniq

theorem cocycle_eq {l : ℕ} [Fact l.Prime] {G V LL : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] [T2Space LL]
    [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (a : G → V → V) (c c' : G → V) (hc : Continuous c) (hc' : Continuous c')
    (ha : ∀ x, a 1 x = x)
    (hcc : ∀ g h, c (g * h) = c g + a g (c h)) (hcc' : ∀ g h, c' (g * h) = c' g + a g (c' h))
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1) (hker : ∀ h, lam h = 1 → c h = c' h) (hg₀ : c g₀ = c' g₀) :
    c = c' := by
  have h1 : c 1 = 0 := by
    have := hcc 1 1
    simpa [ha] using this
  have h1' : c' 1 = 0 := by
    have := hcc' 1 1
    simpa [ha] using this
  let S : Subgroup G :=
    { carrier := {g | c g = c' g}
      mul_mem' := fun {a b} ha hb => by
        change c (a * b) = c' (a * b)
        rw [hcc, hcc', show c a = c' a from ha, show c b = c' b from hb]
      one_mem' := by
        change c 1 = c' 1
        rw [h1, h1']
      inv_mem' := fun {a} ha => by
        change c a⁻¹ = c' a⁻¹
        have e1 := hcc a⁻¹ a
        have e2 := hcc' a⁻¹ a
        rw [inv_mul_cancel, h1, show c a = c' a from ha] at e1
        rw [inv_mul_cancel, h1'] at e2
        exact add_right_cancel (e1.symm.trans e2) }
  have hS : IsClosed (S : Set G) := by
    have : {g | c g = c' g} = ⋂ f : Module.Dual LL V, {g | f (c g) = f (c' g)} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      refine ⟨fun h f => by rw [h], fun h => ?_⟩
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff LL]
      intro f
      rw [map_sub, h f, sub_self]
    change IsClosed {g | c g = c' g}
    rw [this]
    refine isClosed_iInter fun f => ?_
    have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
    exact isClosed_eq (hf.comp hc) (hf.comp hc')
  funext g
  have hcl : IsClosed (lam '' (S : Set G)) := (hS.isCompact.image hlam).isClosed
  have hsub : Set.range (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) ⊆ lam '' (S : Set G) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨g₀ ^ n, S.zpow_mem (show g₀ ∈ S from hg₀) n, ?_⟩
    rw [map_zpow, h₀, ← ofAdd_zsmul]
    simp
  have hd : DenseRange (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) :=
    PadicInt.denseRange_intCast
  have hmem : lam g ∈ lam '' (S : Set G) := hcl.closure_subset_iff.2 hsub (hd (lam g))
  obtain ⟨x, hx, hxg⟩ := hmem
  have h2 : g * x⁻¹ ∈ S := hker _ (by rw [map_mul, map_inv, hxg, mul_inv_cancel])
  have h3 : g ∈ S := by simpa using S.mul_mem h2 hx
  exact h3

variable {l : ℕ} [Fact l.Prime]


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem val_eq_of_Zf {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K))
    (c c' : ↥(latticeCocycles (resLat T H))) (b : TW (RW LL) T) (g : ↥H) (e : Zf AI T H c b g = Zf AI T H c' b g) :
    (c : ↥H → T.V) g = (c' : ↥H → T.V) g := by
  unfold Zf at e
  exact congrArg Subtype.val ((GlobalTheory.WittTensorFixed.main l K LL T).2.2 (add_right_cancel e))


set_option maxHeartbeats 1000000 in
theorem cocycle_eq_lat {K LL : FinExt l} (T : Lt K LL) (H : Subgroup ↥(GK K)) (hH : IsClosed (H : Set ↥(GK K)))
    (c c' : ↥(latticeCocycles (resLat T H)))
    (lam : ↥H →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : ↥H)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1)
    (hker : ∀ h, lam h = 1 → (c : ↥H → T.V) h = (c' : ↥H → T.V) h)
    (hg₀ : (c : ↥H → T.V) g₀ = (c' : ↥H → T.V) g₀) : c = c' := by
  haveI := GlobalTheory.HerrClassMaps.compact_GK K
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.1 hH.isCompact
  haveI := T.mtop
  exact Subtype.ext (cocycle_eq (LL := ↥LL.1) (V := T.V) (fun (g : ↥H) (x : T.V) => T.ρ (g : ↥(GK K)) x) c c' c.2.1.1 c'.2.1.1
    (fun x => by simp) c.2.1.2 c'.2.1.2 lam hlam g₀ h₀ hker hg₀)


set_option maxHeartbeats 2000000 in
theorem class_of_values : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → (∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g = 0) → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ := by
  intro D HW F l _ K s LL h T c b y z hyz g₀ hg₀ hb hk hz
  refine (cl_fit D HW F K s LL h T y z hyz b hb).elim fun cW hW => ?_
  refine (lam_exists D HW K s LL h).elim fun lam hl => ?_
  have e : c = cW := cocycle_eq_lat T _ hl.2.2.2.2 c cW lam hl.1 g₀ ((hl.2.2.1 g₀).2 hg₀)
    (fun g hg => val_eq_of_Zf (D.locA l) T _ c cW b g
      ((hk g ((hl.2.1 g).1 hg)).trans (hW.2.1 g ((hl.2.1 g).1 hg)).symm))
    (val_eq_of_Zf (D.locA l) T _ c cW b g₀ (hz.trans (hW.2.2 g₀ hg₀).symm))
  exact (congrArg Submodule.Quotient.mk e).trans hW.1

end GlobalTheory.NL.HerrClassUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocycleOfWittTensorRelations
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.HerrCocycleCriterion

theorem herr_of_tie {O D M : Type} [CommRing O] [AddCommGroup D] [Module O D] [AddCommGroup M]
    [Module O M] (γ φ : D →ₗ[O] D) (g Φ : M →ₗ[O] M) (j : D →ₗ[O] M) (hj : Function.Injective j)
    (y z : D) (b t : M) (hγ : j (γ y) = g (j y)) (hφ : j (φ z) = Φ (j z))
    (hc : Φ (g b) = g (Φ b)) (ht : Φ t = t) (hy : Φ b - b = j y) (hz : t + (g b - b) = j z) :
    (y, z) ∈ herrCocycles γ φ := by
  simp only [herrCocycles, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply]
  apply hj
  rw [map_zero, map_add (f := _), map_neg, map_sub, map_sub, hγ, hφ, ← hy, ← hz, map_add (f := _), map_sub, map_sub,
    hc, ht]
  abel

theorem TWmap_one {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {R : Type} [CommRing R]
    [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (t : ↥T.L.T) :
    TWmap f T ((1 : R) ⊗ₜ[O] t) = (1 : R) ⊗ₜ[O] t := by
  simp [TWmap]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem cocyc : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (b : TW (RW LL) T) (y z : ((HW l).W K s LL h).DD T) (g₀ : ↥((HW l).W K s LL h).GKs), ((HW l).W K s LL h).resΓ (g₀ : ↥(GK K)) = ((HW l).W K s LL h).gam → TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → Zf (D.locA l) T ((HW l).W K s LL h).GKs c b g₀ = ((F l).E K s LL h).tie.jD T z → (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T := by
  intro D HW F l _ K s LL h T c b y z g₀ hg hy hz
  have h1 := ((F l).E K s LL h).tie.jD_act T (g₀ : ↥(GK K)) y
  rw [hg] at h1
  exact herr_of_tie _ _ _ _ _ (((F l).E K s LL h).tie.jD_inj T) y z b _ h1
    (((F l).E K s LL h).tie.jD_φ T z)
    (GlobalTheory.HerrClassMaps.TWmap_act _ _ (GlobalTheory.HerrClassMaps.phi_gRW (D.locA l) LL _) T _ b)
    (TWmap_one _ T _) hy hz

end GlobalTheory.NL.HerrCocycleCriterion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeAdaptedBasisGaloisActionBdRPlusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeAdaptedBasis_galois_action_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → (ρ g).map ((aDp l).comp (Per.zA l)) * H.V.map (Per.σDp (g : GQ l)) * Matrix.diagonal (fun j => aDp l w ^ H.p j) = aDp l w ^ H.q • H.V := by
  first | (exact @GlobalTheory.BKLim.GalAdapted.gal_V) | (exact GlobalTheory.BKLim.GalAdapted.gal_V) | (intros; apply GlobalTheory.BKLim.GalAdapted.gal_V  <;> assumption)
end

