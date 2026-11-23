module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviCongruence
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetCoeff

theorem exists_coeff_geometric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (m : ℕ), 1 ≤ m → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β, a * u * a⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β) → (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β, a⁻¹ * z * a ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β) → ∀ (y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) (Λ : ℂ), y ≠ 0 → (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y → ∃ (w : V) (l : Module.Dual ℂ V), (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧ (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧ ∀ j : ℕ, l (π (a ^ j) w) = Λ ^ j := by
  classical
  intro k _ _ _ _ N V _ _ π hπ h β _ m hm a ha hcomm _ hconj y Λ hy hyK hΛ
  have hKc := GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k N m
  have hKo := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m
  have hyfix : y ∈ GroundTheory.Automorphic.fixedVectors (GroundTheory.Automorphic.Parabolic.jacquetAction k N β π)
      ((GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m).subgroupOf
        (GroundTheory.Automorphic.Parabolic.levi k N β)) :=
    fun g hg => hyK g (Subgroup.mem_subgroupOf.1 hg)
  obtain ⟨⟨w, hw⟩, hwy⟩ :=
    GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_congruenceSubgroup β hπ hm ⟨y, hyfix⟩
  have hqw : Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) w = y :=
    congrArg Subtype.val hwy
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π),
      f y = 1 := by
    have h0 : ¬ ∀ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π), f y = 0 :=
      fun h' => hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h')
    push_neg at h0
    obtain ⟨f, hf⟩ := h0
    exact ⟨(f y)⁻¹ • f, by simp [hf]⟩

  have hpowc : ∀ j : ℕ, ∀ g ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a ^ j * g = g * a ^ j := by
    intro j g hg
    exact ((show Commute a g from hcomm g hg).pow_left j)
  have hpowz : ∀ j : ℕ, ∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
      GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β,
      (a ^ j)⁻¹ * z * a ^ j ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
        GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β := by
    intro j
    induction j with
    | zero => intro z hz; simpa using hz
    | succ j ih =>
      intro z hz
      have := hconj _ (ih z hz)
      have e : (a ^ (j + 1))⁻¹ * z * a ^ (j + 1) = a⁻¹ * ((a ^ j)⁻¹ * z * a ^ j) * a := by
        rw [pow_succ]; group
      rwa [e]
  have hq : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) =
      Λ ^ j • y := by
    intro j
    induction j with
    | zero => simp [hqw]
    | succ j ih =>
      have e : π (a ^ (j + 1)) w = π a (π (a ^ j) w) := by
        rw [pow_succ', map_mul, Module.End.mul_apply]
      have e2 := GroundTheory.Automorphic.Parabolic.jacquetAction_mk (F := k) (n := N) (β := β) π ⟨a, ha⟩
        (π (a ^ j) w)
      rw [e]
      refine e2.symm.trans ?_
      rw [ih, map_smul, hΛ, smul_smul, pow_succ]
  have hkey : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype)
      (GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo (π (a ^ j) w) : V) =
      Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) := by
    intro j
    refine GroundTheory.Automorphic.Parabolic.mk_fixedProj_eq hπ.1 hKc hKo
      (GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' β hm)
      (fun z hz => ?_) (fun g hg => ?_)
    · have hz' := (Subgroup.mem_inf.1 (hpowz j z hz)).1
      have hzeq : z = a ^ j * ((a ^ j)⁻¹ * z * a ^ j) * (a ^ j)⁻¹ := by group
      have : π z (π (a ^ j) w) = π (a ^ j) (π ((a ^ j)⁻¹ * z * a ^ j) w) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [this, hw _ hz']
    · have hc := hpowc j g (Subgroup.mem_inf.1 hg).2
      rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply,
        hw g (Subgroup.mem_inf.1 hg).1]
  refine ⟨w, f ∘ₗ Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) ∘ₗ
      (GroundTheory.Automorphic.fixedVectors π
        (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)).subtype ∘ₗ
      GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo, hw, ?_, ?_⟩
  · intro g hg
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [GroundTheory.Automorphic.fixedProj_apply_act hπ.1 hKc hKo hg]
  · intro j
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hkey j, hq j, map_smul, hf, smul_eq_mul, mul_one]

end GlobalTheory.CompanionTheory.JacquetCoeff
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviFixedSubmodule
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetEigen


open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic GroundTheory.Automorphic.GLnLocal in
theorem exists_eigenvector_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → ∀ (W T : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π)) (Λ : ℂ), Λ ≠ 0 → T ≤ W → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w ∈ W) → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w - Λ • w ∈ T) → (∃ w ∈ W, w ∉ T) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π, y ≠ 0 ∧ (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) ∧ GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y := by
  intro k _ _ _ _ N V _ _ π hπ h β _hβ a ha hcomm W T Λ hΛ hTW hWst hWT hex
  obtain ⟨w₀, hw₀W, hw₀T⟩ := hex
  let J := GroundTheory.Automorphic.Parabolic.jacquetAction k N β π
  let KM : ℕ → Subgroup (GroundTheory.Automorphic.Parabolic.levi k N β) := fun m =>
    (congruenceSubgroup k N m).subgroupOf (GroundTheory.Automorphic.Parabolic.levi k N β)
  have hA := isAdmissible_jacquetRep (β := β) hπ
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (F := k) (n := N) (β := β)
    ((hA.1 w₀).mem_nhds (one_mem (stabilizerOf _ w₀)))
  have hfix₁ : w₀ ∈ fixedVectors J (KM m₁) := by
    have : w₀ ∈ fixedVectors (jacquetRep k N β π) (KM m₁) := fun x hx => hm₁ hx
    rwa [fixedVectors_jacquetRep_congruenceSubgroup] at this
  refine ⟨m₁, fun m hm => ?_⟩
  have hle : KM m ≤ KM m₁ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone k N hm (Subgroup.mem_subgroupOf.1 hx))
  have hfix : w₀ ∈ fixedVectors J (KM m) := fixedVectors_antitone _ hle hfix₁
  have hfin : FiniteDimensional ℂ (fixedVectors J (KM m)) := by
    have := hA.2 (KM m) (isCompact_subgroupOf_levi (isCompact_congruenceSubgroup k N m))
      (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup k N m))
    rwa [fixedVectors_jacquetRep_congruenceSubgroup] at this
  let A : Module.End ℂ _ := J ⟨a, ha⟩
  let W' : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) :=
    W ⊓ fixedVectors J (KM m)
  have hW'fin : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le inf_le_right
  have hst : ∀ w ∈ W', A w ∈ W' := by
    intro w hw
    refine ⟨hWst w hw.1, fun g hg => ?_⟩
    have hw2 := hw.2 g hg
    have hc : g * ⟨a, ha⟩ = ⟨a, ha⟩ * g := Subtype.ext (hcomm g g.2).symm
    show J g (J ⟨a, ha⟩ w) = J ⟨a, ha⟩ w
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    exact congrArg _ hw2
  let B : W' →ₗ[ℂ] W' := A.restrict hst
  let Tc : Submodule ℂ W' := T.comap W'.subtype
  have hw₀' : w₀ ∈ W' := ⟨hw₀W, hfix⟩
  have hsq : Tc.mkQ ∘ₗ B = (Λ • (LinearMap.id : (W' ⧸ Tc) →ₗ[ℂ] (W' ⧸ Tc))) ∘ₗ Tc.mkQ := by
    ext w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact hWT _ w.2.1
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts W' (W' ⧸ Tc) B
    (Λ • (LinearMap.id : (W' ⧸ Tc) →ₗ[ℂ] (W' ⧸ Tc))) Tc.mkQ (Submodule.mkQ_surjective _) hsq Λ
    (Tc.mkQ ⟨w₀, hw₀'⟩)
    (fun h0 => hw₀T (by simpa [Tc] using (Submodule.Quotient.mk_eq_zero Tc).1 h0))
    rfl hΛ
  refine ⟨y, fun h0 => hy0 (Subtype.ext h0), fun g hg => y.2.2 g (Subgroup.mem_subgroupOf.2 hg), ?_⟩
  exact congrArg Subtype.val hy

end GlobalTheory.CompanionTheory.JacquetEigen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleIrreducibleCentralScalar
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SchurCentre

theorem scalar_acts_by_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → ∀ t : kˣ, ∃ c : ℂ, ∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v := by
  intro k _ _ _ _ N V _ _ π hs hirr hadm t
  haveI := hirr

  have hz : ∀ g : GL (Fin N) k, g * Matrix.GeneralLinearGroup.scalar (Fin N) t =
      Matrix.GeneralLinearGroup.scalar (Fin N) t * g := by
    intro g
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  set z := Matrix.GeneralLinearGroup.scalar (Fin N) t with hzdef
  have hcomm : ∀ (g : GL (Fin N) k) (w : V), π g (π z w) = π z (π g w) := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]

  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    change (⊥ : Submodule ℂ V) = ⊤
    ext u
    simp [h u]

  let S : Subgroup (GL (Fin N) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  let K : Subgroup (GL (Fin N) k) := GlobalTheory.SplitWeil.KO k (Fin N) ⊓ S
  have hKo : IsOpen (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N)).inter (hs v)
  have hKc : IsCompact (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin N)).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)
  haveI hfd : FiniteDimensional ℂ (fixed π K) := hadm.2 K hKo hKc
  have hmem : ∀ w : V, w ∈ fixed π K ↔ ∀ h : K, π (h : GL (Fin N) k) w = w := by
    intro w
    show (∀ h : K, _ = _) ↔ _
    simp
  have hvK : v ∈ fixed π K := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (fixed π K) :=
    ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ w ∈ fixed π K, π z w ∈ fixed π K := by
    intro w hw
    refine (hmem _).2 fun h => ?_
    rw [hcomm, (hmem w).1 hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((π z).restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : π z (w : V) = c • (w : V) := by
    have := congrArg Subtype.val hw.apply_eq_smul
    simpa using this

  let f : Representation.IntertwiningMap π π :=
    { toLinearMap := π z - c • LinearMap.id
      isIntertwining' := by
        intro g
        ext u
        simp [hcomm] }
  refine ⟨c, fun u => ?_⟩
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · exfalso
    apply hw0
    apply hb.1
    show π z (w : V) - c • (w : V) = f 0
    rw [hwc, sub_self, map_zero]
  · have := congrArg (fun F : Representation.IntertwiningMap π π => F u) h0
    have h1 : π z u - c • u = 0 := this
    exact sub_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SchurCentre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockCentralElementCommutesLeviStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
private theorem block_zj_eq_diagonal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ)
    (j : Fin h) :
    ((leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => if Zl.JC.blockIdx d hd i ≤ j then (t : k) else 1 := by
  ext i l
  obtain ⟨⟨a, i'⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, l'⟩, rfl⟩ := (stdBlocks d hd).surjective l
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hil : i' = l'
    · subst hil
      by_cases haj : a ≤ j
      · simp [Zl.JC.zj, Zl.JC.blockIdx, haj, Matrix.GeneralLinearGroup.scalar]
      · simp [Zl.JC.zj, Zl.JC.blockIdx, haj]
    · have hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨a, l'⟩ := fun e => hil (by
        simpa using (stdBlocks d hd).injective e)
      rw [Matrix.diagonal_apply_ne _ hne]
      by_cases haj : a ≤ j
      · simp [Zl.JC.zj, haj, Matrix.GeneralLinearGroup.scalar, hil]
      · simp [Zl.JC.zj, haj, hil]
  · have hne : (stdBlocks d hd) ⟨a, i'⟩ ≠ (stdBlocks d hd) ⟨b, l'⟩ := fun e => hab (by
      simpa using congrArg Sigma.fst ((stdBlocks d hd).injective e))
    rw [leviEmb_apply_ne k _ _ hab, Matrix.diagonal_apply_ne _ hne]


set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_central_element_commutes_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h), ∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * y = y * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) := by
  intro k _ _ _ _ h N d hd t j y hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, block_zj_eq_diagonal]
  ext i l
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hil : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l
  · rw [hil]
    exact mul_comm _ _
  · have h0 : (y : Matrix (Fin N) (Fin N) k) i l = 0 :=
      GroundTheory.Automorphic.Parabolic.mem_levi.1 hy i l hil
    rw [h0, mul_zero, zero_mul]

end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotone
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BlockIndex

theorem sum_castLE_eq_range {h : ℕ} (d : Fin h → ℕ) (a : Fin h) :
    ∑ b : Fin a, d (Fin.castLE a.2.le b) =
      ∑ c ∈ Finset.range a, (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) c := by
  rw [← Fin.sum_univ_eq_sum_range (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) a]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dite_eq_left (b.2.trans a.2)] <;> rfl

theorem partial_sum_succ_le {h : ℕ} (d : Fin h → ℕ) {a b : Fin h} (hab : b < a) :
    ∑ c : Fin b, d (Fin.castLE b.2.le c) + d b ≤ ∑ c : Fin a, d (Fin.castLE a.2.le c) := by
  have hsub : Finset.range ((b : ℕ) + 1) ⊆ Finset.range a := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (show (b : ℕ) + 1 ≤ a from hab))
  have key := Finset.sum_le_sum_of_subset (f := fun c => if hc : c < h then d ⟨c, hc⟩ else 0) hsub
  rw [Finset.sum_range_succ, dite_eq_left b.2] at key
  rw [GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d b, GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d a]
  exact key

theorem stdBlocks_lt_of_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {a b : Fin h} (hab : b < a)
    (x : Fin (d a)) (y : Fin (d b)) : stdBlocks d hd ⟨b, y⟩ < stdBlocks d hd ⟨a, x⟩ := by
  rw [Fin.lt_def, GlobalTheory.SmGL.stdBlocks_val,
    GlobalTheory.SmGL.stdBlocks_val]
  have h1 := GlobalTheory.CompanionTheory.BlockIndex.partial_sum_succ_le d hab
  have h2 := y.2
  omega

theorem blockIdx_monotone : ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), Monotone (Zl.JC.blockIdx d hd) := by
  intro h N d hd i j hij
  by_contra H
  rw [not_le] at H
  have H' : ((GlobalTheory.SmGL.stdBlocks d hd).symm j).1 <
      ((GlobalTheory.SmGL.stdBlocks d hd).symm i).1 := H
  have key := GlobalTheory.CompanionTheory.BlockIndex.stdBlocks_lt_of_lt d hd H'
    ((GlobalTheory.SmGL.stdBlocks d hd).symm i).2
    ((GlobalTheory.SmGL.stdBlocks d hd).symm j).2
  simp only [Sigma.eta, Equiv.apply_symm_apply] at key
  exact absurd hij (not_le.mpr key)

end GlobalTheory.CompanionTheory.BlockIndex
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliOperatorsCommute
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.CapComm

open Formalism.REAL

theorem commute_qdet_of {A : Type} [Ring A] [Algebra ℂ A] {k : ℕ} {X : Fin k → Fin k → A} {x : A}
    (h : ∀ a b, Commute x (X a b)) (u : ℂ) : Commute x (qdet X u) := by
  have hm : ∀ a b, X a b ∈ Subalgebra.centralizer ℂ ({x} : Set A) := fun a b =>
    (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact (h a b).eq
  have hq : qdet X u ∈ Subalgebra.centralizer ℂ ({x} : Set A) := by
    unfold qdet qminor
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
    refine Subalgebra.list_prod_mem _ fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    unfold Tm
    refine Subalgebra.add_mem _ ?_ (hm _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 hq x rfl

theorem qdet_commute_self {A : Type} [Ring A] [Algebra ℂ A] {k : ℕ} {X : Fin k → Fin k → A}
    (hX : GlRel X) (u v : ℂ) : Commute (qdet X u) (qdet X v) :=
  commute_qdet_of (fun a b => qDetCentral A k X hX u a b) v

theorem capR_capS_commute (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ)
    (u v : ℂ) :
    Commute (capR r s τ u) (capR r s τ v) ∧ Commute (capR r s τ u) (capS r s τ v) ∧
      Commute (capS r s τ u) (capS r s τ v) := by
  have hE := glRel_Eop (E := E) (a := r + s) τ
  refine ⟨?_, ?_, ?_⟩
  · exact qdet_commute_self (GlobalTheory.CapHC.glRel_restrict hE _ (Fin.castAdd_injective _ _)) _ _
  · exact (GlobalTheory.CapHC.qdet_comm hE _ _).symm
  · exact qdet_commute_self (GlobalTheory.CapHC.glRel_restrict hE _ (Fin.natAdd_injective _ _)) _ _

end GlobalTheory.CompanionTheory.CTFin.CapComm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterActsByScalarOnCyclic
section
open PositivityTheory.RgBcC.RealD (kF)

namespace GlobalTheory.CompanionTheory.ModelS

theorem eq_smul_of_commute_of_ev : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  intro n V _ _ F1 F2 hfin z hz ev c hev hS x
  set A := Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = kF F1 F2 a b} with hA
  set y : V := z x - c • x with hy
  obtain ⟨S₁, hfd, hyS₁, hst⟩ := hfin y
  have hpres : ∀ T ∈ A, ∀ w ∈ S₁, T w ∈ S₁ := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      exact hst a b
    | algebraMap r =>
      intro w hw
      simpa [Module.algebraMap_end_apply] using S₁.smul_mem r hw
    | add S T _ _ hS' hT' =>
      intro w hw
      exact S₁.add_mem (hS' w hw) (hT' w hw)
    | mul S T _ _ hS' hT' =>
      intro w hw
      exact hS' _ (hT' w hw)
  have hcomm : ∀ T ∈ A, z * T = T * z := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      have h1 := (hz a b).1
      have h2 := (hz a b).2
      show z * (F1 a b + F2 a b) = (F1 a b + F2 a b) * z
      rw [mul_add, add_mul, h1, h2]
    | algebraMap r => exact (Algebra.commutes r z).symm
    | add S T _ _ hS' hT' => rw [mul_add, add_mul, hS', hT']
    | mul S T _ _ hS' hT' => rw [← mul_assoc, hS', mul_assoc, hT', mul_assoc]
  let S : Submodule ℂ V := (Subalgebra.toSubmodule A).map (LinearMap.applyₗ y)
  have hmem : ∀ w, w ∈ S ↔ ∃ T ∈ A, T y = w := by
    intro w
    simp [S, Submodule.mem_map]
  have hle : S ≤ S₁ := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    exact hpres T hT y hyS₁
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
  have hSst : ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨kF F1 F2 a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, rfl⟩) hT, rfl⟩
  have hSev : ∀ w ∈ S, ev w = 0 := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    have hzT : T (z x) = z (T x) := (LinearMap.congr_fun (hcomm T hT) x).symm
    rw [hy, map_sub, map_smul, hzT, map_sub, map_smul, hev, smul_eq_mul, sub_self]
  have hyS : y ∈ S := (hmem y).2 ⟨1, A.one_mem, rfl⟩
  exact sub_eq_zero.1 (hS S hSfd hSst hSev y hyS)

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExistsStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  first | exact @GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | exact GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | (intros; apply GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy <;> assumption)
end

