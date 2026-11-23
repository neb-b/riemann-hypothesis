module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedInductionProductParabolicPiTensor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

section Family

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
  [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)]
  [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem exists_pi_subset
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    (U : Set (∀ a, Γ a)) (hU : U ∈ nhds (1 : ∀ a, Γ a)) :
    ∃ H : ∀ a, Subgroup (Γ a), (∀ a, IsOpen (H a : Set (Γ a))) ∧ (∀ a, IsCompact (H a : Set (Γ a))) ∧
      ((Subgroup.pi Set.univ H : Subgroup (∀ a, Γ a)) : Set (∀ a, Γ a)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  choose H hHo hHc hHs using fun a => hG a (t a) (ht a)
  refine ⟨H, hHo, hHc, fun x hx => hsub fun a _ => hHs a ?_⟩
  exact (Subgroup.mem_pi Set.univ).mp hx a (Set.mem_univ a)

theorem pi_compactOpen_basis
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U) :
    ∀ U ∈ nhds (1 : ∀ a, Γ a), ∃ K : Subgroup (∀ a, Γ a), IsOpen (K : Set (∀ a, Γ a)) ∧
      IsCompact (K : Set (∀ a, Γ a)) ∧ (K : Set (∀ a, Γ a)) ⊆ U := by
  intro U hU
  obtain ⟨H, hHo, hHc, hsub⟩ := exists_pi_subset hG U hU
  refine ⟨Subgroup.pi Set.univ H, ?_, ?_, hsub⟩
  · show IsOpen (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isOpen_set_pi Set.finite_univ fun a _ => hHo a
  · show IsCompact (Set.pi Set.univ fun a => (H a : Set (Γ a)))
    exact isCompact_univ_pi fun a => hHc a

theorem isAdmissible_piTensor [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a)) :
    IsAdmissible (piTensor ρ) := by
  refine ⟨isSmooth_piTensor fun a => (hρ a).1, fun K ho hc => ?_⟩
  obtain ⟨H, h1, h2, h3⟩ := exists_pi_subset hG _ (ho.mem_nhds (one_mem K))
  haveI : ∀ a, FiniteDimensional ℂ (fixed (ρ a) (H a)) := fun a => (hρ a).2 _ (h1 a) (h2 a)
  let M : (⨂[ℂ] a, fixed (ρ a) (H a)) →ₗ[ℂ] ⨂[ℂ] a, X a :=
    PiTensorProduct.map fun a => (fixed (ρ a) (H a)).subtype
  have hle : fixed (piTensor ρ) K ≤ LinearMap.range M := by
    intro w hw
    have hs := GlobalTheory.SmGL.IndTensor.mem_span_of_fixed (fun a => (hρ a).1) h2 w fun h hh =>
      GlobalTheory.ContraRefl.mem_fix.1 hw h (h3 hh)
    refine Submodule.span_le.2 ?_ hs
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨PiTensorProduct.tprod ℂ fun a => ⟨v a, hv a⟩, by simp [M]⟩
  exact Submodule.finiteDimensional_of_le hle

def pairForm (ρ : ∀ a, Representation ℂ (Γ a) (X a)) :
    (⨂[ℂ] a, X a) →ₗ[ℂ] (⨂[ℂ] a, smoothPart (ρ a).dual) →ₗ[ℂ] ℂ :=
  ((PiTensorProduct.dualDistrib (R := ℂ) (M := X)) ∘ₗ
    PiTensorProduct.map fun a => (smoothPart (ρ a).dual).subtype).flip

theorem pairForm_tprod (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (v : ∀ a, X a)
    (l : ∀ a, smoothPart (ρ a).dual) :
    pairForm ρ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ l) =
      ∏ a, (l a : Module.Dual ℂ (X a)) (v a) := by
  simp only [pairForm, LinearMap.flip_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
    PiTensorProduct.dualDistrib_apply, Submodule.subtype_apply]

theorem pairForm_invariant (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a)
    (s : ⨂[ℂ] a, X a) (t : ⨂[ℂ] a, smoothPart (ρ a).dual) :
    pairForm ρ (piTensor ρ g s) (piTensor (fun a => contra (ρ a)) g t) = pairForm ρ s t := by
  have hpt : ∀ v : ∀ a, X a, piTensor ρ g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun a => ρ a (g a) (v a)) := by
    intro v
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (ρ a).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ v) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  have hpt' : ∀ l : ∀ a, smoothPart (ρ a).dual, piTensor (fun a => contra (ρ a)) g (PiTensorProduct.tprod ℂ l) =
      PiTensorProduct.tprod ℂ (fun a => contra (ρ a) (g a) (l a)) := by
    intro l
    show PiTensorProduct.mapMonoidHom ((MonoidHom.pi fun a => (contra (ρ a)).comp (Pi.evalMonoidHom Γ a)) g)
      (PiTensorProduct.tprod ℂ l) = _
    rw [PiTensorProduct.mapMonoidHom_apply, PiTensorProduct.map_tprod]
    rfl
  refine PiTensorProduct.induction_on s (fun r v => ?_) (fun x y hx hy => ?_)
  · refine PiTensorProduct.induction_on t (fun r' l => ?_) (fun x y hx hy => ?_)
    · simp only [map_smul, LinearMap.smul_apply]
      rw [hpt, hpt', pairForm_tprod, pairForm_tprod]
      congr 2
      refine Finset.prod_congr rfl fun a _ => ?_
      show (l a : Module.Dual ℂ (X a)) (ρ a (g a)⁻¹ (ρ a (g a) (v a))) = (l a : Module.Dual ℂ (X a)) (v a)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · simp only [map_add (f := _), hx, hy]
  · simp only [map_add (f := _), LinearMap.add_apply, hx, hy]

theorem nonempty_equiv_piTensor_contra [∀ a, T2Space (Γ a)]
    (hG : ∀ a, ∀ U ∈ nhds (1 : Γ a), ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧
      IsCompact (K : Set (Γ a)) ∧ (K : Set (Γ a)) ⊆ U)
    {ρ : ∀ a, Representation ℂ (Γ a) (X a)} (hρ : ∀ a, IsAdmissible (ρ a))
    (hi : ∀ a, (ρ a).IsIrreducible) :
    Nonempty ((piTensor fun a => contra (ρ a)).Equiv (contra (piTensor ρ))) := by
  have hK : ∀ a, ∃ K : Subgroup (Γ a), IsOpen (K : Set (Γ a)) ∧ IsCompact (K : Set (Γ a)) := fun a => by
    obtain ⟨K, h1, h2, -⟩ := hG a Set.univ Filter.univ_mem
    exact ⟨K, h1, h2⟩
  choose K0 hK1 hK2 using hK
  have hschur : ∀ a, ∀ φ : X a →ₗ[ℂ] X a, (∀ g x, φ (ρ a g x) = ρ a g (φ x)) →
      ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) (X a) (ρ a) (hi a) (hρ a)
  have hci : ∀ a, (contra (ρ a)).IsIrreducible := fun a =>
    GlobalTheory.ContraRefl.contra_isIrreducible (hG a) (hρ a) (hi a)
  have hca : ∀ a, IsAdmissible (contra (ρ a)) := fun a =>
    GlobalTheory.SmGL.ContraTrace.isAdmissible_contra (hρ a)
  have hcschur : ∀ a, ∀ φ : smoothPart (ρ a).dual →ₗ[ℂ] smoothPart (ρ a).dual,
      (∀ g x, φ (contra (ρ a) g x) = contra (ρ a) g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id := fun a =>
    GlobalTheory.SchurAdm.schur_admissible (Γ a) (K0 a) (hK1 a) (hK2 a) _ (contra (ρ a)) (hci a) (hca a)
  have hI : (piTensor ρ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur ρ hi hschur
  have hI' : (piTensor fun a => contra (ρ a)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ hci hcschur
  have hCI : (contra (piTensor ρ)).IsIrreducible :=
    GlobalTheory.ContraRefl.contra_isIrreducible (pi_compactOpen_basis hG) (isAdmissible_piTensor hG hρ) hI
  have hB0 : pairForm ρ ≠ 0 := by
    have hne : ∀ a, ∃ v : X a, v ≠ 0 := fun a => by
      by_contra h
      push_neg at h
      apply (bot_ne_top : (⊥ : Subrepresentation (ρ a)) ≠ ⊤)
      apply Subrepresentation.ext
      ext x
      rw [h x]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    choose v hv using hne
    choose l hl using fun a => GlobalTheory.ContraRefl.exists_smooth_form_ne (hρ a).1 (hG a) (hv a)
    intro h0
    have h1 := pairForm_tprod ρ v l
    rw [h0] at h1
    exact Finset.prod_ne_zero_iff.2 (fun a _ => hl a) (by simpa using h1.symm)
  exact ⟨(GlobalTheory.InvPairing.pairMap (piTensor ρ) (isSmooth_piTensor fun a => isSmooth_contra (ρ a))
    (pairForm ρ) (pairForm_invariant ρ)).ofBijective (GlobalTheory.InvPairing.pairMap_bijective _ _ _ _ hB0 hI' hCI)⟩

end Family

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem contra_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    (contra x.rep).IsIrreducible :=
  GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k x.1)
    (hA k x.1 _ x.rep x.2.rep.smooth x.2.rep.irr) x.2.rep.irr

theorem contra_piTensor_rep (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    Nonempty ((piTensor fun a => contra (x a).rep).Equiv (contra (piTensor fun a => (x a).rep))) := by
  haveI : ∀ a, T2Space (GL (Fin (x a).1) k) := fun a => GlobalTheory.SplitFlip.t2Space_general_linear_group
  exact nonempty_equiv_piTensor_contra (Γ := fun a => GL (Fin (x a).1) k)
    (fun a => GlobalTheory.SqIntUnit.compactOpen_basis k (x a).1)
    (fun a => hA k (x a).1 _ (x a).rep (x a).2.rep.smooth (x a).2.rep.irr)
    fun a => (x a).2.rep.irr

theorem parInd_equiv_contra {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) V} {ρ : Representation ℂ (Levi k m) W}
    (hρ : IsSmooth ρ) (φ : Nonempty (σ.Equiv (contra ρ))) :
    Nonempty ((parInd e σ).Equiv (contra (parInd e ρ))) := by
  obtain ⟨φ⟩ := φ
  obtain ⟨ψ⟩ := InductionContragredient.nonempty_equiv (GlobalTheory.CompanionTheory.Glob.inductionContragredient k) e hρ
  exact ⟨(parIndEquiv e φ).trans ψ⟩

theorem contra_prodIrr_multiProd (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) :
    Nonempty ((multiProd (stdBlocks (fun a => (x a).1) hd) fun a => contra (x a).rep).Equiv
      (contra (prodIrr x hd))) :=
  parInd_equiv_contra (stdBlocks (fun a => (x a).1) hd)
    (isSmooth_piTensor fun a => (x a).2.rep.smooth) (contra_piTensor_rep hA x)

theorem contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), ∃ hd' : ∑ a, (dualCl (x a)).1 = N,
      Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr (fun a => dualCl (x a)) hd')) := by
  intro k _ _ _ _ hA h N x hd
  have hci := fun a => contra_rep_isIrreducible hA (x a)
  have hy : (fun a => dualCl (x a)) =
      fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a) :=
    funext fun a => dif_pos (hci a)
  have key : ∀ y : Fin h → IrrGL (k := k),
      y = (fun a => IrrGL.of (contra (x a).rep) (isSmooth_smoothRep _) (hci a)) →
      ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hd')) := by
    rintro _ rfl
    exact ⟨hd, (contra_prodIrr_multiProd hA x hd).map fun ψ => ψ.symm.trans
      (prodIrrEquiv hd (fun a => contra (x a).rep) (fun a => isSmooth_smoothRep _) hci)⟩
  exact key _ hy

end GlobalTheory.CompanionTheory.ContraProd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CptPartEqInf
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CptGen

theorem cptPart_eq_inf : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (T C : Subgroup G), IsCompact (C : Set G) → (∀ t ∈ T, IsCompact (closure (Subgroup.zpowers t : Set G)) → t ∈ C) → cptPart T = T ⊓ C := by
  intro G _ _ _ _ T C hC h
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    intro x hx
    exact ⟨hx.1, h x hx.1 hx.2⟩
  · intro x hx
    apply Subgroup.subset_closure
    refine ⟨hx.1, hC.of_isClosed_subset isClosed_closure ?_⟩
    exact closure_minimal (fun y hy => (Subgroup.zpowers_le.2 hx.2) hy) hC.isClosed

end GlobalTheory.CompanionTheory.CptGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaEqLatticeIndex
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

theorem delta_ne_zero (c : Matrix (Fin m) (Fin m) K) : delta c ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    (Finset.univ : Finset (Fin m × Fin m)) (fun p => c p.1 p.2)
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose r hr using fun (i j : Fin m) => RingHom.mem_rangeS.1 (hb (i, j) (Finset.mem_univ _))
  have hr' : ∀ i j, algebraMap (𝓞 K) K (r i j) = algebraMap (𝓞 K) K (b : 𝓞 K) * c i j := by
    intro i j
    rw [hr i j, Algebra.smul_def]
  let I : Ideal (𝓞 K) := Ideal.span {(b : 𝓞 K)}
  have hI : I ≠ ⊥ := fun h => hb0 (Ideal.span_singleton_eq_bot.1 h)
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let π : (Fin m → 𝓞 K) →+ (Fin m → 𝓞 K ⧸ I) :=
    AddMonoidHom.pi (fun i => (Ideal.Quotient.mk I).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hker : π.ker ≤ Kc c := by
    intro y hy
    have h0 : π y = 0 := AddMonoidHom.mem_ker.1 hy
    have hyI : ∀ j, y j ∈ I := fun j =>
      Ideal.Quotient.eq_zero_iff_mem.1 (congrFun h0 j)
    choose z hz using fun j => Ideal.mem_span_singleton'.1 (hyI j)
    change ∀ i : Fin m, ∃ o : 𝓞 K,
      algebraMap (𝓞 K) K o = c.mulVec (fun j => algebraMap (𝓞 K) K (y j)) i
    intro i
    refine ⟨∑ j, r i j * z j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, hr' i j, ← hz j, map_mul]
    ring
  have hfin : (π.ker).index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  exact ne_zero_of_dvd_ne_zero hfin (AddSubgroup.index_dvd_of_le hker)

theorem delta_eq_relIndex (c : Matrix (Fin m) (Fin m) K) :
    delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  classical
  let L := (lam c).toAddSubgroup
  let H : AddSubgroup L := (intVec K m).toAddSubgroup.addSubgroupOf L
  let f0 : (Fin m → 𝓞 K) →+ (Fin m → K) :=
    (c.mulVecLin.toAddMonoidHom).comp (AddMonoidHom.pi fun i =>
      (algebraMap (𝓞 K) K).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hmap : ∀ y, f0 y ∈ L := by
    intro y
    have : f0 y ∈ lam c := by
      unfold lam
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨fun j => algebraMap (𝓞 K) K (y j),
        fun j => ⟨y j, rfl⟩, rfl⟩)
    exact this
  let ψ : (Fin m → 𝓞 K) →+ L := f0.codRestrict L hmap
  let φ : (Fin m → 𝓞 K) →+ L ⧸ H := (QuotientAddGroup.mk' H).comp ψ
  have hker : Kc c = φ.ker := by
    ext y
    rw [AddMonoidHom.mem_ker]
    change _ ↔ (QuotientAddGroup.mk (ψ y) : L ⧸ H) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      have hx' : x ∈ lam c := hx
      unfold lam at hx'
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
      choose y hy using hv
      refine ⟨y, ?_⟩
      have hyv : (fun j => algebraMap (𝓞 K) K (y j)) = v := funext hy
      change (QuotientAddGroup.mk (ψ y) : L ⧸ H) = QuotientAddGroup.mk _
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have key : ((-(ψ y) + ⟨_, hx⟩ : L) : Fin m → K) = a := by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_neg]
        change -(c.mulVec (fun j => algebraMap (𝓞 K) K (y j))) + (a + c.mulVec v) = a
        rw [hyv]
        abel
      rw [key]
      exact ha
  show (Kc c).index = H.index
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
  rfl

theorem delta_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K),
    delta c ≠ 0 ∧ delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  intro K _ _ m c
  exact ⟨delta_ne_zero c, delta_eq_relIndex c⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorNormQuadraticExtension
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix nonZeroDivisors

theorem mem_den_iff {K : Type} [Field K] [NumberField K] (x : K) (a : 𝓞 K) :
    a ∈ HS.den K x ↔ ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * x := by
  rw [HS.den, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  show (∀ i : Fin 1, ∃ o, algebraMap (𝓞 K) K o = (a • fun _ : Fin 1 => x) i) ↔ _
  simp only [Pi.smul_apply, Algebra.smul_def]
  exact ⟨fun h => h 0, fun h _ => h⟩

theorem exists_bezout {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ a ∈ HS.den K x, ∃ c ∈ HS.den K x,
      algebraMap (𝓞 K) K a + algebraMap (𝓞 K) K c * x = 1 := by
  classical
  obtain ⟨S, hSdef⟩ : ∃ S : FractionalIdeal (𝓞 K)⁰ K,
      S = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ⊔ FractionalIdeal.spanSingleton (𝓞 K)⁰ x :=
    ⟨_, rfl⟩
  have h1S : (1 : K) ∈ S := by
    rw [hSdef]; exact (le_sup_left : FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) ≤ _)
      (FractionalIdeal.mem_spanSingleton_self _ _)
  have hxS : x ∈ S := by
    rw [hSdef]; exact (le_sup_right : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ _)
      (FractionalIdeal.mem_spanSingleton_self _ _)
  have hS : S ≠ 0 := by
    intro h
    rw [h] at h1S
    exact one_ne_zero ((FractionalIdeal.mem_zero_iff _).1 h1S)
  have hden : ∀ t ∈ S⁻¹, ∃ a ∈ HS.den K x, algebraMap (𝓞 K) K a = t := by
    intro t ht
    rw [FractionalIdeal.mem_inv_iff hS] at ht
    have ht1 : t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      have := ht 1 h1S
      rwa [mul_one] at this
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 ht1
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).1 (ht x hxS)
    exact ⟨a, (mem_den_iff x a).2 ⟨o, by rw [ho, ha]⟩, ha⟩
  have hsplit : ∀ T : FractionalIdeal (𝓞 K)⁰ K, S * T = FractionalIdeal.spanSingleton (𝓞 K)⁰ (1 : K) * T ⊔
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x * T := by
    intro T
    rw [hSdef, FractionalIdeal.sup_eq_add, FractionalIdeal.sup_eq_add, add_mul]
  have h1 : (1 : K) ∈ S * S⁻¹ := by
    rw [mul_inv_cancel₀ hS]; exact FractionalIdeal.one_mem_one _
  rw [hsplit S⁻¹, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_sup, Submodule.mem_sup] at h1
  obtain ⟨u, hu, v, hv, huv⟩ := h1
  rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul] at hu hv
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  obtain ⟨a, ha, ha'⟩ := hden u' hu'
  obtain ⟨c, hc, hc'⟩ := hden v' hv'
  refine ⟨a, ha, c, hc, ?_⟩
  rw [ha', hc', ← huv]
  ring

theorem den_algebraMap (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (x : F) :
    HS.den E (algebraMap F E x) = Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (HS.den F x) := by
  have tower : ∀ o : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) o) =
      algebraMap F E (algebraMap (𝓞 F) F o) := by
    intro o
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  apply le_antisymm
  · intro b hb
    obtain ⟨a, ha, c, hc, hac⟩ := exists_bezout x
    obtain ⟨o, ho⟩ := (mem_den_iff _ b).1 hb
    have key : b = algebraMap (𝓞 F) (𝓞 E) a * b + algebraMap (𝓞 F) (𝓞 E) c * o := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      have hac' := congrArg (algebraMap F E) hac
      simp only [map_add (f := _), map_mul, map_one] at hac'
      simp only [map_add (f := _), map_mul, tower, ho]
      linear_combination (-(algebraMap (𝓞 E) E b)) * hac'
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha))
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc))
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_den_iff]
    obtain ⟨o, ho⟩ := (mem_den_iff x a).1 ha
    exact ⟨algebraMap (𝓞 F) (𝓞 E) o, by rw [tower, tower, ho, map_mul]⟩

theorem absNorm_den_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E], Module.finrank F E = 2 → ∀ x : F,
      Ideal.absNorm (HS.den E (algebraMap F E x)) = Ideal.absNorm (HS.den F x) ^ 2 := by
  intro F E _ _ _ _ _ h2 x
  rw [den_algebraMap, Ideal.absNorm_algebraMap]
  congr 1
  rw [← h2]
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscrNormConductorEqDFOfUnramified
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem discrNormConductor_eq_dF_of_unramified :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker → χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
  intro F _ _ χ hχ
  have htop : χ.conductor = ⊤ := by
    have h := (χ.map_idealLevel_le_ker_iff (𝔪 := ⊤) top_ne_bot).1
      ((map_idealLevel_le_standardOpenSubgroup ⊤).trans hχ)
    rw [Ideal.dvd_iff_le, top_le_iff] at h
    exact h
  rw [HeckeCharacter.discrNormConductor, htop, Ideal.absNorm_top, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF]
  simp

end GlobalTheory.CompanionTheory.PartialZeta
end

