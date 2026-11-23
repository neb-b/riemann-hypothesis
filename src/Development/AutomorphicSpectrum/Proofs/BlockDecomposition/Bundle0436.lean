module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0412
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerCharZeroDimSupport
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem interNumRed_eq_one_of_eq_singleton {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    [Algebra K Γ(X, ⊤)] (hp : IsProjOver (strHom K (X := X))) (Z : Closeds X) {w : X}
    (hZ : (Z : Set X) = {w}) (P : Fin 0 → LB X) : interNumRed K Z P = 1 := by
  letI := algebraΓAlong K (redι Z)
  have hk := appTop_algebraMap_along K (redι Z)
  have hX : IsProper (strHom K (X := X)) := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have hrange : Set.range (redι Z) = {w} := (range_redι Z).trans hZ

  have hsub : Subsingleton (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    refine ⟨fun a b => (redι Z).isEmbedding.injective ?_⟩
    have ha : redι Z a = w := by
      have : redι Z a ∈ Set.range (redι Z) := ⟨a, rfl⟩
      rwa [hrange] at this
    have hb : redι Z b = w := by
      have : redι Z b ∈ Set.range (redι Z) := ⟨b, rfl⟩
      rwa [hrange] at this
    rw [ha, hb]
  have hne : Nonempty (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    have : w ∈ Set.range (redι Z) := by rw [hrange]; rfl
    obtain ⟨a, -⟩ := this
    exact ⟨a⟩
  obtain ⟨p⟩ := hne
  have hAff : IsAffine (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p) (U := ⊤) trivial
    have hUt : U = ⊤ := top_le_iff.1 fun q _ => (Subsingleton.elim q p) ▸ hpU
    subst hUt
    haveI : IsAffine (⊤ : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens).toScheme := hU
    exact IsAffine.of_isIso (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.topIso.inv
  haveI : Nonempty (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := ⟨p⟩
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    isIntegral_red (hZ ▸ isIrreducible_singleton)
  have hpr : IsProper (strHom K (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    rw [← comp_strHom hk]
    infer_instance
  haveI : IsFinite (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : Module.Finite K Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    have hf := IsFinite.finite_app (strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ⊤
      (isAffineOpen_top _)
    have hi : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    have hc := hf.comp hi
    have e : algebraMap K Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) =
        ((strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme).app ⊤).hom.comp
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom :=
      RingHom.ext (algebraMap_eq_strHom K (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)
    rw [← RingHom.finite_algebraMap, e]
    exact hc
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K)
    (K := Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤))
  have e1 : interNumRed K Z P =
      chi K (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    change interNumOn K (redι Z) P = _
    exact (interNumOn_eq_interNum_pull hk isEmptyElim).trans (interNum_of_isEmpty K _ _)
  rw [e1, chi_structureModule_of_isAffine]
  have e2 := (LinearEquiv.ofBijective (Algebra.linearMap K
    Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤)) hbij).finrank_eq
  rw [← e2]
  simp

theorem chi_eq_ncard_support : ∀ {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)], IsProjOver (strHom K (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (0 : ℕ) → (∀ x : X, Module.length (X.presheaf.stalk x) (F.presheaf.stalk x :) ≤ 1) → chi K F = ((support F).ncard : ℤ) ∧ ∀ x ∈ support F, IsClosed ({x} : Set X) := by
  intro K _ _ X _ hp F _ hd hlen
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  have hdim0 : ∀ w ∈ support F,
      topologicalKrullDim (closure ({w} : Set X)) = ((0 : ℕ) : WithBot ℕ∞) := by
    intro w hw
    have hle := (GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.dim_closure_le_suppDim hw).trans hd
    have hne : topologicalKrullDim (closure ({w} : Set X)) ≠ ⊥ := by
      rw [Ne, topologicalKrullDim_eq_bot_iff]
      exact not_isEmpty_of_nonempty (α := (closure ({w} : Set X) : Set X))
        (h := ⟨⟨w, subset_closure rfl⟩⟩)
    obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
    rw [← ha] at hle ⊢
    have : a ≤ 0 := by exact_mod_cast hle
    have : a = 0 := le_antisymm this bot_le
    subst this
    rfl
  have hcl : ∀ x ∈ support F, IsClosed ({x} : Set X) := by
    intro x hx
    refine isClosed_of_closure_subset fun y hy => ?_
    have hys : y ∈ support F :=
      (isClosed_support F).closure_subset_iff.2 (Set.singleton_subset_iff.2 hx) hy
    exact (GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.eq_of_mem_closure hd (hdim0 y hys) x hx hy).symm
  have hfin : (support F).Finite := by
    obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_support F)
    rw [hS]
    refine hSf.sUnion fun t ht => ?_
    have hg := (hSi t ht).isGenericPoint_genericPoint_closure
    have hgt : (hSi t ht).genericPoint ∈ t := by
      have := hg.mem
      rwa [(hSc t ht).closure_eq] at this
    have hgs : (hSi t ht).genericPoint ∈ support F := by
      rw [hS]
      exact ⟨t, ht, hgt⟩
    have e : t = {(hSi t ht).genericPoint} := by
      have := hg.def
      rw [(hSc t ht).closure_eq, (hcl _ hgs).closure_eq] at this
      exact this.symm
    rw [e]
    exact Set.finite_singleton _
  refine ⟨?_, hcl⟩
  have hP : ∀ i : Fin 0, ((finZeroElim : Fin 0 → LB X) i).IsLB := isEmptyElim
  have h := GlobalTheory.CompanionTheory.Ar.IntersectionNumberLength.interNum_eq_sum_length_mul_interNumRed K X hp (Fin 0)
    finZeroElim hP F (by simpa using hd) hfin.toFinset (fun w hw _ => hfin.mem_toFinset.2 hw)
  rw [interNum_of_isEmpty] at h
  rw [h, Set.ncard_eq_toFinset_card _ hfin, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hws : w ∈ support F := hfin.mem_toFinset.1 hw
  have hlen1 : Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) = 1 := by
    refine le_antisymm (hlen w) (ENat.one_le_iff_ne_zero.2 fun h0 => ?_)
    have := Module.length_eq_zero_iff.1 h0
    exact (mem_support_iff.1 hws).exists_pair_ne.elim fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)
  rw [hlen1, interNumRed_eq_one_of_eq_singleton hp _ (w := w) (hcl w hws).closure_eq]
  simp

end GlobalTheory.CompanionTheory.KoszulCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvaluationMapsLinear
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Lin

open GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem muD_add {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) {φ₁ φ₂ : (Fin n → k) → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    @smInt _ _ (borel _) _ _ (muD k n) (φ₁ + φ₂) =
      @smInt _ _ (borel _) _ _ (muD k n) φ₁ + @smInt _ _ (borel _) _ _ (muD k n) φ₂ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  exact smInt_add (muD k n) l₁ c₁ l₂ c₂

theorem muD_smul {W : Type} [AddCommGroup W] [Module ℂ W] (n : ℕ) (c : ℂ) {φ : (Fin n → k) → W}
    (l : IsLocallyConstant φ) (h : HasCompactSupport φ) :
    @smInt _ _ (borel _) _ _ (muD k n) (c • φ) = c • @smInt _ _ (borel _) _ _ (muD k n) φ := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI : MeasureTheory.IsFiniteMeasureOnCompacts (muD k n) := by
    unfold muD
    infer_instance
  have e : (⇑(c • LinearMap.id : W →ₗ[ℂ] W) ∘ φ) = c • φ := rfl
  rw [← e, smInt_linear (muD k n) (c • LinearMap.id : W →ₗ[ℂ] W) l h]
  rfl

variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

def tw (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V :=
  fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y)

theorem tw_add (ψ : AddChar k Circle) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (f + g) y = tw ψ f y + tw ψ g y :=
  funext fun _ => smul_add _ _ _

theorem tw_smul (ψ : AddChar k Circle) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    tw ψ (c • f) y = c • tw ψ f y :=
  funext fun d => by
    show (_ : ℂ) • (c • evX f _) = c • ((_ : ℂ) • evX f _)
    exact smul_comm _ _ _

theorem tw_lc (ψ : AddChar k Circle) (hψ : Continuous ψ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    IsLocallyConstant (tw ψ f y) := by
  have h1 : IsLocallyConstant (fun d : Fin (t + 1) → k => ψ (d (Fin.last t))) :=
    (GlobalTheory.IrredSB.char_isLocallyConstant ψ hψ).comp_continuous (continuous_apply _)
  have h2 : IsLocallyConstant (fun d : Fin (t + 1) → k =>
      (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ)) :=
    h1.comp (fun z : Circle => (((Circle.toUnits z)⁻¹ : ℂˣ) : ℂ))
  exact IsLocallyConstant.comp₂ h2 (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y).1 (fun a b => a • b)

theorem tw_cs (ψ : AddChar k Circle) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    HasCompactSupport (tw ψ f y) := by
  refine (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y).2.mono fun d hd h0 => hd ?_
  have h0' : evX f (dEmb k i t d * y) = 0 := h0
  show (_ : ℂ) • evX f (dEmb k i t d * y) = 0
  rw [h0', smul_zero]

theorem intO_add (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (f + g) y = intO f y + intO g y :=
  muD_add (t + 1) (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y).1 (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y).2
    (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ g y).1 (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ g y).2

theorem intO_smul (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intO (c • f) y = c • intO f y :=
  muD_smul (t + 1) c (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y).1 (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y).2

theorem intC_add (ψ : AddChar k Circle) (hψ : Continuous ψ) (f g : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (f + g) y = intC ψ f y + intC ψ g y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_add ψ f g y)).trans
    (muD_add (t + 1) (tw_lc ψ hψ f y) (tw_cs ψ f y) (tw_lc ψ hψ g y) (tw_cs ψ g y))

theorem intC_smul (ψ : AddChar k Circle) (hψ : Continuous ψ) (c : ℂ) (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    intC ψ (c • f) y = c • intC ψ f y :=
  (congrArg (@smInt _ _ (borel _) _ _ (muD k (t + 1))) (tw_smul ψ c f y)).trans
    (muD_smul (t + 1) c (tw_lc ψ hψ f y) (tw_cs ψ f y))

theorem scaled_add {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u : ℂ)
    {a b c : A} (h : a = b + c) : u • T a = u • T b + u • T c := by
  rw [h, map_add (f := _), smul_add]

theorem scaled_smul {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (T : A →ₗ[ℂ] B) (u c : ℂ)
    {a b : A} (h : a = c • b) : u • T a = c • u • T b := by
  rw [h, map_smul, smul_comm]

theorem eC_eO_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f g : XS τ σ) (c : ℂ),
    eC ψ (f + g) = eC ψ f + eC ψ g ∧ eC ψ (c • f) = c • eC ψ f ∧ eO ψ (f + g) = eO ψ f + eO ψ g ∧ eO ψ (c • f) = c • eO ψ f := by
  intro k _ _ _ _ i t ψ hψ τ σ _ _ f g c
  refine ⟨funext fun m => ?_, funext fun m => ?_, funext fun m => ?_, funext fun m => ?_⟩
  · exact scaled_add (qC τ σ) _ (intC_add ψ hψ f g _)
  · exact scaled_smul (qC τ σ) _ c (intC_smul ψ hψ c f _)
  · exact scaled_add (qO τ σ ψ) _ (intO_add f g _)
  · exact scaled_smul (qO τ σ ψ) _ c (intO_smul c f _)

end GlobalTheory.CompanionTheory.BZPhiPG.Lin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteLeviStableChains
section
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvStableChains

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def chainsInL (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) : Submodule ℂ (Cq n V) where
  carrier := {x | SuppL (inUU lev) x ∧ DegL d x ∧ ∀ A, x A ∈ S}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    have key : ∀ A, (x + y) A ≠ 0 → x A ≠ 0 ∨ y A ≠ 0 := fun A h => by
      by_contra hc
      push Not at hc
      exact h (by simp [hc.1, hc.2])
    refine ⟨fun A h => ?_, fun A h => ?_, fun A => S.add_mem (hx3 A) (hy3 A)⟩
    · rcases key A h with h' | h'
      · exact hx1 A h'
      · exact hy1 A h'
    · rcases key A h with h' | h'
      · exact hx2 A h'
      · exact hy2 A h'
  zero_mem' := ⟨fun A h => absurd rfl h, fun A h => absurd rfl h, fun A => S.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3⟩
    have key : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A h h0 => h (by simp [h0])
    exact ⟨fun A h => hx1 A (key A h), fun A h => hx2 A (key A h), fun A => S.smul_mem c (hx3 A)⟩

theorem finiteDimensional_chainsInL (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (chainsInL lev d S) := by
  let L : chainsInL lev d S →ₗ[ℂ] (Finset (Lt n) → S) :=
    LinearMap.pi fun A => LinearMap.codRestrict S ((LinearMap.proj A).comp (chainsInL lev d S).subtype)
      fun x => x.2.2.2 A
  refine Module.Finite.of_injective L fun x y h => Subtype.ext (funext fun A => ?_)
  exact congrArg Subtype.val (congrFun h A)

theorem Lv_apply (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cq n V)
    (A : Finset (Lt n)) :
    Lv lev E1 E2 p q x A = kA E1 E2 p q (x A) +
      ∑ l : Lt n, ∑ k : Lt n, if inUU lev l then adCL false p q l k • creL k (annL l x) A else 0 := by
  simp only [Lv, adLL, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, liftL_apply]
  congr 1
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [Module.End.mul_apply]

theorem creL_annL_mem {S : Submodule ℂ V} {x : Cq n V} (hx : ∀ A, x A ∈ S) (l k : Lt n) (A : Finset (Lt n)) :
    creL k (annL l x) A ∈ S := by
  rw [creL_apply]
  split_ifs
  · refine S.smul_mem _ ?_
    rw [annL_apply]
    split_ifs
    · exact S.zero_mem
    · exact S.smul_mem _ (hx _)
  · exact S.zero_mem

theorem inUU_of_adCL {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {l k : Lt n}
    (h : adCL false p q l k ≠ 0) (hl : inUU lev l) : inUU lev k := by
  by_cases c1 : q = l.2.1.1 ∧ k.1 = (false ^^ l.1) ∧ k.2.1 = (p, l.2.1.2)
  · show lev k.2.1.1 < lev k.2.1.2
    rw [c1.2.2]
    show lev p < lev l.2.1.2
    rw [hpq, c1.1]
    exact hl
  by_cases c2 : l.2.1.2 = p ∧ k.1 = (false ^^ l.1) ∧ k.2.1 = (l.2.1.1, q)
  · show lev k.2.1.1 < lev k.2.1.2
    rw [c2.2.2]
    show lev l.2.1.1 < lev q
    rw [← hpq, ← c2.1]
    exact hl
  · exact absurd (by rw [adCL, if_neg c1, if_neg c2, sub_zero]) h

theorem Lv_ne {lev : Fin n → ℕ} {E1 E2 : Fin n → Fin n → Module.End ℂ V} {p q : Fin n} {x : Cq n V}
    {A : Finset (Lt n)} (h : Lv lev E1 E2 p q x A ≠ 0) :
    kA E1 E2 p q (x A) ≠ 0 ∨ ∃ l k, inUU lev l ∧ adCL false p q l k ≠ 0 ∧ creL k (annL l x) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [Lv_apply, hc.1, zero_add]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
  split_ifs with hl
  · by_cases h0 : adCL false p q l k = 0
    · rw [h0, zero_smul]
    · rw [hc.2 l k hl h0, smul_zero]
  · rfl

theorem term_suppL {lev : Fin n → ℕ} {d : ℕ} {p q : Fin n} (hpq : lev p = lev q) {x : Cq n V}
    (hx : SuppL (inUU lev) x) (hd : DegL d x) {A : Finset (Lt n)} {l k : Lt n} (h0 : adCL false p q l k ≠ 0)
    (h : creL k (annL l x) A ≠ 0) : (∀ j ∈ A, inUU lev j) ∧ A.card = d := by
  obtain ⟨hk, h1⟩ := creL_ne h
  obtain ⟨h2, h3⟩ := annL_ne h1
  have hs := hx _ h3
  have hi : inUU lev l := hs l (mem_insert_self _ _)
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases e : j = k
    · exact e ▸ inUU_of_adCL hpq h0 hi
    · exact hs j (mem_insert_of_mem (mem_erase.2 ⟨e, hj⟩))
  · have e1 := hd _ h3
    rw [card_insert_of_notMem h2] at e1
    have e2 := card_erase_add_one hk
    omega

theorem Lv_mem_chainsInL {lev : Fin n → ℕ} {d : ℕ} {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    {S : Submodule ℂ V} (hS : ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) {p q : Fin n} (hpq : lev p = lev q)
    {x : Cq n V} (hx : x ∈ chainsInL lev d S) : Lv lev E1 E2 p q x ∈ chainsInL lev d S := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hk : ∀ A, kA E1 E2 p q (x A) ≠ 0 → x A ≠ 0 := fun A h h0 => h (by rw [h0, map_zero])
  refine ⟨fun A h => ?_, fun A h => ?_, fun A => ?_⟩
  · rcases Lv_ne h with h' | ⟨l, k, -, h0, h'⟩
    · exact hx1 A (hk A h')
    · exact (term_suppL hpq hx1 hx2 h0 h').1
  · rcases Lv_ne h with h' | ⟨l, k, -, h0, h'⟩
    · exact hx2 A (hk A h')
    · exact (term_suppL hpq hx1 hx2 h0 h').2
  · rw [Lv_apply]
    refine S.add_mem (hS p q _ (hx3 A)) (S.sum_mem fun l _ => S.sum_mem fun k _ => ?_)
    split_ifs
    · exact S.smul_mem _ (creL_annL_mem hx3 l k A)
    · exact S.zero_mem

theorem exists_stable : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cq n V),
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) →
    SuppL (inUU lev) y → DegL d y →
    ∃ T : Submodule ℂ (Cq n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppL (inUU lev) x ∧ DegL d x) ∧
      ∀ p q : Fin n, lev p = lev q → ∀ x ∈ T, Lv lev E1 E2 p q x ∈ T := by
  intro n lev V _ _ E1 E2 d y hF hy hd
  choose Sf hfd hmem hSt using hF
  let S : Submodule ℂ V := ⨆ A, Sf (y A)
  have : ∀ A, FiniteDimensional ℂ (Sf (y A)) := fun A => hfd _
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _
  have hSs : ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S := fun a b v hv =>
    (iSup_le fun A z hz => Submodule.mem_iSup_of_mem A (hSt _ a b z hz) : S ≤ S.comap (kA E1 E2 a b)) hv
  refine ⟨chainsInL lev d S, finiteDimensional_chainsInL lev d S,
    ⟨hy, hd, fun A => Submodule.mem_iSup_of_mem A (hmem _)⟩, fun x hx => ⟨hx.1, hx.2.1⟩,
    fun p q hpq x hx => Lv_mem_chainsInL hSs hpq hx⟩

end GlobalTheory.CompanionTheory.LvStableChains
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
section
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AutLevel

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

theorem finEmb_eq_finGL (k : AdelicGLn.FiniteAdelicGL E a) :
    AutomorphicForm.finEmb E a k = finGL E a k := by
  apply (AdelicGLn.prodEquiv E a).injective
  rw [AutomorphicForm.prodEquiv_finEmb]
  have s1 : ∀ x, (sFin E x).1 = 0 := fun _ => rfl
  have s2 : ∀ x, (sFin E x).2 = x := fun _ => rfl
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).1 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).1 + (sFin E (k i j)).1
    rw [s1, s1, sub_zero, add_zero]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
  · change k.1 i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).2 + (sFin E (k i j)).2
    rw [s2, s2]
    have h1 : ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 = (1 : Matrix (Fin a) (Fin a) (Af E)) i j := by
      by_cases h : i = j
      · subst h
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        rfl
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
        rfl
    rw [h1, sub_self, zero_add]

theorem exists_open_level : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → (∃ U : Subgroup (AdelicGLn.integralFiniteGL E a), IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) ∧
    ∀ (g : AdelicGLn.AdelicGL E a) (u : U), φ.1 (g * AutomorphicForm.finEmb E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a)) = φ.1 g) := by
  intro E _ _ _ a φ hφ
  let S : Subgroup (AdelicGLn.FiniteAdelicGL E a) :=
    { carrier := {k | finRep E a k φ = φ}
      mul_mem' := fun {x y} hx hy => by
        change finRep E a (x * y) φ = φ
        rw [map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := by
        change finRep E a 1 φ = φ
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {x} hx => by
        change finRep E a x⁻¹ φ = φ
        have h : finRep E a x⁻¹ (finRep E a x φ) = φ := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [hx] at h }
  refine ⟨S.subgroupOf (AdelicGLn.integralFiniteGL E a), ?_, ?_⟩
  · exact hφ.level.preimage continuous_subtype_val
  · intro g u
    have hu : finRep E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a) φ = φ :=
      Subgroup.mem_subgroupOf.1 u.2
    rw [finEmb_eq_finGL]
    exact congrArg (fun ψ : Sm E a => ψ.1 g) hu

end GlobalTheory.CompanionTheory.AutLevel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntertwinerEqZeroOfVanishOnHighestStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [AddCommGroup V] [Module ℂ V] (G : Fin n → Fin n → Module.End ℂ H) (D : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ R : H →ₗ[ℂ] V, (∀ a b w, R (G a b w) = D a b (R w)) → (∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v → R v = 0) → R = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest | exact GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest | (intros; apply GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest <;> assumption)
end

