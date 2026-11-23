module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0148
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinEquivApply
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BKGal.CrisTensor

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

section Zl

@[reducible] def zlT (T : QLat LL) : Module ℤ_[l] ↥T.L.T := Module.compHom _ (algebraMap ℤ_[l] ↥(OL LL))

@[reducible] def zlV (T : QLat LL) : Module ℤ_[l] T.V := Module.compHom _ (algebraMap ℤ_[l] ℚ_[l])

@[reducible] def zlB (Pl : LocPrime l) : Module ℤ_[l] Pl.R.B := Module.compHom _ (algebraMap ℤ_[l] ℚ_[l])

attribute [local instance] zlT zlV zlB

theorem towT (T : QLat LL) : IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem towV (T : QLat LL) : IsScalarTower ℤ_[l] ℚ_[l] T.V :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem towB (Pl : LocPrime l) : IsScalarTower ℤ_[l] ℚ_[l] Pl.R.B :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

attribute [local instance] towT towV towB

def incl (T : QLat LL) : ↥T.L.T →ₗ[ℤ_[l]] T.V where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' z x := by
    change ((algebraMap ℤ_[l] ↥(OL LL) z • x : ↥T.L.T) : T.V) = algebraMap ℤ_[l] ℚ_[l] z • (x : T.V)
    rw [Submodule.coe_smul, ← algebraMap_smul ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z) (x : T.V),
      ← algebraMap_smul ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] z) (x : T.V)]
    rfl

theorem exists_pow_smul_mem (T : QLat LL) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem
  | (apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPowerScalar.exists_pow_smul_mem ..)

theorem zl_smul_V (T : QLat LL) (z : ℤ_[l]) (v : T.V) : z • v = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) • v := by
  change algebraMap ℤ_[l] ℚ_[l] z • v = _
  rw [← algebraMap_smul ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] z) v]
  rfl

theorem isLoc (T : QLat LL) : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (incl T) := by
  refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, ?_⟩⟩
  · have hs : ((s : ℤ_[l]) : ℚ_[l]) ≠ 0 := by
      rw [Ne, PadicInt.coe_eq_zero]; exact nonZeroDivisors.coe_ne_zero s
    have hs' : algebraMap ℚ_[l] ↥LL.1 ((s : ℤ_[l]) : ℚ_[l]) ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective]
    refine (Module.End.isUnit_iff _).2 ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, zl_smul_V, zl_smul_V] at hab
      exact smul_right_injective _ hs' hab
    · refine ⟨(algebraMap ℚ_[l] ↥LL.1 ((s : ℤ_[l]) : ℚ_[l]))⁻¹ • a, ?_⟩
      rw [Module.algebraMap_end_apply, zl_smul_V, smul_smul, mul_inv_cancel₀ hs', one_smul]
  · obtain ⟨n, hn⟩ := exists_pow_smul_mem T y
    have hl : ((l : ℤ_[l]) ^ n) ∈ nonZeroDivisors ℤ_[l] :=
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
    refine ⟨(⟨_, hn⟩, ⟨_, hl⟩), ?_⟩
    show ((l : ℤ_[l]) ^ n) • y = (l : ↥LL.1) ^ n • y
    rw [zl_smul_V]
    congr 1
    simp
  · simp only [one_smul]; exact Subtype.ext h

theorem hbc (T : QLat LL) : IsBaseChange ℚ_[l] (incl T) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] (incl T)).1 (isLoc T)

variable {Bc : Type} [CommRing Bc] [Algebra ℤ_[l] Bc] {Pl : LocPrime l}

def ringLin (eB : Pl.R.B ≃+* Bc) (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z) :
    Bc ≃ₗ[ℤ_[l]] Pl.R.B :=
  { eB.symm.toAddEquiv with
    map_smul' := fun z b => by
      show eB.symm (z • b) = algebraMap ℤ_[l] ℚ_[l] z • eB.symm b
      rw [Algebra.smul_def z b, map_mul, Algebra.smul_def]
      congr 1
      rw [RingEquiv.symm_apply_eq]
      exact (hz z).symm }

def swapLat (T : QLat LL) : TW (↥(OL LL) ⊗[ℤ_[l]] Bc) T ≃ₗ[↥(OL LL)] ↥T.L.T ⊗[↥(OL LL)] (↥(OL LL) ⊗[ℤ_[l]] Bc) :=
  TensorProduct.comm ↥(OL LL) (↥(OL LL) ⊗[ℤ_[l]] Bc) ↥T.L.T

def cancelCoeff (T : QLat LL) : ↥T.L.T ⊗[↥(OL LL)] (↥(OL LL) ⊗[ℤ_[l]] Bc) ≃ₗ[↥(OL LL)] ↥T.L.T ⊗[ℤ_[l]] Bc :=
  AlgebraTensorModule.cancelBaseChange ℤ_[l] ↥(OL LL) ↥(OL LL) ↥T.L.T Bc

def changeRing (T : QLat LL) (eB : Pl.R.B ≃+* Bc)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z) :
    ↥T.L.T ⊗[ℤ_[l]] Bc ≃ₗ[ℤ_[l]] Pl.R.B ⊗[ℤ_[l]] ↥T.L.T :=
  (TensorProduct.congr (LinearEquiv.refl ℤ_[l] ↥T.L.T) (ringLin eB hz)).trans (TensorProduct.comm ℤ_[l] ↥T.L.T Pl.R.B)


variable (Pl) in
def invertPrime (T : QLat LL) : Pl.R.B ⊗[ℤ_[l]] ↥T.L.T ≃ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.B :=
  (AlgebraTensorModule.cancelBaseChange ℤ_[l] ℚ_[l] ℚ_[l] Pl.R.B ↥T.L.T).symm.trans
     ((TensorProduct.congr (LinearEquiv.refl ℚ_[l] Pl.R.B) (hbc T).equiv).trans
       (TensorProduct.comm ℚ_[l] Pl.R.B T.V))

def addEquiv (T : QLat LL) (eB : Pl.R.B ≃+* Bc)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z) :
    TW (↥(OL LL) ⊗[ℤ_[l]] Bc) T ≃+ T.V ⊗[ℚ_[l]] Pl.R.B :=
  (((swapLat T).trans (cancelCoeff T)).toAddEquiv.trans (changeRing T eB hz).toAddEquiv).trans (invertPrime Pl T).toAddEquiv

theorem addEquiv_tmul (T : QLat LL) (eB : Pl.R.B ≃+* Bc)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] Bc z)
    (o : ↥(OL LL)) (b : Bc) (x : ↥T.L.T) :
    addEquiv T eB hz ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = (((o • x : ↥T.L.T)) : T.V) ⊗ₜ[ℚ_[l]] eB.symm b := by
  simp [addEquiv, swapLat, cancelCoeff, changeRing, invertPrime, ringLin, IsBaseChange.equiv_tmul, incl]

end Zl

variable {Pl : LocPrime l}

theorem addEquiv_smul (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (c : ↥(OL LL)) (w : TW (OB l ↥(OL LL)) T) :
    addEquiv T eB hz (c • w) = c • addEquiv T eB hz w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add x y hx hy =>
    rw [smul_add, map_add (f := _), map_add (f := _)]
    exact (congrArg₂ (· + ·) hx hy).trans (smul_add c _ _).symm
  | tmul y x =>
    rw [TensorProduct.smul_tmul']
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, zero_tmul, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [smul_add, add_tmul, add_tmul, map_add (f := _), map_add (f := _)]
      exact (congrArg₂ (· + ·) h₁ h₂).trans (smul_add c _ _).symm
    | tmul o b =>
      have e : (((c • o) • x : ↥T.L.T) : T.V) = (c : ↥LL.1) • ((o • x : ↥T.L.T) : T.V) := by
        rw [smul_assoc, Submodule.coe_smul, ← algebraMap_smul ↥LL.1 c]
        rfl
      rw [TensorProduct.smul_tmul', addEquiv_tmul, addEquiv_tmul, e]
      exact (TensorProduct.smul_tmul' (c : ↥LL.1) _ _).symm

def linEquiv (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z) :
    TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B :=
  (addEquiv T eB hz).toLinearEquiv (addEquiv_smul T eB hz)

theorem linEquiv_apply (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (w : TW (OB l ↥(OL LL)) T) : linEquiv T eB hz w = addEquiv T eB hz w := rfl

theorem linEquiv_one (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (x : ↥T.L.T) :
    linEquiv T eB hz ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B) := by
  rw [linEquiv_apply, Algebra.TensorProduct.one_def, addEquiv_tmul, one_smul, map_one]

theorem linEquiv_act (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (hact : ∀ (g : GQ l) (b : Pl.R.B), eB (Pl.actQ g b) = Per.σB g (eB b))
    (g : Gl l) (w : TW (OB l ↥(OL LL)) T) :
    linEquiv T eB hz (actB (sQ l) T g w) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (linEquiv T eB hz w) := by
  rw [linEquiv_apply, linEquiv_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    exact congrArg₂ (· + ·) hx hy
  | tmul y x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [zero_tmul, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [add_tmul, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
      exact congrArg₂ (· + ·) h₁ h₂
    | tmul o b =>
      have h1 : actB (sQ l) T g ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.σB (g : GQ l) b) ⊗ₜ[↥(OL LL)] T.actT g x := rfl
      rw [h1, addEquiv_tmul, addEquiv_tmul]
      simp only [actVB, AlgebraTensorModule.map_tmul]
      congr 1
      · rw [Submodule.coe_smul, Submodule.coe_smul, ← algebraMap_smul ↥LL.1 o, ← algebraMap_smul ↥LL.1 o,
          map_smul]
        rfl
      · rw [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom, Pl.PD_actB,
          RingEquiv.symm_apply_eq, hact, RingEquiv.apply_symm_apply]

theorem linEquiv_frob (T : QLat LL) (eB : Pl.R.B ≃+* Per.Bcris l)
    (hz : ∀ z : ℤ_[l], eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z)
    (hfr : ∀ b : Pl.R.B, eB (Pl.φB b) = Per.φB l (eB b))
    (w : TW (OB l ↥(OL LL)) T) :
    linEquiv T eB hz (TWmap (frobOB l ↥(OL LL)) T w) =
      φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (linEquiv T eB hz w) := by
  rw [linEquiv_apply, linEquiv_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    exact congrArg₂ (· + ·) hx hy
  | tmul y x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [zero_tmul, map_zero]
    | add y₁ y₂ h₁ h₂ =>
      rw [add_tmul, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
      exact congrArg₂ (· + ·) h₁ h₂
    | tmul o b =>
      have h1 : TWmap (frobOB l ↥(OL LL)) T ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) =
          (o ⊗ₜ[ℤ_[l]] Per.φB l b) ⊗ₜ[↥(OL LL)] x := rfl
      rw [h1, addEquiv_tmul, addEquiv_tmul]
      simp only [φVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply]
      congr 1
      rw [AlgHom.toLinearMap_apply, Pl.PD_φ, RingEquiv.symm_apply_eq, hfr, RingEquiv.apply_symm_apply]

end GlobalTheory.BKGal.CrisTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCupPairingReducedCocycles
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

namespace GlobalTheory.CupAbove

theorem cup_mem_of_span {R Γ M M' P : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
    [AddCommGroup P] [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (π : Representation R Γ M) (π' : Representation R Γ M') (μ : Representation R Γ P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (π g x) (π' g y) = μ g (b x y)) (hc : ContAction π')
    (W : Submodule R (Z2 μ)) (hW : (B2 μ).comap (Z2 μ).subtype ≤ W) (S : Set (H1 π)) (S' : Set (H1 π'))
    (h : ∀ s ∈ S, ∀ s' ∈ S', ∃ z z', s = Submodule.Quotient.mk z ∧ s' = Submodule.Quotient.mk z' ∧
      cupCocycleZ1Z1 π π' μ b hb hbe hc z z' ∈ W)
    (x : Z1 π) (y : Z1 π') (hx : Submodule.Quotient.mk x ∈ Submodule.span R S)
    (hy : Submodule.Quotient.mk y ∈ Submodule.span R S') : cupCocycleZ1Z1 π π' μ b hb hbe hc x y ∈ W := by
  have e : ∀ z z', cupProductH1H1 π π' μ b hb hbe hc (Submodule.Quotient.mk z) (Submodule.Quotient.mk z') =
      Submodule.mkQ _ (cupCocycleZ1Z1 π π' μ b hb hbe hc z z') := fun _ _ => rfl
  have h1 : Submodule.map₂ (cupProductH1H1 π π' μ b hb hbe hc) (Submodule.span R S) (Submodule.span R S') ≤
      W.map (Submodule.mkQ _) := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨s, hs, s', hs', rfl⟩
    obtain ⟨z, z', rfl, rfl, hz⟩ := h s hs s' hs'
    exact ⟨_, hz, (e z z').symm⟩
  have h2 := h1 (Submodule.apply_mem_map₂ _ hx hy)
  rw [e, ← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_eq_right.2 hW] at h2
  exact h2

def addCob {K Γ A : Type} [CommRing K] [Group Γ] [TopologicalSpace Γ] [TopologicalSpace K] [DiscreteTopology K]
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] (μ : Representation K Γ K) (χ : Γ → A) : Submodule K (Z2 μ) where
  carrier := {z | ∀ lam : K →+ A, ∃ a : Γ → A, Continuous a ∧ ∀ g h, lam (z.1 (g, h)) = χ g * a h - a (g * h) + a g}
  zero_mem' := fun lam => ⟨0, continuous_const, fun g h => by simp⟩
  add_mem' := fun {z z'} hz hz' lam => by
    obtain ⟨a, ha, h1⟩ := hz lam
    obtain ⟨a', ha', h2⟩ := hz' lam
    refine ⟨a + a', ha.add ha', fun g h => ?_⟩
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), h1, h2]
    ring
  smul_mem' := fun k z hz lam => hz (lam.comp (AddMonoidHom.mulLeft k))

theorem map_padic_mul {l : ℕ} [Fact l.Prime] {K : Type} [CommRing K] (φ : ℤ_[l] →+* K) (hl : (l : K) = 0)
    (lam : K →+ ZMod (l ^ 1)) (u : ℤ_[l]) (k : K) : lam (φ u * k) = PadicInt.toZModPow 1 u * lam k := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 u)
  have h1 : φ u = (u.appr 1 : ℕ) := by
    have := congrArg φ hc
    rw [map_mul, map_pow, map_natCast, hl, map_sub, map_natCast, pow_one, mul_zero] at this
    exact sub_eq_zero.1 this.symm
  have h2 : PadicInt.toZModPow 1 u = (u.appr 1 : ℕ) := rfl
  rw [h1, h2, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

section Galois

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}

theorem mk_eq_zero_iff (w : Z2 (muLoc F l 1 A)) : (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 ↔
    ∃ a : Dec (F := F) A → ZMod (l ^ 1), Continuous a ∧ ∀ g h : Dec (F := F) A, w.1 (g, h) =
      PadicInt.toZModPow 1 ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) * a h - a (g * h) + a g := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, separated_dvr_second_cohomology_mem]
  refine exists_congr fun a => and_congr_right fun _ => ⟨fun e g h => (congrFun e (g, h)).symm, fun e => ?_⟩
  funext ⟨g, h⟩
  exact (e g h).symm

variable {K : Type} [CommRing K] [TopologicalSpace K] [DiscreteTopology K] (φ : ℤ_[l] →+* K) (hl : (l : K) = 0)
  (μ : Representation K (Dec (F := F) A) K) (hμ : ∀ g k, μ g k = φ ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) * k)

include hl hμ

theorem exists_push (z : Z2 μ) (lam : K →+ ZMod (l ^ 1)) : ∃ w : Z2 (muLoc F l 1 A), ∀ g h, w.1 (g, h) = lam (z.1 (g, h)) := by
  refine ⟨⟨fun p => lam (z.1 p), continuous_of_discreteTopology.comp z.2.1, fun g h k => ?_⟩, fun _ _ => rfl⟩
  have e := congrArg lam (z.2.2 g h k)
  rw [map_sub, map_add (f := _), map_sub, hμ, map_padic_mul φ hl, map_zero] at e
  exact e

theorem coboundaries_le_cyclotomic_additive : (B2 μ).comap (Z2 μ).subtype ≤
    addCob μ (fun g => PadicInt.toZModPow 1 ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) := by
  rintro z ⟨c, hc, e⟩ lam
  refine ⟨fun g => lam (c g), continuous_of_discreteTopology.comp hc, fun g h => ?_⟩
  have e' : z.1 (g, h) = μ g (c h) - c (g * h) + c g := (congrFun e (g, h)).symm
  rw [e', map_add (f := _), map_sub, hμ, map_padic_mul φ hl]

end Galois

theorem mk_eq_zero_of_rational (hT : LocalTateDuality) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (β : O →+ ZMod (l ^ 1)) (z : Dec (F := F) A → Dec (F := F) A → O) (f : Dec (F := F) A → ↥Bw.LL.1) (hf : Continuous f)
    (hz : ∀ g h, Bw.toLL (z g h) =
      Bw.toLL (algebraMap ℤ_[l] O ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) * f h - f (g * h) + f g)
    (w : Z2 (muLoc F l 1 A)) (hw : ∀ g h, w.1 (g, h) = β (z g h)) :
    (Submodule.Quotient.mk w : H2 (muLoc F l 1 A)) = 0 := by
  have : IsGalois F Ω := {}
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have : IsTopologicalRing ↥Bw.LL.1 := inferInstanceAs (IsTopologicalRing ↥Bw.LL.1.toSubfield.toSubring)
  have hr : Set.range Bw.toLL = Set.range (algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1) :=
    Bw.eO.surjective.range_comp (algebraMap ↥(Loc.OL Bw.LL) ↥Bw.LL.1)
  obtain ⟨n, a, ha, e⟩ := _root_.GlobalTheory.exists_zmod_pow_coboundary_of_rational_coboundary (Dec (F := F) A) l (fun g => ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l])) O ↥Bw.LL.1 Bw.toLL
    (GlobalTheory.BlochKatoIntegralScalars.toLL_injective Bw) (hr ▸ GlobalTheory.LocalIntegers.isOpen_integers l Bw.LL)
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    (fun x => by
      obtain ⟨n, hn⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL Bw.LL (fun (_ : Unit) (_ : Fin 1) => x)
        continuous_const
      exact ⟨n, hr ▸ ⟨⟨_, hn () 0⟩, rfl⟩⟩) β z f hf hz
  refine GlobalTheory.T.mu_cocycle_coboundary_lift hT F Ω l A v hA n w a ha fun g h => ?_
  rw [hw]
  exact e g h

section Matrices

variable {Γ O K : Type} [Group Γ] [CommRing O] [CommRing K] [Algebra O K] {r : ℕ}

theorem repOn_one_apply (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    repOn ρ (1 : Γ →* Kˣ) K g m = (((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (algebraMap O K)).mulVec m := by
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

theorem dot_equivariant (T T' : Matrix (Fin r) (Fin r) O) (hT : IsUnit T.det) (u : O) (h : T' = u • T⁻¹.transpose)
    (x y : Fin r → K) :
    (T.map (algebraMap O K)).mulVec x ⬝ᵥ (T'.map (algebraMap O K)).mulVec y = algebraMap O K u * (x ⬝ᵥ y) := by
  have e : (T.map (algebraMap O K)).transpose * T'.map (algebraMap O K) = algebraMap O K u • 1 := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h, Matrix.mul_smul, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hT, Matrix.transpose_one]
    ext a b
    by_cases hab : a = b <;> simp [hab]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem dot_generators (T : Matrix (Fin r) (Fin r) O) (y y' : Fin r → O) (b b' : K) :
    (fun a => algebraMap O K (y a) • b) ⬝ᵥ (T.map (algebraMap O K)).mulVec (fun a => algebraMap O K (y' a) • b') =
      (b * b') * algebraMap O K (y ⬝ᵥ T.mulVec y') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Matrix.map_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

end Matrices

theorem cup_eq_zero_above : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → ∀ (lam : K →+ ZMod (X.l i ^ 1)) (w : Z2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))), (∀ g h : ↥(DecV N v), w.1 (g, h) = lam (x.1 g ⬝ᵥ red i K ρ g (y.1 h))) → (Submodule.Quotient.mk w : H2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))) = 0 := by
  intro hT D N X bkP i s _ K _ _ _ _ hK ρ hρ v hv x y hx hy lam w hw
  let φ : ℤ_[X.l i] →+* K := (algebraMap (X.O0 i) K).comp (algebraMap ℤ_[X.l i] (X.O0 i))
  have hl : ((X.l i : ℕ) : K) = 0 := by
    rw [← map_natCast (algebraMap (X.O0 i) K)]
    exact hK _ (GlobalTheory.PrimeToInertia.l_mem i)
  let μ : Representation K (DecV N v) K :=
    charRep (((Units.map (algebraMap (X.O0 i) K).toMonoidHom).comp (eps0 X i)).comp (DecV N v).subtype)
  have hμ : ∀ (g : DecV N v) k, μ g k = φ ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) * k := fun _ _ => rfl
  have hbe : ∀ (g : DecV N v) (m m' : Fin D.R.r → K),
      dotProductBilin K K (((red i K (Tgl i s)).comp (DecV N v).subtype) g m) (((red i K ρ).comp (DecV N v).subtype) g m') =
        μ g (dotProductBilin K K m m') := by
    intro g m m'
    change red i K (Tgl i s) g m ⬝ᵥ red i K ρ g m' = algebraMap (X.O0 i) K ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (m ⬝ᵥ m')
    rw [repOn_one_apply, repOn_one_apply]
    refine dot_equivariant _ _ (Matrix.isUnits_det_units _) _ ?_ m m'
    rw [hρ, Tgl_coe]
    rfl
  have hc : ContAction ((red i K ρ).comp (DecV N v).subtype) := by
    have : IsLocalHom (algebraMap (X.O0 i) K) := ⟨fun a ha => by
      by_contra hn
      exact ha.ne_zero (hK a hn)⟩
    have h1 : ContAction (red i K ρ) := by
      refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ ?_ 1 (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) fun b => ⟨1, fun c hc => ?_⟩
      · simp_rw [show ∀ g, _ from hρ]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
      · rw [pow_one, IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hc
        rw [hc, zero_smul]
    exact h1.comp (f := fun p : DecV N v × (Fin D.R.r → K) => ((p.1 : GE N), p.2)) (by fun_prop)
  rw [bkOn, dite_eq_left hv] at hx hy
  have key := cup_mem_of_span _ _ μ (dotProductBilin K K) continuous_of_discreteTopology hbe hc _
    (coboundaries_le_cyclotomic_additive φ hl μ hμ) _ _ (by
      rintro _ ⟨z, c, t, b, h1, h2, h3, rfl⟩ _ ⟨z', c', t', b', h1', h2', h3', rfl⟩
      refine ⟨z, z', rfl, rfl, fun lam => ?_⟩
      obtain ⟨f, hf, e⟩ := _root_.GlobalTheory.BKCup.cup_coboundary D N X bkP i s ‹_› ρ hρ v hv c c' t t' h1 h1' h2 h2'
      obtain ⟨w, hw⟩ := exists_push φ hl μ hμ
        (cupCocycleZ1Z1 _ _ μ (dotProductBilin K K) continuous_of_discreteTopology hbe hc z z') lam
      simp_rw [← hw]
      refine (mk_eq_zero_iff w).1 (mk_eq_zero_of_rational hT (N.plOm.2 v) (bkP.br i v hv)
        ((lam.comp (AddMonoidHom.mulLeft (b * b'))).comp (algebraMap (X.O0 i) K).toAddMonoidHom) _ f hf e w fun g h => ?_)
      rw [hw]
      change lam (z.1 g ⬝ᵥ red i K ρ g (z'.1 h)) = lam (b * b' * algebraMap (X.O0 i) K _)
      rw [repOn_one_apply, show z.1 g = _ from funext (h3 g), show z'.1 h = _ from funext (h3' h), dot_generators])
    x y hx hy
  obtain ⟨a, ha, e⟩ := key lam
  exact (mk_eq_zero_iff w).2 ⟨a, ha, fun g h => (hw g h).trans (e g h)⟩

end GlobalTheory.CupAbove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAssembly
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.Proof.LocalGlobalAssembly

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GlobalTheory.PtCore.GoodPtRow D := by
  intro D _ _ hZ a π hπ
  have hπ' : π ∈ ZgoodN D.nd D.naut a := (D.Zgood_tie a π).1 hπ
  obtain ⟨-, Sig, hX, hg⟩ := id hπ'
  have hHG : HG D.nd D.naut a := ⟨π, hπ'⟩
  have h1 := ((hZ a hHG).1 π hπ' Sig hX).2

  have hE : eigC D.nd D.naut a π ≠ ⊥ := by
    obtain ⟨P, hP, -⟩ := hX
    intro h
    apply D.naut.typeV_ne a P
    rw [eq_bot_iff, ← h]
    exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | D.naut.ptV a P = some π}) => D.naut.typeV a P) P hP le_rfl
  have hM : MjSig D.nd D.naut a Sig ≠ ⊥ := by
    intro h
    apply hE
    rw [← h1, h, Submodule.map_bot]
  obtain ⟨σ, hW, hσ⟩ : ∃ σ, HasParamW D.nd D.naut a σ Sig ∧ D.what₂.isot (D.nd.j a) σ ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    apply hM
    unfold MjSig
    exact le_bot_iff.1 (iSup₂_le fun σ hW => (hc σ hW).le)
  have hgr : D.nd.goodRow σ := (GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig D.nd D.naut hW.2.2).2 hg
  exact ⟨σ, Sig, ⟨hgr, hσ⟩, hW, hX⟩

end GlobalTheory.Proof.LocalGlobalAssembly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCrysBKFunctorOLOfBhattScholze
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per

namespace GlobalTheory

theorem nonempty_crysBKFunctorOL_of_bhattScholze :
    GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → Nonempty (CrysBKFunctorOL a ϖ LL P) := by
  intro BS l _ a e _ _ ϖ LL _ P AI h
  refine ⟨BKFunctor.ofExists (fun T hT => GlobalTheory.T.exists_breuilKisin_module_basis_of_fCrystal BS l a e _ _ _ ϖ T ?_) fun M M' f => GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism BS l a e _ _ _ ϖ _ _ _ _ _ _ M.I M'.I M.isBK M'.isBK f⟩
  obtain ⟨E, j, H⟩ := (BS l _ _ _ (isAinf_ainfObj (ϖ.field a))).1 P AI h LL T hT
  exact ⟨E, j, H⟩

end GlobalTheory
end

