module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0420
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationEquivariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0403
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0476
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMMapOfZero

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHolds
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}

theorem mcast_spec {a b : ℕ} (h : a = b) (Y : MRep k a) :
    ∃ e : Y.V ≃ₗ[ℂ] (mcast h Y).V, ∀ x v, e (Y.ρ x v) = (mcast h Y).ρ (castM k h x) (e v) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem dpowM_castM {a b : ℕ} (h : a = b) (s : ℝ) (x : Mir k a) : dpowM b s (castM k h x) = dpowM a s x := by
  subst h
  rfl

theorem mExt_mcast {a b : ℕ} (h : a = b) {A B C : MRep k a} (H : MExt A B C) :
    MExt (mcast h A) (mcast h B) (mcast h C) := by
  subst h
  exact H

theorem phiN_mcast (ψ : AddChar k Circle) {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1) (X : MRep k (a + 1)) :
    phiN ψ (mcast h' X) = mcast h (phiN ψ X) := by
  subst h
  rfl

theorem mcast_mcast {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) (X : MRep k a) :
    mcast h₂ (mcast h₁ X) = mcast h₃ X := by
  subst h₁
  subst h₂
  rfl

theorem evX_cInd {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (g p : Mir k ((i + 1) + t + 1)) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) p = evX f (p * g) := rfl

theorem intC_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g y : Mir k ((i + 1) + t + 1)) :
    intC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y = intC ψ f (y * g) := by
  simp only [intC, evX_cInd, mul_assoc]

theorem intO_translate {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g y : Mir k ((i + 1) + t + 1)) :
    intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y = intO f (y * g) := by
  simp only [intO, evX_cInd, mul_assoc]

abbrev XR (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t + 1) := prodPGn (i := i + 1) (t := t + 1) τ σ

theorem eC_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (x m : Mir k ((i + 1) + t)) :
    eC ψ f (x * m) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) x := by
  simp only [eC, map_mul, Units.val_mul, intC_translate, smul_smul, mul_comm]

theorem eO_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (x m : Mir k (i + (t + 1))) :
    eO ψ f (x * m) = ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) •
      eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) (castM k (by omega : i + (t + 1) = (i + 1) + t) m)) f) x := by
  simp only [eO, map_mul, Units.val_mul, intO_translate, smul_smul, mul_comm, mul_assoc]

def XR' (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t + 1) :=
  ⟨XS τ σ, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)⟩

def RC (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t) :=
  ⟨cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ), cInd (MirabolicParabolic k (i + 1) t) (sigC τ σ)⟩

def RO (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k (i + (t + 1)) :=
  ⟨cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), cInd (HPG k i (t + 1)) (sigO τ σ ψ)⟩

set_option maxHeartbeats 1000000 in
theorem xr_eq (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : XR τ σ = XR' τ σ := rfl

set_option maxHeartbeats 1000000 in
theorem rc_eq (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : prodGPn (psiN τ) (gres σ) = RC τ σ := rfl

set_option maxHeartbeats 1000000 in
theorem ro_eq (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) :
    prodPGn (phiN ψ τ) σ = RO ψ τ σ := rfl

theorem rho_eq (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    (phiN ψ (n := (i + 1) + t) (XR' τ σ)).ρ m (Submodule.Quotient.mk f) =
      ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) :
          TwJacquet (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t))) := rfl

def jC (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) :
    (RC τ σ).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (psiN τ).V ⊗[ℂ] σ.V) :=
  (indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)).subtype ∘ₗ (smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).subtype ∘ₗ
    (cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)).subtype

def mirabolicRestriction (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hh : i + (t + 1) = (i + 1) + t) :
    (RO ψ τ σ).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) :=
  (LinearMap.funLeft ℂ _ (fun m => (castM k hh).symm m)) ∘ₗ
    (indSpace (HPG k i (t + 1)) (sigO τ σ ψ)).subtype ∘ₗ (smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).subtype ∘ₗ
      (cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).subtype

theorem jC_inj (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : Function.Injective (jC τ σ) :=
  fun _ _ hab => Subtype.ext (Subtype.ext (Subtype.ext hab))

theorem jO0_inj (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hh : i + (t + 1) = (i + 1) + t) :
    Function.Injective (mirabolicRestriction ψ τ σ hh) := fun a b hab => by
  refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
  funext m
  have h2 : (a : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (castM k hh m)) =
      (b : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (castM k hh m)) := congrFun hab (castM k hh m)
  rw [MulEquiv.symm_apply_apply] at h2
  exact h2

def eCl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) : XS τ σ →ₗ[ℂ] (Mir k ((i + 1) + t) → (psiN τ).V ⊗[ℂ] σ.V) where
  toFun f := eC ψ f
  map_add' f g := (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear k i t ψ hψ τ σ hτ hσ f g 0).1
  map_smul' c f := (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear k i t ψ hψ τ σ hτ hσ f f c).2.1

def eOl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) :
    XS τ σ →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) where
  toFun f m := eO ψ f ((castM k hh).symm m)
  map_add' f g := by
    funext m
    exact congrFun (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear k i t ψ hψ τ σ hτ hσ f g 0).2.2.1 _
  map_smul' c f := by
    funext m
    exact congrFun (_root_.GlobalTheory.CompanionTheory.BZPhiPG.Lin.eC_eO_linear k i t ψ hψ τ σ hτ hσ f f c).2.2.2 _

theorem eOl_apply (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) (f : XS τ σ) (m : Mir k ((i + 1) + t)) :
    eOl ψ hψ τ σ hτ hσ hh f m = eO ψ f ((castM k hh).symm m) := rfl

theorem aO_eOl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    rightReg ℂ _ _ m (eOl ψ hψ τ σ hτ hσ hh f) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eOl ψ hψ τ σ hτ hσ hh (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) := by
  funext x
  show eO ψ f ((castM k hh).symm (x * m)) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) ((castM k hh).symm x)
  have e1 := map_mul (castM k hh).symm x m
  have e2 := eO_translate ψ f ((castM k hh).symm x) ((castM k hh).symm m)
  have e3 : castM k hh ((castM k hh).symm m) = m := MulEquiv.apply_symm_apply _ _
  have e4 : dpowM (i + (t + 1)) (-1 / 2) ((castM k hh).symm m) = dpowM ((i + 1) + t) (-1 / 2) m := by
    have := dpowM_castM (k := k) hh (-1 / 2) ((castM k hh).symm m)
    rw [e3] at this
    exact this.symm
  have e6 := congrArg (fun g => eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) g) f)
    ((castM k hh).symm x)) e3
  have e7 : ((dpowM (i + (t + 1)) (-1 / 2) ((castM k hh).symm m) : ℂˣ) : ℂ) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) :=
    congrArg _ e4
  exact (congrArg (eO ψ f) e1).trans (e2.trans (congrArg₂ (· • ·) e7 e6))

theorem aC_eCl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    rightReg ℂ _ _ m (eCl ψ hψ τ σ hτ hσ f) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eCl ψ hψ τ σ hτ hσ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) := by
  funext x
  exact eC_translate ψ f x m

set_option maxHeartbeats 1000000 in
theorem phiPG_core (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) :
    MExt (mcast (by omega : i + (t + 1) = (i + 1) + t) (RO ψ τ σ)) (phiN ψ (n := (i + 1) + t) (XR' τ σ)) (RC τ σ) := by
  have hh : i + (t + 1) = (i + 1) + t := by omega
  obtain ⟨hUn, hθ, hCc, hHC, hCU, hdir⟩ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.Grp.main k ψ hψ i t
  obtain ⟨e, he⟩ := mcast_spec hh (RO ψ τ σ)
  let jOl : (mcast hh (RO ψ τ σ)).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) :=
    mirabolicRestriction ψ τ σ hh ∘ₗ e.symm.toLinearMap
  have hjOl : Function.Injective jOl := (jO0_inj ψ τ σ hh).comp e.symm.injective
  have hes : ∀ (m : Mir k ((i + 1) + t)) v, e.symm ((mcast hh (RO ψ τ σ)).ρ m v) =
      (RO ψ τ σ).ρ ((castM k hh).symm m) (e.symm v) := by
    intro m v
    rw [LinearEquiv.symm_apply_eq, he, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hjOe : ∀ m v, jOl ((mcast hh (RO ψ τ σ)).ρ m v) = rightReg ℂ _ _ m (jOl v) := by
    intro m v
    show mirabolicRestriction ψ τ σ hh (e.symm _) = _
    rw [hes]
    funext x
    show (e.symm v : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm x * (castM k hh).symm m) =
      (e.symm v : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (x * m))
    rw [map_mul]
  exact GlobalTheory.T.twisted_jacquet_closed_open_sequence (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) hUn (mirChar k ψ ((i + 1) + t)) hθ hdir
    (sEmb k ((i + 1) + t)) (dpowM ((i + 1) + t) (-1 / 2)) (phiN ψ (n := (i + 1) + t) (XR' τ σ)).ρ (fun m f => rho_eq ψ τ σ m f)
    (Cl k i t) hCc hHC hCU
    (RC τ σ).ρ (mcast hh (RO ψ τ σ)).ρ
    (rightReg ℂ _ _) (rightReg ℂ _ _) (jC τ σ) jOl (jC_inj τ σ) hjOl (fun m v => rfl) hjOe
    (eCl ψ hψ τ σ hτ hσ) (eOl ψ hψ τ σ hτ hσ hh)
    (fun u f => _root_.GlobalTheory.CompanionTheory.BZPhiPG.TwC.eC_tw k i t ψ hψ τ σ hτ hσ u f)
    (fun u f => by
      funext m
      exact congrFun (GlobalTheory.T.open_evaluation_equivariant k i t ψ hψ τ σ hτ hσ u f) _)
    (fun m f => aC_eCl ψ hψ τ σ hτ hσ m f)
    (fun m f => aO_eOl ψ hψ τ σ hτ hσ hh m f)
    (fun f => by
      obtain ⟨y, hy⟩ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.MemC.memC k i t ψ hψ τ σ hτ hσ f
      exact ⟨y, hy⟩)
    (fun f hf => by
      obtain ⟨y, hy⟩ := _root_.GlobalTheory.CompanionTheory.BZPhiPG.MemO.eO_mem k i t ψ hψ τ σ hτ hσ f hf
      refine ⟨e y, ?_⟩
      funext m
      have e1 : e.symm (e y) = y := e.symm_apply_apply y
      exact (congrArg (fun z => mirabolicRestriction ψ τ σ hh z m) e1).trans (congrFun hy _))
    (fun v => _root_.GlobalTheory.CompanionTheory.BZPhiPG.Onto.eC_onto k i t ψ hψ τ σ hτ hσ v)
    (fun v => by
      obtain ⟨f, hf, hy⟩ := GlobalTheory.T.open_evaluation_surjective k i t ψ hψ τ σ hτ hσ (e.symm v)
      refine ⟨f, hf, ?_⟩
      funext m
      exact congrFun hy _)
    (fun f hf => _root_.GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish k i t ψ τ σ hτ hσ f hf)
    (fun f h0 p hp => _root_.GlobalTheory.CompanionTheory.BZPhiPG.LocC.avgVanish_of_mem_Cl k i t ψ hψ τ σ hτ hσ f h0 p hp)
    (fun f h0 p hp => GlobalTheory.T.average_vanishes_open_cell k i t ψ hψ τ σ hτ hσ f (by
      funext m
      have := congrFun h0 (castM k hh m)
      rw [eOl_apply, MulEquiv.symm_apply_apply] at this
      exact this) p hp)

theorem phiPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG k := by
  intro k _ _ _ _ ψ hψ _ i t τ σ hτ hσ
  have h0 : (i + 1) + t = i + t + 1 := by omega
  have H := mExt_mcast h0 (phiPG_core ψ hψ i t τ σ hτ hσ)
  rw [mcast_mcast _ _ (by omega : i + (t + 1) = i + t + 1), ← ro_eq, ← xr_eq, ← rc_eq] at H
  rw [phiN_mcast ψ h0 (by omega)]
  exact H

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMulComplSelf
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Cell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CellDecomp

section Weyl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem matHom_proj_weyl (σ : E →ₐ[F] E) (J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (g : GAd σ J)
    (hg : (matHom _ σ J g).1 = blk4 0 1 (-1) 0) :
    (matHom _ σ J (proj σ J v g)).1 = blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0 := by
  rw [matHom_proj, bc_val, hg]
  exact weyl_map _

theorem stab_of_weyl (σ : E →ₐ[F] E) (J : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : GLoc σ J v)
    (hk : (matHom _ σ J k).1 = blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0) :
    k ∈ stabLoc σ J (stdLattice E (n + n)) v := by
  rw [stabLoc, Subgroup.mem_comap]
  change ∀ x, x ∈ latLoc F (stdLattice E (n + n)) v ↔ (↑(matHom _ σ J k) : Matrix _ _ _).mulVec x ∈ latLoc F (stdLattice E (n + n)) v
  rw [hk]
  have hmap : ∀ y ∈ latLoc F (stdLattice E (n + n)) v,
      (blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec y ∈ latLoc F (stdLattice E (n + n)) v := by
    intro y hy
    change y ∈ AddSubgroup.closure _ at hy
    change _ ∈ AddSubgroup.closure _
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨a, ha, (blk4 (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0).mulVec x, ?_, ?_⟩
      · change _ ∈ Submodule.pi _ _ at hx ⊢
        rw [Submodule.mem_pi] at hx ⊢
        intro j _
        obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
        rcases s with i | i
        · rw [(weyl_mulVec x i).1]
          exact hx _ (Set.mem_univ _)
        · rw [(weyl_mulVec x i).2]
          exact neg_mem (hx _ (Set.mem_univ _))
      · funext j
        obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
        rcases s with i | i
        · rw [(weyl_mulVec _ i).1, (weyl_mulVec x i).1]
        · rw [(weyl_mulVec _ i).2, (weyl_mulVec x i).2, TensorProduct.tmul_neg]
    | zero =>
      rw [Matrix.mulVec_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [Matrix.mulVec_add]
      exact add_mem hy hz
    | neg y _ hy =>
      rw [Matrix.mulVec_neg]
      exact neg_mem hy
  have hWW : ∀ y : Fin (n + n) → Fv F v ⊗[F] E,
      (blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec
        ((blk4 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) 1 (-1) 0).mulVec y) = -y := by
    intro y
    funext j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with i | i
    · rw [(weyl_mulVec _ i).1, (weyl_mulVec y i).2, Pi.neg_apply]
    · rw [(weyl_mulVec _ i).2, (weyl_mulVec y i).1, Pi.neg_apply]
  intro x
  constructor
  · exact hmap x
  · intro hx
    have h2 := neg_mem (hmap _ hx)
    rwa [hWW, neg_neg] at h2

end Weyl

section Main

variable {D : D7} {n : ℕ}

theorem pt_comm {e : AE D} (he : e * e = e) (hc : cA D e = e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) (x y : G D n) :
    pt e he hc x * pt (1 - e) he' hc' y = pt (1 - e) he' hc' y * pt e he hc x := by
  apply mat_inj
  rw [mat_mul', mat_mul', mat_pt, mat_pt, (ptM_mul_compl he he' _ _).1, (ptM_mul_compl he he' _ _).2]

theorem pt_mul_compl_self {e : AE D} (he : e * e = e) (hc : cA D e = e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) (x : G D n) : pt e he hc x * pt (1 - e) he' hc' x = x := by
  apply mat_inj
  rw [mat_mul', mat_pt, mat_pt, (ptM_mul_compl he he' _ _).1, ← add_smul, add_sub_cancel, one_smul]

theorem pt_nb {e : AE D} (he : e * e = e) (hc : cA D e = e) {nb : hermA D n → G D n} (hnb : IsNMap nb)
    (x : hermS D n e) : pt e he hc (nb x.1) = nb x.1 := by
  apply mat_inj
  rw [mat_pt, hnb, ptM_unip he x.2]

theorem proj_weyl {w : G D n} (hw : IsW w) (v : Pl D) :
    proj D.sp.cm.sig (Jst D n) v w ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v := by
  exact stab_of_weyl _ _ v _ (matHom_proj_weyl _ _ v w hw)

theorem proj_pt_zero {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {v : Pl D} (h : cv D v f = 0) :
    proj D.sp.cm.sig (Jst D n) v (pt f hf hc x) = 1 := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_proj, map_one, bc_val]
  exact ptM_map_of_zero (cv D v) hf h (mat x)

theorem proj_pt_one {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {v : Pl D} (h : cv D v f = 1) :
    proj D.sp.cm.sig (Jst D n) v (pt f hf hc x) = proj D.sp.cm.sig (Jst D n) v x := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_proj, matHom_proj, bc_val, bc_val]
  exact ptM_map_of_one (cv D v) hf h (mat x)

theorem projArch_pt_zero {f : AE D} (hf : f * f = f) (hc : cA D f = f) (x : G D n) {w : NumberField.InfinitePlace D.host.F}
    (h : compInf D.host.F D.host.E w f = 0) : projArch D.sp.cm.sig (Jst D n) w (pt f hf hc x) = 1 := by
  refine matHom_injective _ _ _ (Units.ext ?_)
  rw [matHom_projArch, map_one, bc_val]
  exact ptM_map_of_zero (compInf D.host.F D.host.E w) hf h (mat x)

theorem cv_of_mem {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∈ S) : cv D v e = 1 := by
  rw [hS.2 v, if_pos hv]

theorem cv_of_not_mem {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) {v : Pl D} (hv : v ∉ S) : cv D v e = 0 := by
  rw [hS.2 v, if_neg hv]

theorem pt_mem_KOff {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) (he' : (1 - e) * (1 - e) = 1 - e)
    (hc' : cA D (1 - e) = 1 - e) {x : G D n}
    (hx : ∀ v, proj D.sp.cm.sig (Jst D n) v x ∈ stabLoc D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) v) :
    pt (1 - e) he' hc' x ∈ KOff D n S := by
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · exact projArch_pt_zero he' hc' x (map_compl_zero _ (hS.1 w))
  · exact proj_pt_zero he' hc' x (map_compl_zero _ (cv_of_mem hS hv))
  · rw [proj_pt_one he' hc' x (map_compl_one _ (cv_of_not_mem hS hv))]
    exact hx v

theorem mat_inv_wn {w : G D n} (hw : IsW w) {nb : hermA D n → G D n} (hnb : IsNMap nb) (y : hermA D n) :
    mat (w * nb y)⁻¹ = blk4 (-y.1) (-1) 1 0 := by
  have hw' : mat w = blk4 0 1 (-1) 0 := hw
  have h1 : mat (w * nb y) * blk4 (-y.1) (-1) 1 0 = 1 := by
    rw [mat_mul', hw', hnb, weyl_inv]
  have h2 : mat (w * nb y)⁻¹ * mat (w * nb y) = 1 := by
    rw [← mat_mul', inv_mul_cancel, mat_one']
  calc mat (w * nb y)⁻¹ = mat (w * nb y)⁻¹ * (mat (w * nb y) * blk4 (-y.1) (-1) 1 0) := by
        rw [h1, mul_one]
    _ = blk4 (-y.1) (-1) 1 0 := by rw [← mul_assoc, h2, one_mul]

theorem cB_quot {e : AE D} (he : e * e = e) (hc : cA D e = e) {w : G D n} (hw : IsW w) {nb : hermA D n → G D n}
    (hnb : IsNMap nb) (g : G D n) (y : hermA D n) (hy : mm (e • cB g) y.1 = e • dB g) :
    cB (pt e he hc (g * (w * nb y)⁻¹)) = 0 := by
  rw [cB_pt, cB_mul, blkA_of (mat_inv_wn hw hnb y), cB_of (mat_inv_wn hw hnb y)]
  exact cell_alg hy

theorem cB_off {f : AE D} (hf : f * f = f) (hc : cA D f = f) {q : G D n} (hq : q ∈ P D n) :
    cB (pt f hf hc q) = 0 := by
  rw [cB_pt, cB_of_mem_P hq, smul_zero]

theorem decomp (hI : IdemEx) : Decomp := by
  intro D p nb hnb w hw S e hS g _ y hy
  obtain ⟨he, hc⟩ := (hI D S).2 e hS
  have he' := idem_compl he
  have hc' : cA D (1 - e) = 1 - e := by rw [map_sub, map_one, hc]
  obtain ⟨q₀, hq₀, k₀, hk₀, hgk⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D p g
  have hA : pt e he hc (nb y.1) = nb y.1 := pt_nb he hc hnb y
  have key := assemble (pt e he hc) (pt (1 - e) he' hc') (pt_comm he hc he' hc')
    (pt_mul_compl_self he hc he' hc') (w := w) hA hgk
  refine ⟨pt e he hc (g * (w * nb y.1)⁻¹) * pt (1 - e) he' hc' q₀, ?_, pt (1 - e) he' hc' (w⁻¹ * k₀), ?_, key, ?_⟩
  · exact mul_mem (mem_siegelParabolic_of_lowerLeft_eq_zero (cB_quot he hc hw hnb g y.1 hy)) (mem_siegelParabolic_of_lowerLeft_eq_zero (cB_off he' hc' hq₀))
  · apply pt_mem_KOff hS he' hc'
    intro v
    have hk : proj D.sp.cm.sig (Jst D p) v k₀ ∈
        stabLoc D.sp.cm.sig (Jst D p) (stdLattice D.host.E (p + p)) v :=
      Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk₀).1 v
    rw [map_mul, map_inv]
    exact mul_mem (inv_mem (proj_weyl hw v)) hk
  · intro x
    rw [← pt_nb he hc hnb x]
    exact pt_comm he hc he' hc' _ _

end Main

end GlobalTheory.CompanionTheory.CellDecomp

end
end

