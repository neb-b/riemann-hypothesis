module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π :=
  GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal_of GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial
    (fun k _ _ _ _ ψ m n V _ _ π => GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM (k := k) ψ m n V π) _root_.GlobalTheory.CompanionTheory.BZMir.twKer_derUnip_eq_top_of_isCuspidal
    (fun k _ _ _ _ ψ N V _ _ π => GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ N V π)
