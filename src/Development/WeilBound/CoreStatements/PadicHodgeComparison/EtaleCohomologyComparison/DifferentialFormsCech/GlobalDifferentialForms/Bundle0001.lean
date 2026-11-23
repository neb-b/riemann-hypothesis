module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FV
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison.Pb

namespace CrystallineSemistableComparison.Om.Glob

abbrev FV {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (a : ℕ) :
    (KS q (a + 1) {V}).FullSubcategory ⥤ ModuleCat.{0} K :=
  (KS q (a + 1) {V}).ι ⋙ HT.grT (smFun X q) a

end CrystallineSemistableComparison.Om.Glob
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.RowSurjZ
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.CechSerre

universe w

namespace CrystallineSemistableComparison.Om.Glob

theorem glob_iso (h : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] (formCos q U.U a).cx.H j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
      (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a j : ℕ) (c : (formCos p W.U a).X j)
      (h0 : (formCos p W.U a).cx.d j c = 0)
      (h1 : (formCos q U.U a).cx.d j (fun i => formRes q (hτ j i) a (formPull hu (capO W.U (τ ∘ i)) a (c (τ ∘ i)))) = 0),
      HT.pullH u hu a (a + j) ((e p W a j).symm ((formCos p W.U a).cx.cls c h0)) =
        (e q U a j).symm ((formCos q U.U a).cx.cls _ h1)) : type_of% @h := @h

end CrystallineSemistableComparison.Om.Glob
end
end

