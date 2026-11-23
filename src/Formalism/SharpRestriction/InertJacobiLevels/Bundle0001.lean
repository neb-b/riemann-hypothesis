module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalRingCardinality.DataNChoice

@[expose] public section

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Finset

theorem isRowLev_one (k rS n : ℕ) (F : Type) [Zero F] [One F] [DecidableEq (Fin n)] :
    IsRowLev k rS (1 : Matrix (Fin n) (Fin n) F) := by
  refine ⟨fun i j h => Matrix.one_apply_ne ?_, fun i => Matrix.one_apply_eq i,
    fun i j _ h => Matrix.one_apply_ne (ne_of_gt h), fun i j _ h _ => Matrix.one_apply_ne h⟩
  rintro rfl
  exact lt_irrefl _ h

theorem idxRowLoc_pos (g k m : ℕ) [NeZero g] : 0 < idxRowLoc g k m := by
  unfold idxRowLoc idxLoc
  have : Nonempty {A : GL (Fin (k + m - 1)) (ZMod g) //
      IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} :=
    ⟨⟨1, by rw [Units.val_one]; exact isRowLev_one _ _ _ _⟩⟩
  have h1 : 0 < Nat.card (GL (Fin (k + m - 1)) (ZMod g)) := Nat.card_pos
  have h2 : 0 < Nat.card {A : GL (Fin (k + m - 1)) (ZMod g) //
      IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} := Nat.card_pos
  positivity

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.BasicNotions.Examples₂ NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Ext

structure Tow (D : D7) (t : ℕ) where
  Xs : ℕ → HSp D
  Xs_rank : ∀ j, j ≤ D.R.m → (Xs j).rank = D.R.k + j * (t + 1)
  Xs_sig : ∀ j, j ≤ D.R.m → (Xs j).SigOK ∧ (Xs j).IsDefinite
  Ys : ℕ → HSp D
  Ys_rank : ∀ j, j ≤ D.R.m → (Ys j).rank = D.R.r + j * t
  Ys_sig : ∀ j, j ≤ D.R.m → (Ys j).SigOK
  iXYs : ∀ j, (Xs j).V →ₗ[D.host.E] (Ys j).V
  iXYs_isom : ∀ j, j < D.R.m → HSpace.IsIsomEmb (Xs j) (Ys j) (iXYs j)
  iYXm : (Ys D.R.m).V →ₗ[D.host.E] (Xs D.R.m).V
  iYXm_isom : HSpace.IsIsomEmb (Ys D.R.m) (Xs D.R.m) iYXm

def recTow (D : D7) : Tow D D.R.t where
  Xs := D.sp.X
  Xs_rank := fun j hj => D.sp.X_rank j hj
  Xs_sig := fun j hj => ⟨D.sp.X_sig j, D.sp.X_def j hj⟩
  Ys := D.sp.Y
  Ys_rank := fun j hj => D.sp.Y_rank j hj
  Ys_sig := fun j _ => D.sp.Y_sig j
  iXYs := D.sp.iXY
  iXYs_isom := D.sp.iXY_isom
  iYXm := D.sp.iX'.comp D.sp.eYm.symm.toLinearMap
  iYXm_isom := fun x y => by
    have h1 := D.sp.iX'_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    have h2 := D.sp.eYm_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm


end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraVal
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain IsLocalRing

section Rec

variable (D : D7)

theorem resChar_mem (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have h1 := D.what₂.places.val_resChar w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  rw [D.val_eq w _ hne, Formalism.BasicNotions.vAdd] at h1
  have h2 := WithTop.coe_injective h1
  have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hne
  obtain ⟨n, hn⟩ : ∃ n : ℤ,
      (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = WithZero.exp n :=
    ⟨_, (WithZero.exp_log hv0).symm⟩
  rw [hn, WithZero.log_exp] at h2
  have hpos := D.what₂.places.ramIdx_pos w
  have hlt : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
    rw [hn, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
  have e : (D.plEq w).valuation D.what₂.LL
      (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) =
      (D.plEq w).intValuation ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) :=
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _
  rw [← e, map_natCast]
  exact hlt

end Rec

end Formalism.MainNotions.Inhab

end
end

