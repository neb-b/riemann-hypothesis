module

public import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.MeanHeightDescent.AverageDegreeBounds.TwistLower

@[expose] public section

noncomputable section

open Module Matrix NumberField Formalism.BasicNotions Formalism.HN

namespace Formalism.L2.Geo.Def.G1

section Line

variable {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]

section Single

variable {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]


end Single

theorem lcv_eq_mu {n : ℕ} (hn : 0 < n) (Y : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hY : ∀ v, IsUnit (Y v).det)
    (T : Submodule (𝓞 K) (Fin n → K)) (hfg : T.FG) (hrk : rkK T = n) :
    Formalism.DivisionValues.lcv Y T = -(n : ℝ) * muDef (Pi.basisFun K (Fin n)) Y T := by
  have hsp : Submodule.span K (T : Set (Fin n → K)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have : finrank K (Submodule.span K (T : Set (Fin n → K))) = n := hrk
    rw [this]; simp
  let B : HLat K := { V := Fin n → K, ι := Fin n, b := Pi.basisFun K (Fin n), X := Y, L := T }
  have hB : B.Good := ⟨hY, hfg, hsp⟩
  have hBr : B.rank = n := hrk
  have h := bridge_hn_mu_holds K B hB (by rw [hBr]; exact hn)
  rw [hBr] at h
  have h1 : B.mu = muDef (Pi.basisFun K (Fin n)) Y T := rfl
  have h2 : B.lcv = Formalism.DivisionValues.lcv Y T := rfl
  rw [← h1, ← h2, h]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end Line

end Formalism.L2.Geo.Def.G1
