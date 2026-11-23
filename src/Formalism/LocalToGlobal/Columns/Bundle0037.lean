module

public import Formalism.LocalToGlobal.Columns.Bundle0036
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete
public import Formalism.LocalToGlobal.Columns.Bundle0031
public import Formalism.LocalToGlobal.Columns.Bundle0010
public import Formalism.LocalToGlobal.Columns.LevGCount
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.Bundle0008
public import Formalism.LocalToGlobal.Columns.ReductionExistsInLatticeStabilizerHolds
public import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.LastRowColLevSym
section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section LR

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem xt_N_top {m2 : ℕ} (hm : R.m = m2 + 2) : R.N (m2 + 1 + 1) - 1 = R.r + R.m * R.t := by
  unfold Ranks.N Ranks.r
  rw [hm]
  have e : (m2 + 1 + 1) * (R.t + 1) = (m2 + 2) * R.t + (m2 + 2) := by ring
  omega

theorem lastRow_colLevSym (Ch : Chars X Pr R.m) {m2 : ℕ} (hm : R.m = m2 + 2) : LastRow (colLevSym Ch (m2 + 1 + 1)) := by
  intro w h' hh' l
  rw [colLevSym_top_H Ch (by omega) w] at hh'
  have hN := xt_N_top (R := R) hm
  have hbt := HPar_le _ _ _ hh'.1
  by_cases hl : l.1 = R.N (m2 + 1 + 1) - 1
  · rw [if_pos hl, hh'.2 _ l (by rw [hl, hN])]
    have : (⟨R.N (m2 + 1 + 1) - 1, xt_last_lt R _⟩ : Fin (R.N (m2 + 1 + 1))) = l := Fin.ext hl.symm
    rw [this, Matrix.one_apply_eq]
  · rw [if_neg hl]
    refine mem_btG.1 hbt _ l ?_
    have hl2 : l.1 < R.r + R.m * R.t := by have := l.2; omega
    show coarse R.r (List.replicate R.m R.t) l.1 < coarse R.r (List.replicate R.m R.t) (R.N (m2 + 1 + 1) - 1)
    rw [hN]
    have e1 : coarse R.r (List.replicate R.m R.t) (R.r + R.m * R.t) = R.m + 1 := by
      unfold coarse blkIdx
      rw [if_neg (by omega), Nat.add_sub_cancel_left, blkIdx_replicate_of_le _ _ _ le_rfl]
    rw [e1]
    unfold coarse blkIdx
    split_ifs with h0
    · omega
    · have := blkIdx_replicate_lt R.t R.m (l.1 - R.r) (by omega)
      omega

end LR

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.XiFirstLawAllLevels
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Pts

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem first_sum_scalar_mul {k K : Type} [CommRing k] [Field K] {n' c' n c : ℕ} (psi : k → K) (vals : Finset k) (wt : K) (a : K)
    (Φ : Loc.SF k K (n' + c') (n + c)) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (fun x => a * Φ x) xj = a * Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Φ xj := by
  unfold Loc.E1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

end Pts

section Res

variable {k : Type} [CommRing k]

end Res

section Assemble

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

end Assemble

section Deep

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

end Deep

end Formalism.L2.Col
end
end

