module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.AtTRank
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Formalism.LocalToGlobal.Columns.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0004
public import Formalism.LocalToGlobal.Columns.BaseInst
public import Formalism.LocalToGlobal.Columns.AtTOwedS
public import Formalism.LocalToGlobal.Columns.AtTLemmas
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalToGlobal.Columns.Bundle0008
public import Formalism.LocalToGlobal.Columns.Bundle0005
public import Formalism.LocalToGlobal.Columns.LocWLemmas
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.GL3MeanSquares.HookFormulaTorsion.FourierCommutesHeckeScalar
public import Formalism.GL3MeanSquares.HookFormulaTorsion.LengthQuotientBoundGeneral
public import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0002
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.Columns.RowFormsGood
public import Formalism.LocalToGlobal.Columns.TiedCG
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.NonDeg
section
open NumberField IsDedekindDomain Module IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Host

section TBig

variable {X : Fields} {Pr : Primes X}

end TBig

section Gen

open GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

end Gen

section ColsRam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColsRam

section Delta

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end Delta

section ColsUD

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColsUD

section SeenEx

variable {X : Fields} {Pr : Primes X}

end SeenEx

section Pos

open ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

def GSD.pairEmb (σ : K →+* ℂ) (x y : S.V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (σ (S.bV.repr x i)) * σ (S.gramV i j) * σ (S.bV.repr y j)

theorem GSD.map_pair (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (x y : S.V) :
    σ (S.pair x y) = S.pairEmb σ x y := by
  conv_lhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, map_mul, hσ, GSD.pairEmb, GSD.gramV, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def GSD.ipEmb (h : S.Ok) (σ : K →+* ℂ) (φ ψ : S.D → S.V) : ℂ :=
  letI : Fintype S.Cl := h.fintypeCl
  ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℂ)⁻¹ * S.pairEmb σ (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))

theorem GSD.ipAt_eq_ipEmb (h : S.Ok) (v : InfinitePlace K) (φ ψ : S.D → S.V) :
    S.ipAt h v φ ψ = S.ipEmb h v.embedding φ ψ := rfl

theorem GSD.map_ip (h : S.Ok) (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (φ ψ : S.D → S.V) :
    σ (S.ip h φ ψ) = S.ipEmb h σ φ ψ := by
  let _ : Fintype S.Cl := h.fintypeCl
  unfold GSD.ip GSD.ipOf GSD.ipEmb CSD.csum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, map_inv₀, map_natCast]
  congr 1
  exact S.map_pair σ hσ _ _

end Pos

section ColPos

open ComplexOrder

variable {X : Fields}

variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColPos

section LatGen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

end LatGen

section ColLat

variable {X : Fields}

variable {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end ColLat

section Cert

end Cert

section GaussInst

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end GaussInst

def ndIota : Qb →+* ℂ :=
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := Qb)).toRingHom

section OfSizes

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end OfSizes

section InstThms

open ComplexOrder

end InstThms

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RowFormsRat
section
open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Mat

variable {K : Type} [Field K]

theorem rf_inv_entries_mem (K0 : Subfield K) {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (hA : ∀ i j, A i j ∈ K0) (i j : Fin d) :
    A⁻¹ i j ∈ K0 := by
  let A0 : Matrix (Fin d) (Fin d) K0 := fun i j => ⟨A i j, hA i j⟩
  have e : A = A0.map K0.subtype := rfl
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', e, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, ← RingHom.map_adjugate]
  exact mul_mem (inv_mem (A0.det).2) ((A0.adjugate i j).2)

end Mat

namespace CSDRat

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

theorem pair_mem (R : S.Rat) (x y : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (hy : ∀ i, S.bV.repr y i ∈ cmMax K) :
    S.pair x y ∈ cmMax K := by
  rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply]
  refine sum_mem fun j _ => mul_mem (hy j) (sum_mem fun i _ => ?_)
  exact mul_mem (Formalism.L2.DIV.star_mem_cmMax (hx i)) (R.pair_rat i j)

theorem csum_mem (R : S.Rat) (f g : S.Cl → S.V) (hf : S.IsRat f) (hg : S.IsRat g) : S.csum f g ∈ cmMax K := by
  unfold CSD.csum
  exact sum_mem fun c _ => mul_mem (inv_mem (natCast_mem _ _)) (pair_mem S R _ _ (hf c) (hg c))

theorem H_mem (R : S.Rat) (hb : S.HasRatBasis) (i j : Fin S.dim) : S.H i j ∈ cmMax K :=
  csum_mem S R _ _ (S.basis_rat hb i) (S.basis_rat hb j)

theorem csum_basis (i : Fin S.dim) (x : Fin S.dim → K) :
    S.csum (S.basis i : S.Cl → S.V) (S.I x) = (S.H *ᵥ x) i := by
  have h := S.csum_sum (Pi.single i 1) x
  have e : S.I (Pi.single i 1) = (S.basis i : S.Cl → S.V) := by
    rw [S.I_eq_sum, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [e, Finset.sum_eq_single i] at h
  · rw [h]
    simp [Matrix.mulVec, dotProduct]
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem repr_mem (R : S.Rat) (hb : S.HasRatBasis) (hdet : S.H.det ≠ 0) (f : S.Forms) (hf : S.IsRat (f : S.Cl → S.V))
    (i : Fin S.dim) : S.basis.repr f i ∈ cmMax K := by
  set x : Fin S.dim → K := S.basis.equivFun f with hx
  have hI : S.I x = (f : S.Cl → S.V) := by
    rw [S.I_apply, hx, LinearEquiv.symm_apply_apply]
  have h1 : S.H *ᵥ x = fun i => S.csum (S.basis i : S.Cl → S.V) (f : S.Cl → S.V) := by
    funext i
    rw [← csum_basis, hI]
  have h2 : x = S.H⁻¹ *ᵥ fun i => S.csum (S.basis i : S.Cl → S.V) (f : S.Cl → S.V) := by
    rw [← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  show x i ∈ cmMax K
  rw [h2]
  show ∑ j, S.H⁻¹ i j * S.csum (S.basis j : S.Cl → S.V) (f : S.Cl → S.V) ∈ cmMax K
  exact sum_mem fun j _ => mul_mem (rf_inv_entries_mem _ _ (H_mem S R hb) i j) (csum_mem S R _ _ (S.basis_rat hb j) hf)

theorem actRat_of (R : S.Rat) (hb : S.HasRatBasis) (hdet : S.H.det ≠ 0) {G : Type} [Group G] [Fintype G]
    (r : Representation K G S.Forms)
    (hr : ∀ (t : G) (f : S.Forms), S.IsRat (f : S.Cl → S.V) → S.IsRat (r t f : S.Cl → S.V)) : S.ActRat r := by
  intro t i j
  unfold CSD.actMat
  rw [LinearMap.toMatrix_apply]
  exact repr_mem S R hb hdet _ (hr t _ (S.basis_rat hb j)) i

end CSDRat

section GSDRat

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem GSD.rho_mem (R : S.Rat) (g : S.G) (x : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (i : S.ιV) :
    S.bV.repr (S.ρ g x) i ∈ cmMax K := by
  have e : S.ρ g x = S.ρ g (∑ j, S.bV.repr x j • S.bV j) := by rw [S.bV.sum_repr x]
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact sum_mem fun j _ => mul_mem (hx j) (R.act_rat g i j)

theorem GSD.det_H_ne_zero (R : S.Rat) (h : S.Ok) : (S.toCSD h).H.det ≠ 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have hp := (R.posH h v).det_pos
  intro h0
  have e : ((S.toCSD h).H.map v.embedding).det = v.embedding (S.toCSD h).H.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hp' : 0 < ((S.toCSD h).H.map v.embedding).det := hp
  rw [e, h0, map_zero] at hp'
  exact lt_irrefl _ hp'

theorem GSD.repCSD_actRat (h : S.Ok) (R : S.Rat) {A : Type} [Group A] [Fintype A] (r : Representation K A S.EqFun)
    (hr : ∀ (a : A) (φ : S.EqFun) (d : S.D), ∃ d' : S.D, (r a φ : S.D → S.V) d = (φ : S.D → S.V) d') :
    (S.toCSD h).ActRat (S.repCSD h r) := by
  refine CSDRat.actRat_of _ (S.toCSDOf_rat h R _) (csd_hasRatBasis _ (S.toCSDOf_rat h R _)) (S.det_H_ne_zero R h) _ ?_
  intro t f hf c i
  obtain ⟨d', hd'⟩ := hr t ((S.res h).symm f) (S.outSec.rep c)
  show S.bV.repr ((r t ((S.res h).symm f) : S.D → S.V) (S.outSec.rep c)) i ∈ cmMax K
  rw [hd']
  show S.bV.repr (S.ρ (S.outSec.mv d') ((f.1 : S.Cl → S.V) (S.cls d'))) i ∈ cmMax K
  exact S.rho_mem R _ _ (hf _) i

end GSDRat

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem unipotentActionForms_rational (hX : X.Ok) (h : (mtildeKGSD W Ch sel mu).Ok) :
    (MtildeKCSD W Ch sel mu h).ActRat (g0Act W Ch sel mu h) :=
  GSD.repCSD_actRat _ h (mtildeK_rat W Ch sel mu hX) _ fun _ _ _ => ⟨_, rfl⟩

theorem unipotentActionClassSum_rational (hX : X.Ok) (j : ℕ) (h : (mtKGSD W Ch sel mu j).Ok) :
    (MtKCSD W Ch sel mu j h).ActRat (unipotentRightActionOnForms W Ch sel mu j h) :=
  GSD.repCSD_actRat _ h (mtK_rat W Ch sel mu hX j) _ fun _ _ _ => ⟨_, rfl⟩

end Rows

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedCB
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def crdN (D : ColRec) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : ColRec) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)


end Formalism.L2.Col.CF

end
end

