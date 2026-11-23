module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0639
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactMaximalPairPlace
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.FA
open scoped Classical

attribute [local instance] borelG borelF borelH

namespace GlobalTheory.CompanionTheory.FmPowP

section Generic

variable {H : Type} [Group H]

theorem hint_ind_left (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) (m : H) :
    hint K (fun z => (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) z * f (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((1 : H) : H ⧸ U)]
    · have hmem : (((1 : H) : H ⧸ U).out : H) ∈ U := by
        have := QuotientGroup.out_eq' ((1 : H) : H ⧸ U)
        simpa using (QuotientGroup.eq.1 this)
      rw [Set.indicator_of_mem (by exact hmem), hl _ (inv_mem hmem)]
      field_simp
    · intro q hq
      have hnot : (q.out : H) ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using inv_mem h))
      rw [Set.indicator_of_notMem (by exact hnot), zero_mul]
  · have h1 : (x * k ∈ (U : Set H)) ↔ x ∈ (U : Set H) := Subgroup.mul_mem_cancel_right U hk
    have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    rw [h2, hl _ (inv_mem hk)]
    by_cases hx : x ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem hint_ind_right (K U : Subgroup H) (hUK : U ≤ K) (hi : U.relIndex K ≠ 0) (f : H → ℂ)
    (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) (m : H) :
    hint K (fun z => f z * (U : Set H).indicator (fun _ => ((U.relIndex K : ℕ) : ℂ)) (z⁻¹ * m)) = f m := by
  have hC : ((U.relIndex K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hi
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K U _ hUK (fun k hk x => ?_) hi]
  · rw [finsum_eq_single _ ((m : H) : H ⧸ U)]
    · obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U m
      have hmem : ((((m : H) : H ⧸ U).out : H))⁻¹ * m ∈ U := by
        rw [hu]; simp
      rw [Set.indicator_of_mem (by exact hmem), hu, hr _ u.2]
      field_simp
    · intro q hq
      have hnot : ((q.out : H))⁻¹ * m ∉ U := fun h => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 h)
      rw [Set.indicator_of_notMem (by exact hnot), mul_zero]
  · have h2 : (x * k)⁻¹ * m = k⁻¹ * (x⁻¹ * m) := by group
    have h1 : (k⁻¹ * (x⁻¹ * m) ∈ (U : Set H)) ↔ x⁻¹ * m ∈ (U : Set H) :=
      Subgroup.mul_mem_cancel_left U (inv_mem hk)
    rw [hr _ hk, h2]
    by_cases hx : x⁻¹ * m ∈ (U : Set H)
    · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

theorem relIndex_ne_of_open [TopologicalSpace H] [IsTopologicalGroup H] {K U : Subgroup H}
    (hU : IsOpen (U : Set H)) (hK : IsCompact (K : Set H)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := hU.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem isCompact_maximal_pair_place (w : Pl E) : IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  have h1 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have h2 := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
  simpa [Subgroup.coe_prod] using h1.prod h2

theorem mconv_idem_left {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hl : ∀ u ∈ U, ∀ g, f (u * g) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv (idem U) f = f := by
  funext m
  exact hint_ind_left _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hl m

theorem mconv_idem_right {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) (f : LF a b w) (hr : ∀ u ∈ U, ∀ g, f (g * u) = f g) :
    PositivityTheory.Rg.BcN.F2.mconv f (idem U) = f := by
  funext m
  exact hint_ind_right _ U hUK (relIndex_ne_of_open hU (isCompact_maximal_pair_place w)) f hr m

theorem mconv_zero_left {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv (0 : LF a b w) f = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem mconv_zero_right {w : Pl E} (f : LF a b w) : PositivityTheory.Rg.BcN.F2.mconv f (0 : LF a b w) = 0 := by
  funext m
  simpa [PositivityTheory.Rg.BcN.F2.mconv] using GlobalTheory.CompanionTheory.FamClP.hint_zero (K2 a b w)

theorem idem_left {w : Pl E} (U : Subgroup (GLw a w × GLw b w)) (u) (hu : u ∈ U) (g) : idem U (u * g) = idem U g := by
  have h1 : (u * g ∈ (U : Set (GLw a w × GLw b w))) ↔ g ∈ (U : Set (GLw a w × GLw b w)) :=
    Subgroup.mul_mem_cancel_left U hu
  unfold idem
  by_cases hx : g ∈ (U : Set (GLw a w × GLw b w))
  · rw [Set.indicator_of_mem (h1.2 hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (fun h => hx (h1.1 h)), Set.indicator_of_notMem hx]

section Sel

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

end Sel

section Alg

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)]

theorem mconv_idem_idem {w : Pl E} {U : Subgroup (GLw a w × GLw b w)} (hU : IsOpen (U : Set (GLw a w × GLw b w)))
    (hUK : U ≤ K2 a b w) : PositivityTheory.Rg.BcN.F2.mconv (idem U) (idem U) = idem U :=
  mconv_idem_left hU hUK _ (idem_left U)

end Alg

section Lev

end Lev

section Act

end Act

section Main

variable {κ : Pl E → Type} [∀ w, Fintype (κ w)] {S : Set (Pl E)} {P : Finset (Pl E)} {B : Block E}
  {e : B.κ ≃ ∀ w : P, κ w} {U₁ U₂ : ∀ w : Pl E, Subgroup (GLw B.a w × GLw B.b w)} {L : LM κ B.a B.b}

variable (hAlg : FmAlg) (hAt : FmAtP) (hCM : Tail.ConvMul) (hAct : ActAlg) (hId : ActIdem) (hS : IsSection S)
  (hP : (↑P : Set (Pl E)) ⊆ S) (hU₁ : IsLev U₁) (hU₂ : IsLev U₂) (hok : L.Ok P) (hs : ∀ w, L.s w = idem (U₁ w))
  (ht : ∀ w, L.t w = idem (U₂ w))
  (hinv : ∀ w ∈ P, ∀ x y, ∀ u ∈ U₁ w, ∀ g, L.m w x y (u * g) = L.m w x y g ∧ L.m w x y (g * u) = L.m w x y g)









end Main

end GlobalTheory.CompanionTheory.FmPowP

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNMapAdd
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem isNMap_add : ∀ {D : D7} {p : ℕ} {nb : hermA D p → G D p} (hnb : IsNMap nb) (x y : hermA D p), nb (x + y) = nb x * nb y := by
  intro D p nb hnb x y
  apply mat_inj
  rw [mat_mul, hnb, hnb, hnb, submatrix_fromBlocks_mul]
  simp [add_comm]

end GlobalTheory.CompanionTheory.MuC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_cuspidal_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c N : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp), jm y hy (prodIrr x hx) = (Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} : ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.CuspJm.main | exact GlobalTheory.CompanionTheory.CuspJm.main | (intros; apply GlobalTheory.CompanionTheory.CuspJm.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocMIterateDiag
section
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.F.Tail
open PositivityTheory.Rg.BcB.F (LF)

namespace GlobalTheory.CompanionTheory.TailLocPow

theorem hint_fun_zero {H : Type} [Group H] (K : Subgroup H) : hint K (fun _ : H => (0 : ℂ)) = 0 := by
  simp [hint]

theorem rStab_smul {H : Type} [Group H] (c : ℂ) (hc : c ≠ 0) (u : H → ℂ) :
    rStab (fun x => c * u x) = rStab u := by
  ext k
  show (∀ x, c * u (x * k) = c * u x) ↔ (∀ x, u (x * k) = u x)
  exact forall_congr' fun x => mul_right_inj' hc

theorem hint_smul {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (u : H → ℂ) :
    hint K (fun x => c * u x) = c * hint K u := by
  by_cases hc : c = 0
  · subst hc
    simpa using hint_fun_zero K
  · have key : ∀ S : Subgroup H, S = rStab u →
        (((S ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (S ⊓ K), c * u q.out =
          c * ((((rStab u ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out) := by
      rintro S rfl
      have h : (∑ᶠ q : H ⧸ (rStab u ⊓ K), c * u q.out) = c * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out := by
        simpa only [smul_eq_mul] using (smul_finsum c (fun q : H ⧸ (rStab u ⊓ K) => u q.out)).symm
      rw [h]
      ring
    exact key _ (rStab_smul c hc u)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {k : Type} [Fintype k]

end GlobalTheory.CompanionTheory.TailLocPow

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerDiagonalOfUpperTriangularBlock
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC.LeftCell

variable {D : D7} {p : ℕ}

theorem upper_triangular_block_mul_lower_rows (a b d : Mx D p p) (N : Mx D (p + p) (p + p)) (k : Fin p → Fin (p + p)) :
    (blk4 a b 0 d * N).submatrix (fun i : Fin p => finSumFinEquiv (Sum.inr i)) k =
      d * N.submatrix (fun i : Fin p => finSumFinEquiv (Sum.inr i)) k := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [blk4, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem lowerDiagonal_of_upper_triangular_block {a b d : Mx D p p} {q : G D p} (h : mat q = blk4 a b 0 d) : lowD q = d := by
  ext i j
  simp only [lowD, h, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem low_mul {q : G D p} (hq : q ∈ P D p) (g : G D p) :
    lowC (q * g) = lowD q * lowC g ∧ lowD (q * g) = lowD q * lowD g := by
  obtain ⟨b, d, hm⟩ := GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq
  have hd := lowerDiagonal_of_upper_triangular_block hm
  rw [hd]
  constructor
  · change (mat (q * g)).submatrix _ _ = _
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]
    exact upper_triangular_block_mul_lower_rows _ _ _ _ _
  · change (mat (q * g)).submatrix _ _ = _
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]
    exact upper_triangular_block_mul_lower_rows _ _ _ _ _

theorem lowD_one : lowD (1 : G D p) = 1 := by
  ext i j
  simp [lowD, GlobalTheory.StdUnn.LeftInvSect.mat_one, Matrix.one_apply]

theorem lowD_inv_mul {q : G D p} (hq : q ∈ P D p) : lowD q⁻¹ * lowD q = 1 := by
  have h := (low_mul ((P D p).inv_mem hq) q).2
  rw [inv_mul_cancel, lowD_one] at h
  exact h.symm

theorem isB_mul {e : AE D} {q g : G D p} (hq : q ∈ P D p) {x : hermS D p e} (h : IsB e g x) :
    IsB e (q * g) x := by
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  obtain ⟨hC, hD⟩ := low_mul hq g
  refine ⟨⟨mm y (lowD q⁻¹), ?_⟩, ?_⟩
  · change (y * lowD q⁻¹) * lowC (q * g) = _
    change y * lowC g = _ at hy
    rw [hC, Matrix.mul_assoc, ← Matrix.mul_assoc (lowD q⁻¹), lowD_inv_mul hq, Matrix.one_mul, hy]
  · change lowC (q * g) * x.1.1 = _
    change lowC g * x.1.1 = _ at hx
    rw [hC, hD, Matrix.mul_assoc, hx, Matrix.mul_smul]

theorem isB_left : ∀ {D : D7} {p : ℕ} {e : AE D} {q g : G D p} (hq : q ∈ P D p) (x : hermS D p e),
    IsB e (q * g) x ↔ IsB e g x := by
  intro D p e q g hq x
  refine ⟨fun h => ?_, isB_mul hq⟩
  have h' := isB_mul ((P D p).inv_mem hq) h
  rwa [inv_mul_cancel_left] at h'

end GlobalTheory.CompanionTheory.MuC.LeftCell
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulNBlockInr
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mul_nBlock_inl {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inl j)) = A i (finSumFinEquiv (Sum.inl j)) := by
  simp [Matrix.mul_apply, blk4, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_nBlock_inr {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inr j)) =
      ∑ k, A i (finSumFinEquiv (Sum.inl k)) * y k j + A i (finSumFinEquiv (Sum.inr j)) := by
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂]
  simp [Matrix.one_apply]

theorem lowC_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowC (g * nb y) = lowC g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, Matrix.submatrix_apply, hm]
  exact mul_nBlock_inl _ _ _ _

theorem lowD_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowD (g * nb y) = lowC g * y.1 + lowD g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, lowD, Matrix.submatrix_apply, hm, Matrix.add_apply, Matrix.mul_apply]
  exact mul_nBlock_inr _ _ _ _

theorem isB_mul_nb {D : D7} {p : ℕ} {e : AE D} {nb : hermA D p → G D p} (hnb : IsNMap nb) {g : G D p}
    (y x : hermS D p e) : IsB e (g * nb y.1) (x + y) ↔ IsB e g x := by
  have hy : e • y.1.1 = y.1.1 := y.2
  have hc : e • (lowC g * y.1.1) = lowC g * y.1.1 := by rw [← Matrix.mul_smul, hy]
  have hs : (x + y).1.1 = x.1.1 + y.1.1 := rfl
  unfold IsB InCell
  rw [lowC_mul_nb hnb, lowD_mul_nb hnb, hs]
  refine and_congr_right fun _ => ?_
  simp only [mm]
  rw [mul_add, smul_add, hc, add_comm (lowC g * y.1.1) (e • lowD g), add_left_inj]

end GlobalTheory.CompanionTheory.MuC

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_hermitian_lattice : ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∀ f : hermA D r → ℂ, Continuous f → (∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖f (b + c.1)‖ ≤ u c) → Integrable f lam ∧ (Summable (fun t : ratHerm D r => ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) → ∑' c : ratHerm D r, f c.1 = ∑' t : ratHerm D r, ∫ b, f b * ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
  first | exact @GlobalTheory.CompanionTheory.HermPoisson.poisson_herm | exact GlobalTheory.CompanionTheory.HermPoisson.poisson_herm | (intros; apply GlobalTheory.CompanionTheory.HermPoisson.poisson_herm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactFrameEquivStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_compact_frame_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), Dict → DictInf → IsCMExt F E σ → ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (B : Base F E) (K : Subgroup (G2 σ Y)), IsStdK (σ := σ) (Y := Y) B b K → ∀ x : G2 σ Y, x ∈ K ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uK ε (Fin n) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff | exact GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff | (intros; apply GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff <;> assumption)
end

