module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsInertPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertExist

section Local

open GlobalTheory.SelfDualGenus GlobalTheory.PlaceComp GlobalTheory.HeckeLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem mem_stdLat_iff {n : ℕ} (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔ ∀ i, IsIntegral ℤ (x i) := by
  show x ∈ Formalism.L2.Col.stdLat E n ↔ _
  simp only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x i, h⟩, rfl⟩⟩

theorem antiJ_herm (n : ℕ) (a b : Fin n) :
    ReciprocityTheory.ChartRestriction.G.FD.cc (Formalism.UG.antiJ E n a b) = Formalism.UG.antiJ E n b a := by
  simp only [Formalism.UG.antiJ, add_comm b.val a.val]
  split_ifs <;> simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_one, map_zero]

theorem antiJ_det_ne_zero (n : ℕ) : (Formalism.UG.antiJ E n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (GlobalTheory.DualDivU.antiJ_sq (L := E) (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem selfDual_antiJ (n : ℕ) (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔
      ∀ y ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)),
        IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm (Formalism.UG.antiJ E n) x y) := by
  rw [mem_stdLat_iff]
  constructor
  · intro hx y hy
    rw [mem_stdLat_iff] at hy
    refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
    refine ((hx a).mul ?_).mul ?_
    · unfold Formalism.UG.antiJ; split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · exact (hy b).map (IsCMField.complexConj E : E →+* E).toIntAlgHom
  · intro h i
    have hy : (Pi.single i.rev (1 : E) : Fin n → E) ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) := by
      rw [mem_stdLat_iff]
      intro j
      by_cases hj : j = i.rev
      · subst hj; simpa using isIntegral_one
      · simpa [hj] using isIntegral_zero
    have := h _ hy
    convert this using 1
    simp [ReciprocityTheory.ChartRestriction.G.FD.herm, Formalism.UG.antiJ, Pi.single_apply, ReciprocityTheory.ChartRestriction.G.FD.cc]
    rw [Finset.sum_eq_single i]
    · rw [if_pos (by have := i.2; omega)]
    · intro b _ hb
      rw [if_neg]
      intro hc; apply hb; ext; have := i.2; have := b.2; omega
    · intro h; exact absurd (Finset.mem_univ i) h

theorem locLattice_le {n : ℕ} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    {x : Fin n → LocAlg v} (hx : x ∈ locLattice v (Formalism.L2.Col.stdLat E n)) (i : Fin n) : x i ∈ locOrder v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = y i := ⟨⟨y i, (mem_stdLat_iff y).1 hy i⟩, rfl⟩
    show locEmb v (y i) ∈ locOrder v
    rw [← hz]
    exact locEmb_mem_locOrder v z
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Subalgebra.smul_mem _ hx c

theorem mulVec_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i j, M i j ∈ O) {z : Fin n → R} (hz : ∀ i, z i ∈ O) (i : Fin n) : (M *ᵥ z) i ∈ O := by
  show ∑ j, M i j * z j ∈ O
  exact O.sum_mem fun j _ => mul_mem (hM i j) (hz j)

theorem single_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} (j i : Fin n) :
    (Pi.single j (1 : R) : Fin n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem exists_antiFrame [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) :
    ∃ h : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E),
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 *
        (Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v)) * h.1 = 1 ∧
      (∀ i j, h.1 i j ∈ ordAt E v) ∧ ∀ i j, (h⁻¹).1 i j ∈ ordAt E v := by
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame (antiJ_herm n) (antiJ_det_ne_zero n)
    ⟨Formalism.L2.Col.stdLat_lattice.fg, by
      rw [Formalism.L2.Col.stdLat_eq_span, Submodule.span_span_of_tower]
      convert (Pi.basisFun E (Fin n)).span_eq using 1
      congr 2
      ext i
      exact congrFun (Pi.basisFun_apply E (Fin n) i).symm _⟩ (selfDual_antiJ n) v
  have hs : ∀ j, (Pi.single j (1 : LocAlg v) : Fin n → LocAlg v) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
    intro j
    refine Submodule.subset_span ⟨Pi.single j 1, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← SetLike.mem_coe, mem_stdLat_iff]
      intro i
      by_cases hi : i = j
      · subst hi; simpa using isIntegral_one
      · simpa [hi] using isIntegral_zero
    · funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
  refine ⟨h, ?_, fun i j => ?_, fun i j => ?_⟩
  · have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
      Matrix.transpose_one] at h3
    have hT : ((Formalism.UG.antiJ E n).map (locEmb v))ᵀ = (Formalism.UG.antiJ E n).map (locEmb v) := by
      ext a b; simp only [Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.antiJ, add_comm b.val a.val]
    rw [hT] at h3
    exact h3
  · rw [mem_ordAt_iff]
    have hm : (fun k => (h.1 *ᵥ Pi.single j 1) k) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
      rw [h2]
      intro k
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact single_int (O := (locOrder v).toSubring) j k
    have := locLattice_le v hm i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · rw [mem_ordAt_iff]
    have := (h2 _).1 (hs j) i
    rw [Matrix.mulVec_single_one] at this
    exact this

theorem exists_std [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) {ϖ : E} (h0 : ϖ ≠ 0) (hσ : hc.sig ϖ = ϖ) (d : ℕ → ℤ) (hd : ∀ i : Fin n, d i.rev.1 = -d i.1) :
    ∃ u ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) (1 : Matrix (Fin n) (Fin n) _),
      StdDiv (ordAt E v) 1 (fun i : Fin n => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) u.1 := by
  obtain ⟨h, hh, hi, hi'⟩ := exists_antiFrame hc v n
  have hσι : ∀ x : E, sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) x) =
      inclR (Fv (maximalRealSubfield E) v) (hc.sig x) := fun x => by
    show (Algebra.TensorProduct.map (AlgHom.id _ _) hc.sig) ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ x) =
      (1 : Fv (maximalRealSubfield E) v) ⊗ₜ hc.sig x
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  let t : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)
  let t' : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ (-d i.1))
  have tt : ∀ i, t i * t' i = 1 := fun i => by
    simp only [t, t', ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
  let T : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) :=
    ⟨Matrix.diagonal t, Matrix.diagonal t',
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact tt i,
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact tt i⟩
  have hT : T ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig)
      ((Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v))) := by
    show Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) (Matrix.diagonal t) * _ * Matrix.diagonal t = _
    rw [Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    by_cases hij : i.val + j.val + 1 = n
    · have hj : j = i.rev := Fin.ext (by rw [Fin.val_rev]; omega)
      subst hj
      simp only [Formalism.UG.antiJ, if_pos hij, map_one, mul_one]
      show sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) *
        inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.rev.1) = 1
      rw [hσι, map_zpow₀, hσ, hd, ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
    · simp only [Formalism.UG.antiJ, if_neg hij, map_zero, mul_zero, zero_mul]
  have hu := conj_mem_UJ _ hh hT
  have hTv : ∀ w, T.1 *ᵥ w = t * w := fun w => funext fun k => by
    show (Matrix.diagonal t *ᵥ w) k = t k * w k
    rw [Matrix.mulVec_diagonal]
  refine ⟨h⁻¹ * T * h, hu, (h⁻¹).1, fun z hz i => ?_, fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩,
    fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩, fun z hz => ⟨(h⁻¹).1 *ᵥ z, mulVec_int hi' hz, ?_⟩⟩
  · rw [one_smul]; exact mulVec_int hi' hz i
  · rw [one_smul, one_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTv]
  · have hz' : h.1 *ᵥ ((h⁻¹).1 *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz', hTv]

end Local

section Host

open GlobalTheory.PlaceComp

theorem exists_suppF_divAt : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g := by
  intro D V P e x ϖ d hP hx h1 h2 hlen hdual
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  obtain ⟨v, hf, hef⟩ : ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v e ∧ e * e = e := by
    rcases id hP with ⟨⟨⟨a1, a2, v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩, he⟩ | ⟨-, ⟨v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩
    · rw [← he] at a3
      exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e e hP).1⟩
    · exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e e hP).1⟩
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _)
  have hσ : D.sp.cm.sig (ϖ : D.host.E) = ϖ := by
    rw [hx]
    exact D.sp.cm.sig.commutes _
  have hd : ∀ i : Fin V.rank, d.getD i.rev.1 0 = -d.getD i.1 0 := fun i => by
    have := GlobalTheory.DualDivU.getD_dualLab d hlen i
    rw [hdual] at this
    rw [this, neg_neg]
  obtain ⟨u, hu, hs⟩ := GlobalTheory.InertExist.exists_std D.sp.cm v V.rank h0 hσ (fun i => d.getD i 0) hd
  obtain ⟨g, hg, hg'⟩ := (GlobalTheory.HeckeLabels.exists_div_iff (E := D.host.E) D.sp.cm V hf hef (ϖ : D.host.E)
    (fun i => d.getD i 0) rfl).2 ⟨u, hu, by rw [hf.2.1]; exact hs⟩
  exact ⟨g, hg, hlen, hg'⟩

end Host

end GlobalTheory.InertExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsSplitPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitExist

theorem dv_of_conj {R : Type} [CommRing R] {n : ℕ} {Λ : (Fin n → R) → Prop} {O : R → Prop} {ε : R}
    (hε : ε * ε = ε) {B C M : Matrix (Fin n) (Fin n) R} {u : Fin n → R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B *ᵥ z)
    (hCB : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R))
    (hM : ε • M = ε • (B * Matrix.diagonal u * C)) :
    GlobalTheory.DivDual.Dv Λ O ε u M := by
  have key : ∀ y z : Fin n → R, ε • y = ε • B *ᵥ z →
      ε • M *ᵥ y = ε • B *ᵥ (fun i => u i * z i) := by
    intro y z hyz
    have e1 : (fun i => u i * z i) = Matrix.diagonal u *ᵥ z := by
      funext i; simp [Matrix.mulVec_diagonal]
    have e2 : ε • (C *ᵥ (B *ᵥ z)) = ε • z := by
      rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, hCB, Matrix.smul_mulVec, Matrix.one_mulVec]
    calc ε • M *ᵥ y = (ε • M) *ᵥ y := (Matrix.smul_mulVec _ _ _).symm
      _ = (B * Matrix.diagonal u * C) *ᵥ (ε • y) := by
          rw [hM, Matrix.smul_mulVec, Matrix.mulVec_smul]
      _ = (B * Matrix.diagonal u) *ᵥ (ε • (C *ᵥ (B *ᵥ z))) := by
          rw [hyz, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            Matrix.mulVec_mulVec]
      _ = ε • B *ᵥ (fun i => u i * z i) := by
          rw [e2, e1, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  refine ⟨B, h1, h2, fun y hy => ?_, fun z hz => ⟨ε • B *ᵥ z, h1 z hz, key _ _ ?_⟩⟩
  · obtain ⟨z, hz, e⟩ := h2 y hy
    exact ⟨z, hz, key y z e⟩
  · rw [smul_smul, hε]

end GlobalTheory.SplitExist

namespace GlobalTheory.SplitExist


set_option maxHeartbeats 1000000 in
theorem split_exist : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ : 𝓞 D.host.E) (d : List ℤ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    d.length = V.rank → ∃ g : GA D V, SuppF V (e + cA D e) g ∧ DivAt V e (ϖ : D.host.E) d g := by
  intro D V P e ϖ d hI h1 h2 hd
  have he : e * e = e := hI.1.1
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis V he hI.2
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have hϖ : (ϖ : D.host.E) ≠ 0 := fun h0 => h2 (by
    have : ϖ = 0 := by exact_mod_cast h0
    rw [this]; exact zero_mem _)
  let u : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun i => finPart D (incA D ((ϖ : D.host.E) ^ (d.getD i.1 0)))
  let u' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun i => finPart D (incA D ((ϖ : D.host.E) ^ (-(d.getD i.1 0))))
  have huu : Matrix.diagonal u * Matrix.diagonal u' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    simp [u, u', ← map_mul, zpow_ne_zero _ hϖ]
  have key : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * (C * B) * Y) = finPart D e • (X * Y) := fun X Y => by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, c2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hmm : finPart D e • ((B * Matrix.diagonal u * C) * (B * Matrix.diagonal u' * C)) =
      finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := by
    have : (B * Matrix.diagonal u * C) * (B * Matrix.diagonal u' * C) =
        (B * Matrix.diagonal u) * (C * B) * (Matrix.diagonal u' * C) := by
      simp only [Matrix.mul_assoc]
    rw [this, key, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal u), huu, Matrix.one_mul, c1]
  obtain ⟨g, hg, hgm⟩ := GlobalTheory.SplitLift.split_lift V e hI.1 _ _ hmm
  exact ⟨g, fun i j => hg i j, (GlobalTheory.DivDual.divAt_iff V e _ d g).2 ⟨hd, dv_of_conj hee b1 b2 c2 hgm⟩⟩

end GlobalTheory.SplitExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdealMulHomMapMemMatrixHomLattice
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt

noncomputable section

namespace GlobalTheory.TwU

theorem map_mem_homLat_of_mem_YYl : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : D.host.E →+* Qq) (hA : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 D.host.E) D.host.E)) (h1 : ∀ x : 𝓞 D.host.E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) {k k' : ℕ} (N : Submodule (𝓞 D.host.E) (Fin k → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin k' → D.host.E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (hNa : Submodule.span W ((fun x i => ρ (x i)) '' (N : Set (Fin k → D.host.E))) = colSpan W a) (hNb : Submodule.span W ((fun x i => ρ (x i)) '' (N' : Set (Fin k' → D.host.E))) = colSpan W b), ∀ A ∈ TaylorLogMetric.YYl D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
  intro D P W Qq _ _ _ _ _ _ p hp ρ hA h1 k k' N N' a b hNa hNb

  have hsc : ∀ (c : D.host.E) (M : Matrix (Fin k') (Fin k) D.host.E), (∃ y : W, ρ c = algebraMap W Qq y) →
      M.map ρ ∈ homLat W (colSpan W a) (colSpan W b) → (c • M).map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    rintro c M ⟨y, hy⟩ hM z hz
    have e : (c • M).map ρ = y • M.map ρ := by
      ext i j
      simp [Matrix.map_apply, map_mul, hy, Algebra.smul_def]
    rw [e, Matrix.smul_mulVec]
    exact (colSpan W b).smul_mem y (hM z hz)
  have hO : ∀ c : 𝓞 D.host.E, ∃ y : W, ρ (c : D.host.E) = algebraMap W Qq y := fun c =>
    (h1 c).imp fun y hy => hy.1

  have hAA : ∀ x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ y : W, ρ x = algebraMap W Qq y := by
    intro x hx
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
      ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
    rw [hA] at hx'
    obtain ⟨s, hs, hsx⟩ := hx'
    obtain ⟨t, ht⟩ := Submodule.mem_one.1 hsx
    obtain ⟨ys, hys, hsP⟩ := h1 s
    obtain ⟨yt, hyt⟩ := hO t
    have hu : IsUnit ys := by
      have hmax : IsLocalRing.maximalIdeal W = Ideal.span {(p : W)} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hp
      by_contra hn
      have : ys ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal ys).2 hn
      rw [hmax, Ideal.mem_span_singleton] at this
      exact hs (hsP.2 this)
    refine ⟨hu.unit⁻¹ * yt, ?_⟩
    have e1 : ρ (algebraMap (𝓞 D.host.E) D.host.E t) = ρ (s : D.host.E) * ρ x := by
      rw [ht, Algebra.smul_def, map_mul]
    have e2 : algebraMap W Qq ys ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective W Qq)]
      exact hu.ne_zero
    rw [map_mul, ← hyt]
    change _ = _ * ρ (t : D.host.E)
    rw [show ((t : D.host.E)) = algebraMap (𝓞 D.host.E) D.host.E t from rfl, e1, hys, ← mul_assoc, ← map_mul,
      IsUnit.val_inv_mul, map_one, one_mul]

  have hHom : ∀ A ∈ TaylorLogMetric.homL D N N', A.map ρ ∈ homLat W (colSpan W a) (colSpan W b) := by
    intro A hA'
    induction hA' using Submodule.span_induction with
    | mem A hA0 =>
      intro z hz
      rw [← hNa] at hz
      rw [← hNb]
      induction hz using Submodule.span_induction with
      | mem z hz0 =>
        obtain ⟨x, hx, rfl⟩ := hz0
        refine Submodule.subset_span ⟨A *ᵥ x, hA0 x hx, ?_⟩
        funext i
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hz hz'
      | smul c z _ hz => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hz
    | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
    | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
    | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA
  intro A hA'
  induction hA' using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨c, hc, A, hA0, rfl⟩ := hB
    exact hsc c A (hAA c hc) (hHom A hA0)
  | zero => rw [Matrix.map_zero _ (map_zero ρ)]; exact Submodule.zero_mem _
  | add A B _ _ hA hB => rw [Matrix.map_add _ (map_add ρ)]; exact Submodule.add_mem _ hA hB
  | smul c A _ hA => exact hsc (c : D.host.E) A (hO c) hA

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JacquetModuleCoinvariantsSubsingletonOfCharConj
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

theorem jacquet_subsingleton_of_char_nontrivial_on_conj :
    ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), π.IsIrreducible →
      ∀ (N H : Subgroup G) (χ : H →* ℂˣ) (v : V), v ≠ 0 → (∀ h : H, π h v = (χ h : ℂ) • v) →
      (∀ g : G, ∃ h : H, g * h * g⁻¹ ∈ N ∧ χ h ≠ 1) → Subsingleton (Jacquet π N) := by
  intro G V _ _ _ π hπ N H χ v hv0 hv hconj
  set K : Submodule ℂ V := twKer π N 1 with hK

  have hgv : ∀ g : G, π g v ∈ K := by
    intro g
    obtain ⟨h, hn, hχ⟩ := hconj g
    have hmem : π (g * h * g⁻¹) (π g v) - (1 : ℂ) • π g v ∈ K := by
      refine Submodule.subset_span ⟨⟨_, hn⟩, π g v, ?_⟩
      simp
    have hcalc : π (g * h * g⁻¹) (π g v) = (χ h : ℂ) • π g v := by
      rw [← Module.End.mul_apply, ← map_mul]
      have : g * (h : G) * g⁻¹ * g = g * h := by group
      rw [this, map_mul, Module.End.mul_apply, hv h, map_smul]
    rw [hcalc, ← sub_smul] at hmem
    have hne : (χ h : ℂ) - 1 ≠ 0 := by
      intro e
      apply hχ
      ext
      simpa [sub_eq_zero] using e
    have := K.smul_mem ((χ h : ℂ) - 1)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  let S : Submodule ℂ V := ⨅ g : G, K.comap (π g)
  have hS : ∀ w, w ∈ S ↔ ∀ g : G, π g w ∈ K := by
    intro w; simp [S, Submodule.mem_iInf]
  let Wr : Subrepresentation π :=
    { toSubmodule := S
      apply_mem_toSubmodule := by
        intro g w hw
        rw [hS] at hw ⊢
        intro g'
        rw [← Module.End.mul_apply, ← map_mul]
        exact hw _ }
  have hvW : v ∈ S := (hS v).2 hgv
  have htop : K = ⊤ := by
    rcases hπ.eq_bot_or_eq_top Wr with e | e
    · exfalso
      have : v ∈ Wr.toSubmodule := hvW
      rw [e] at this
      exact hv0 this
    · rw [eq_top_iff]
      intro w _
      have : w ∈ Wr.toSubmodule := by rw [e]; trivial
      have := (hS w).1 this 1
      simpa using this
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective K a
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K b
  exact (Submodule.Quotient.eq K).2 (by rw [htop]; trivial)
end GlobalTheory
end

