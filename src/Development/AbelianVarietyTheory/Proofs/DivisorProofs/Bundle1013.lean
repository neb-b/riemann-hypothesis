module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBounds
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHyperspecialStableLatticeEqMultiple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.SplitLatMatch

open GlobalTheory.SplitHecke

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem half (V : HSp D) (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e)
    (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)))
    (hM : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M)
    (hf : ∀ z ∈ M, finPart D (e + cA D e) • z = z)
    (hb : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V)
    (hK : ∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) :
    ∃ a a' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, finPart D e * a * a' = finPart D e ∧
      ∀ z, (finPart D e • z ∈ M ↔ (finPart D e * a) • z ∈ Formalism.L2.NTheta.LamHat V) := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  obtain ⟨β, hβ⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ V
  obtain ⟨φ, hφ⟩ := GlobalTheory.SplitFrame.exists_factor hπ
  have hπe : π e = 1 := GlobalTheory.SplitHomLattice.pi_idem he hπ
  have hpe : φ (finPart D e) = 1 := by rw [hφ]; exact hπe
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hφs : Function.Surjective φ := fun t => by
    obtain ⟨a, rfl⟩ := hπ.1 t
    exact ⟨finPart D a, hφ a⟩
  have hker : ∀ x, φ x = 0 → finPart D e * x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := GlobalTheory.SplitHecke.Stab.finPart_surj x
    rw [hφ] at hx
    rw [← map_mul, (hπ.2.1 a).1 hx, map_zero]
  let T : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V.rank → Fv D.host.F v) :=
    { toFun := fun z => (β⁻¹).1 *ᵥ fun k => φ (z k)
      map_zero' := by
        have : (fun k : Fin V.rank => φ ((0 : Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) k)) = 0 :=
          funext fun k => by rw [Pi.zero_apply, map_zero, Pi.zero_apply]
        simp only [this, Matrix.mulVec_zero]
      map_add' := by
        intro x y
        have : (fun k => φ ((x + y) k)) = (fun k => φ (x k)) + fun k => φ (y k) :=
          funext fun k => by rw [Pi.add_apply, map_add (f := _), Pi.add_apply]
        simp only [this, Matrix.mulVec_add] }
  have hT : ∀ z, T z = (β⁻¹).1 *ᵥ fun k => φ (z k) := fun z => rfl
  have hTs : ∀ (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) z, T (x • z) = φ x • T z := by
    intro x z
    rw [hT, hT, ← Matrix.mulVec_smul]
    congr 1
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  have hTp : ∀ z, T (finPart D e • z) = T z := by
    intro z; rw [hTs, hpe, one_smul]
  have hmem : ∀ z, finPart D e • z ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, T z i ∈ v.adicCompletionIntegers D.host.F := by
    intro z
    choose y hy using fun k => GlobalTheory.SplitHecke.Stab.finPart_surj (z k)
    have e1 : finPart D e • z = fun i => finPart D (e * y i) := funext fun i => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, hy]
    have e2 : (fun k => φ (z k)) = fun k => π (y k) := funext fun k => by rw [← hy, hφ]
    rw [e1, hβ y, hT, e2]
    exact forall_congr' fun i => isInt_Ov
  have hinj : ∀ z m, T z = T m → finPart D e • z = finPart D e • m := by
    intro z m h
    have h1 : (fun k => φ (z k)) = fun k => φ (m k) := by
      have := congrArg (fun u => β.1 *ᵥ u) h
      simpa only [hT, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec] using this
    funext k
    have h2 := hker (z k - m k) (by rw [map_sub, sub_eq_zero]; exact congrFun h1 k)
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [mul_sub, sub_eq_zero] at h2
    exact h2
  let S : AddSubgroup (Fin V.rank → Fv D.host.F v) := M.map T
  have hS : ∀ z, T z ∈ S ↔ finPart D e • z ∈ M := by
    intro z
    constructor
    · rintro ⟨m, hm, h⟩
      rw [hinj z m h.symm]
      exact hM _ hpO m hm
    · intro h
      exact ⟨_, h, hTp z⟩
  obtain ⟨N, hN, hlo, hup⟩ := hb
  have : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F (Fv D.host.F v)).injective
  have hN' : ((N : ℕ) : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hφN : φ ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = (N : Fv D.host.F v) := map_natCast φ N
  have hf' : finPart D (e + cA D e) * finPart D e = finPart D e := by
    rw [map_add, add_mul, hpp, mul_comm (finPart D (cA D e)), hpq, add_zero]
  obtain ⟨t, ht, hSt⟩ := GlobalTheory.LatticeBetweenMultiples.eq_multiple_of_standard_lattice v S (by
      intro o ho w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨a, ha⟩ := hπ.1 o
      refine ⟨finPart D (e * a) • m, hM _ ((hπ.2.2.2 a).2 (isInt_Ov.2 (ha ▸ ho))) m hm, ?_⟩
      rw [hTs, hφ, map_mul, hπe, one_mul, ha])
    (by
      refine ⟨N, hN', fun w hw => ?_⟩
      choose z hz using fun k => hφs ((β.1 *ᵥ w) k)
      have hTz : T z = w := by
        rw [hT, (funext hz : (fun k => φ (z k)) = β.1 *ᵥ w), Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec]
      have hzL : finPart D e • z ∈ Formalism.L2.NTheta.LamHat V := (hmem z).2 (by rw [hTz]; exact hw)
      have h1 := hlo _ hzL
      rw [smul_smul (finPart D (e + cA D e)), hf'] at h1
      exact ⟨_, h1, by rw [hTs, hTp, hφN, hTz]⟩)
    (by
      refine ⟨N, hN', fun w hw i => ?_⟩
      obtain ⟨m, hm, rfl⟩ := hw
      have h2 : finPart D e • (((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • m) ∈ Formalism.L2.NTheta.LamHat V :=
        GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ (hup m hm)
      have h3 := (hmem _).1 h2 i
      rwa [hTs, hφN, Pi.smul_apply, smul_eq_mul] at h3)
    (by
      intro x hx1 hx2 w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v π he hπ V β x
      have hgK : g ∈ KsphC V ∅ := (GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ V β hβ g hg).2 (by
        rw [hgx]
        exact ⟨fun i j => isInt_Ov.2 (hx1 i j), fun i j => isInt_Ov.2 (hx2 i j)⟩)
      refine ⟨_, hK g hgK hg m hm, ?_⟩
      have e1 : (fun k => φ ((finMat D.sp.cm.sig V.gram g *ᵥ m) k)) = (mt V g).map π *ᵥ fun k => φ (m k) := by
        funext k
        rw [RingHom.map_mulVec, GlobalTheory.SplitHecke.Stab.finMat_eq, Matrix.map_map]
        congr 2
        funext y
        exact hφ y
      rw [hT, hT, e1, ← hgx, rho_val, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one])
  obtain ⟨a, ha⟩ := hφs t
  obtain ⟨a', ha'⟩ := hφs t⁻¹
  refine ⟨a, a', ?_, fun z => ?_⟩
  · have := hker (a * a' - 1) (by rw [map_sub, map_mul, ha, ha', mul_inv_cancel₀ ht, map_one, sub_self])
    linear_combination this
  · rw [← hS, hSt, mul_smul, hmem, hTs, ha]
    simp only [Pi.smul_apply, smul_eq_mul]

end GlobalTheory.SplitLatMatch

namespace GlobalTheory.SplitLatMatch

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem lat_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e + cA D e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e + cA D e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  intro D V P e hP M hMs hf hb hK
  have he : IsSplitIdem D e := hP.1
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨a, a', ha, hA⟩ := half V e he M hMs hf hb hK
  have hsum : cA D e + cA D (cA D e) = e + cA D e := by rw [cA_cA, add_comm]
  obtain ⟨b, b', hb', hB⟩ := half V (cA D e) he' M hMs (by rw [hsum]; exact hf) (by rw [hsum]; exact hb)
    (by rw [hsum]; exact hK)
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hqq : finPart D (cA D e) * finPart D (cA D e) = finPart D (cA D e) := by rw [← map_mul, he'.1]
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hqO : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hqq
  have hfe : finPart D (e + cA D e) = finPart D e + finPart D (cA D e) := map_add _ _ _
  rw [hfe] at hf
  rw [hfe]
  refine ⟨finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e))),
    isUnit_iff_exists_inv.2 ⟨finPart D e * a' + finPart D (cA D e) * b' + (1 - (finPart D e + finPart D (cA D e))),
      by linear_combination (a * a' - a - a' + 1) * hpp + (b * b' - b - b' + 1) * hqq +
        (a * b' + b * a' - a - a' - b - b' + 2) * hpq + ha + hb'⟩, fun z => ⟨fun hz => ⟨hf z hz, ?_⟩, fun ⟨hz, hc⟩ => ?_⟩⟩
  · have h1 := (hA z).1 (hMs _ hpO z hz)
    have h2 := (hB z).1 (hMs _ hqO z hz)
    have h3 := hf z hz
    have e1 : (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z =
        (finPart D e * a) • z + (finPart D (cA D e) * b) • z + (z - (finPart D e + finPart D (cA D e)) • z) := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, h3, sub_self, add_zero]
    exact add_mem h1 h2
  · have e2 : ∀ (p c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), p * (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) = p * c →
        p • ((finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z) = (p * c) • z := by
      intro p c h
      rw [smul_smul, h]
    have h1 : finPart D e • z ∈ M := (hA z).2 (by
      rw [← e2 (finPart D e) a (by linear_combination (a - 1) * hpp + (b - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ hc)
    have h2 : finPart D (cA D e) • z ∈ M := (hB z).2 (by
      rw [← e2 (finPart D (cA D e)) b (by linear_combination (b - 1) * hqq + (a - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hqO _ hc)
    rw [← hz, add_smul]
    exact add_mem h1 h2

end GlobalTheory.SplitLatMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableRangeOneDetUnitElementary
section
open NumberField IsDedekindDomain GlobalTheory.HaarLin

namespace GlobalTheory.HaarLin.Gauss

open Matrix

variable {R : Type} [CommRing R]

theorem transvection_mem {κ : Type} [Fintype κ] [DecidableEq κ] {i j : κ} (h : i ≠ j) (c : R) :
    transvection i j c ∈ TD R κ :=
  Submonoid.subset_closure (Or.inl ⟨i, j, c, h, rfl⟩)

theorem diagonal_mem {κ : Type} [Fintype κ] [DecidableEq κ] (d : κ → Rˣ) :
    (diagonal fun i => (d i : R)) ∈ TD R κ :=
  Submonoid.subset_closure (Or.inr ⟨d, rfl⟩)

theorem exists_inv {κ : Type} [Fintype κ] [DecidableEq κ] {A : Matrix κ κ R} (hA : A ∈ TD R κ) :
    ∃ B ∈ TD R κ, B * A = 1 ∧ A * B = 1 := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨transvection i j (-c), transvection_mem hij _, ?_, ?_⟩ <;>
        simp [transvection_mul_transvection_same _ _ hij]
    · refine ⟨_, diagonal_mem (fun i => (d i)⁻¹), ?_, ?_⟩ <;>
        simp [diagonal_mul_diagonal]
  | one => exact ⟨1, one_mem _, by simp, by simp⟩
  | mul A B _ _ IA IB =>
    obtain ⟨A', hA', h1, h2⟩ := IA
    obtain ⟨B', hB', h3, h4⟩ := IB
    refine ⟨B' * A', mul_mem hB' hA', ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc A', h1, one_mul, h3]
    · rw [mul_assoc, ← mul_assoc B, h4, one_mul, h2]

theorem of_left {κ : Type} [Fintype κ] [DecidableEq κ] {E M : Matrix κ κ R} (hE : E ∈ TD R κ)
    (hM : IsUnit M.det) (h : IsUnit (E * M).det → E * M ∈ TD R κ) : M ∈ TD R κ := by
  obtain ⟨B, hB, h1, h2⟩ := exists_inv hE
  have hd : IsUnit E.det := IsUnit.of_mul_eq_one B.det (by rw [← det_mul, h2, det_one])
  have := mul_mem hB (h (by rw [det_mul]; exact hd.mul hM))
  rwa [← mul_assoc, h1, one_mul] at this

theorem of_right {κ : Type} [Fintype κ] [DecidableEq κ] {E M : Matrix κ κ R} (hE : E ∈ TD R κ)
    (hM : IsUnit M.det) (h : IsUnit (M * E).det → M * E ∈ TD R κ) : M ∈ TD R κ := by
  obtain ⟨B, hB, h1, h2⟩ := exists_inv hE
  have hd : IsUnit E.det := IsUnit.of_mul_eq_one B.det (by rw [← det_mul, h2, det_one])
  have := mul_mem (h (by rw [det_mul]; exact hM.mul hd)) hB
  rwa [mul_assoc, h2, mul_one] at this

theorem rowOp {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ M : Matrix κ κ R, (∀ b, (E * M) p b = M p b + ∑ k ∈ s, w k * M k b) ∧
      ∀ a b, a ≠ p → (E * M) a b = M a b := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH (fun h => hs (by simp [h]))
    refine ⟨transvection p k (w k) * E, mul_mem (transvection_mem hkp _) hE, fun M => ⟨fun b => ?_, fun a b ha => ?_⟩⟩
    · rw [mul_assoc, transvection_mul_apply_same, (H M).1, (H M).2 _ _ hkp.symm, Finset.sum_insert hk]
      ring
    · rw [mul_assoc, transvection_mul_apply_of_ne _ _ _ _ ha, (H M).2 _ _ ha]

theorem colOpLeft {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ (M : Matrix κ κ R) a b, (E * M) a b = M a b + if a ∈ s then w a * M p b else 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    have hps : p ∉ s := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH hps
    refine ⟨transvection k p (w k) * E, mul_mem (transvection_mem hkp.symm _) hE, fun M a b => ?_⟩
    by_cases ha : a = k
    · subst ha
      rw [mul_assoc, transvection_mul_apply_same, H, H]
      simp [hk, hps]
    · rw [mul_assoc, transvection_mul_apply_of_ne _ _ _ _ ha, H]
      simp [ha]

theorem colOpRight {κ : Type} [Fintype κ] [DecidableEq κ] (p : κ) (w : κ → R) (s : Finset κ) (hs : p ∉ s) :
    ∃ E ∈ TD R κ, ∀ (M : Matrix κ κ R) a b, (M * E) a b = M a b + if b ∈ s then w b * M a p else 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | insert k s hk IH =>
    have hkp : p ≠ k := fun h => hs (by simp [h])
    have hps : p ∉ s := fun h => hs (by simp [h])
    obtain ⟨E, hE, H⟩ := IH hps
    refine ⟨E * transvection p k (w k), mul_mem hE (transvection_mem hkp _), fun M a b => ?_⟩
    by_cases hb : b = k
    · subst hb
      rw [← mul_assoc, mul_transvection_apply_same, H, H]
      simp [hk, hps]
    · rw [← mul_assoc, mul_transvection_apply_of_ne _ _ _ _ hb, H]
      simp [hb]

theorem reindex_mem {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    {A : Matrix κ κ R} (hA : A ∈ TD R κ) : A.submatrix e.symm e.symm ∈ TD R κ' := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · have : (transvection i j c).submatrix e.symm e.symm = transvection (e i) (e j) c := by
        ext a b
        simp [transvection, Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply]
      rw [this]
      exact transvection_mem (e.injective.ne hij) c
    · rw [submatrix_diagonal_equiv]
      exact diagonal_mem (fun i => d (e.symm i))
  | one => rw [submatrix_one_equiv]; exact one_mem _
  | mul A B _ _ IA IB =>
    rw [← submatrix_mul_equiv A B e.symm e.symm e.symm]
    exact mul_mem IA IB

theorem fromBlocks_mem {κ : Type} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ R} (hA : A ∈ TD R κ) : fromBlocks A 0 0 (1 : Matrix Unit Unit R) ∈ TD R (κ ⊕ Unit) := by
  induction hA using Submonoid.closure_induction with
  | mem N hN =>
    rcases hN with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · have : transvection (Sum.inl i) (Sum.inl j) c = fromBlocks (transvection i j c) 0 0 (1 : Matrix Unit Unit R) :=
        TransvectionStruct.toMatrix_sumInl Unit (⟨i, j, hij, c⟩ : TransvectionStruct κ R)
      rw [← this]
      exact transvection_mem (Sum.inl_injective.ne hij) c
    · rw [← diagonal_one, fromBlocks_diagonal]
      convert diagonal_mem (R := R) (Sum.elim d (fun _ : Unit => 1)) using 2
      ext x
      cases x <;> rfl
  | one => rw [fromBlocks_one]; exact one_mem _
  | mul A B _ _ IA IB =>
    have := mul_mem IA IB
    rw [fromBlocks_multiply] at this
    simpa using this

theorem step {κ : Type} [Fintype κ] [DecidableEq κ] (hR : HasStableRangeOne R)
    (IH : ∀ N : Matrix κ κ R, IsUnit N.det → N ∈ TD R κ)
    (M : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R) (hM : IsUnit M.det) : M ∈ TD R (κ ⊕ Unit) := by
  set l : κ ⊕ Unit := Sum.inr () with hl
  set s : Finset (κ ⊕ Unit) := Finset.univ.erase l with hs
  have hls : l ∉ s := Finset.notMem_erase _ _
  have hin : ∀ i : κ, Sum.inl i ∈ s := fun i => by simp [hs, hl]
  have h1 : (M⁻¹ * M) l l = 1 := by rw [nonsing_inv_mul M hM, one_apply_eq]
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ l)] at h1
  obtain ⟨t, ht⟩ := hR (M l l) (∑ k ∈ s, M⁻¹ l k * M k l) ⟨M⁻¹ l l, 1, by rw [one_mul]; exact h1⟩
  obtain ⟨E₁, hE₁, H₁⟩ := rowOp l (fun k => t * M⁻¹ l k) s hls
  refine of_left hE₁ hM fun hM₁ => ?_
  have hu : IsUnit ((E₁ * M) l l) := by
    rw [(H₁ M).1]
    simpa [Finset.mul_sum, mul_assoc] using ht
  generalize E₁ * M = M₁ at hM₁ hu
  obtain ⟨u, hu⟩ := hu
  obtain ⟨E₂, hE₂, H₂⟩ := colOpLeft l (fun a => - M₁ a l * ↑u⁻¹) s hls
  refine of_left hE₂ hM₁ fun hM₂ => ?_
  have hu₂ : (E₂ * M₁) l l = u := by rw [H₂, if_neg hls, add_zero, hu]
  have hc₂ : ∀ i : κ, (E₂ * M₁) (Sum.inl i) l = 0 := fun i => by
    rw [H₂, if_pos (hin i), ← hu, mul_assoc, Units.inv_mul]; ring
  generalize E₂ * M₁ = M₂ at hM₂ hu₂ hc₂
  obtain ⟨E₃, hE₃, H₃⟩ := colOpRight l (fun b => - M₂ l b * ↑u⁻¹) s hls
  refine of_right hE₃ hM₂ fun hM₃ => ?_
  have hu₃ : (M₂ * E₃) l l = u := by rw [H₃, if_neg hls, add_zero, hu₂]
  have hc₃ : ∀ i : κ, (M₂ * E₃) (Sum.inl i) l = 0 := fun i => by
    rw [H₃, if_neg hls, add_zero, hc₂]
  have hr₃ : ∀ i : κ, (M₂ * E₃) l (Sum.inl i) = 0 := fun i => by
    rw [H₃, if_pos (hin i), hu₂, mul_assoc, Units.inv_mul]; ring
  generalize M₂ * E₃ = M₃ at hM₃ hu₃ hc₃ hr₃
  have hform : M₃ = (diagonal fun i => ((Sum.elim (fun _ => 1) (fun _ => u) : κ ⊕ Unit → Rˣ) i : R)) *
      fromBlocks M₃.toBlocks₁₁ 0 0 (1 : Matrix Unit Unit R) := by
    ext a b
    rw [diagonal_mul]
    rcases a with a | ⟨⟩ <;> rcases b with b | ⟨⟩
    · simp [toBlocks₁₁]
    · simpa using hc₃ a
    · simpa using hr₃ b
    · simpa using hu₃
  have hN : IsUnit M₃.toBlocks₁₁.det := by
    rw [hform, det_mul, det_fromBlocks_zero₂₁, det_one, mul_one] at hM₃
    exact isUnit_of_mul_isUnit_right hM₃
  rw [hform]
  exact mul_mem (diagonal_mem _) (fromBlocks_mem (IH _ hN))

theorem mem_TD_of_isUnit_det : ∀ (R : Type) [CommRing R], HasStableRangeOne R → ∀ (κ : Type) [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R), IsUnit M.det → M ∈ TD R κ := by
  intro R _ hR κ _ _
  have key : ∀ n : ℕ, ∀ N : Matrix (Fin n) (Fin n) R, IsUnit N.det → N ∈ TD R (Fin n) := by
    intro n
    induction n with
    | zero => intro N _; rw [Subsingleton.elim N 1]; exact one_mem _
    | succ n IH =>
      intro N hN
      let e : Fin n ⊕ Unit ≃ Fin (n + 1) := (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
      have := reindex_mem e (step hR IH (N.submatrix e e) (by rwa [det_submatrix_equiv_self]))
      simpa using this
  intro M hM
  let e := (Fintype.equivFin κ).symm
  have := reindex_mem e (key _ (M.submatrix e e) (by rwa [det_submatrix_equiv_self]))
  simpa using this

end GlobalTheory.HaarLin.Gauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFixedFieldEmbeddingInjective
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc.BaseChangeCent

variable {p : ℕ} [Fact p.Prime]

def shL (G : HTGroup p) : G.C →ₗ[ℚ] G.C where
  toFun := sh G
  map_add' x y := by simp only [sh, map_add (f := _), MulOpposite.unop_add]
  map_smul' q x := by
    show (G.star (q • x)).unop = q • (G.star x).unop
    rw [map_rat_smul]; rfl

theorem shL_apply (G : HTGroup p) (c : G.C) : shL G c = sh G c := rfl

def phi (G : HTGroup p) (β Y : G.C) (β' : G.C) : G.C →ₗ[ℚ] G.C × G.C :=
  (LinearMap.mulRight ℚ Y - LinearMap.mulLeft ℚ Y).prod
    (LinearMap.mulLeft ℚ β ∘ₗ LinearMap.mulRight ℚ β' ∘ₗ shL G - LinearMap.id)

theorem phi_apply (G : HTGroup p) (β Y β' c : G.C) :
    phi G β Y β' c = (c * Y - Y * c, β * sh G c * β' - c) := by
  simp [phi, shL_apply, mul_assoc]

theorem lTensor_phi (G : HTGroup p) (K : Type) [Field K] [Algebra ℚ K] (β Y β' : G.C)
    (x : K ⊗[ℚ] G.C) :
    TensorProduct.prodRight ℚ ℚ K G.C G.C ((phi G β Y β').lTensor K x) =
      (x * inC G K Y - inC G K Y * x, inC G K β * (starT G.star K x).unop * inC G K β' - x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp <;> rfl
  | tmul k c =>
    simp only [LinearMap.lTensor_tmul, phi_apply, TensorProduct.prodRight_tmul, inC, starT_tmul,
      AlgHom.coe_toRingHom, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_sub, sh]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy]
    simp only [map_add (f := _), MulOpposite.unop_add, mul_add, add_mul, Prod.mk_add_mk]
    refine Prod.ext ?_ ?_ <;> dsimp only <;> abel

end GlobalTheory.FinClsLoc.BaseChangeCent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBoundsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbit_norm_bounds : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → ∃ k : ℕ, ∀ (γ : Gp G) (δ z y : Gr G r), IsNrm G r γ δ z → φ (y⁻¹ * δ * sigG G r y) ≠ 0 → ‖((γ.1 : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k ∧ ‖((γ.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k ∧ (∀ (w : Fin G.m) (μ : PadicAlgCl p), (((γ.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) ∧ (∀ (w : Fin G.m) (μ : PadicAlgCl p), ((((γ.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) := by
  first | (exact @GlobalTheory.AtPBd.main) | (exact GlobalTheory.AtPBd.main) | (intros; apply GlobalTheory.AtPBd.main  <;> assumption)
end

