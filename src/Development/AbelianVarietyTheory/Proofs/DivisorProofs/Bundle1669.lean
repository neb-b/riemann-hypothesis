module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.FrameTransport.Cong

variable {D : D7}

theorem adSwap_mem_intAf (x : StandardLatticesGL3.AE D) (hx : x ∈ StandardLatticesGL3.OhE D) :
    adSwap D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := _root_.GlobalTheory.FrameTransport.adSwap_mem_intAf_of_OhE x hx

theorem adSwap_inc (e : D.host.E) : adSwap D (StandardLatticesGL3.inc D e) = inclEAf D e := by
  have h1 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
    show GlobalTheory.LFun.toFinAd ℚ D.host.E ((1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ⊗ₜ e) = _
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  have h2 : GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e) = (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e := by
    show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D e)) = _
    rw [h1, RingEquiv.symm_apply_eq]
    show _ = GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ e)
    rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D e)) = _
  rw [h2]
  rfl

theorem intG_entries {n : ℕ} (k : StandardLatticesGL3.GA D n) (hk : k ∈ GlobalTheory.NormSum.intG D n) : StandardLatticesGL3.IntG D k.1 := by
  have hmul : ∀ a b : GL (Fin n) (StandardLatticesGL3.AE D), (∀ i j, a.val i j ∈ StandardLatticesGL3.OhE D) → (∀ i j, b.val i j ∈ StandardLatticesGL3.OhE D) →
      ∀ i j, (a * b).val i j ∈ StandardLatticesGL3.OhE D := fun a b ha hb i j => by
    rw [Units.val_mul, Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (ha i l) (hb l j)
  let H : Subgroup (StandardLatticesGL3.GA D n) :=
    { carrier := {k | StandardLatticesGL3.IntG D k.1}
      mul_mem' := fun {a b} ha hb i j => by
        refine ⟨hmul a.1 b.1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j, ?_⟩
        have e : ((a * b : StandardLatticesGL3.GA D n) : GL (Fin n) (StandardLatticesGL3.AE D))⁻¹ = b.1⁻¹ * a.1⁻¹ := by
          rw [Subgroup.coe_mul, _root_.mul_inv_rev]
        rw [e]
        exact hmul _ _ (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
      one_mem' := fun i j => by
        have h1 : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) i j ∈ StandardLatticesGL3.OhE D := fun i j => by
          rw [Matrix.one_apply]
          split_ifs
          exacts [Subring.one_mem _, Subring.zero_mem _]
        exact ⟨h1 i j, by rw [Subgroup.coe_one, inv_one]; exact h1 i j⟩
      inv_mem' := fun {a} ha i j => by
        refine ⟨(ha i j).2, ?_⟩
        rw [Subgroup.coe_inv, inv_inv]
        exact (ha i j).1 }
  exact (Subgroup.closure_le H).2 (fun k hk => hk) hk

theorem hatL_colLat_int {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (i : Fin n) :
    ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  GlobalTheory.T.completedColumnLattice_integral_frameCoords fr y hy i

theorem col_mem_hatL {n : ℕ} (fr : GL (Fin n) D.host.E) (j : Fin n) :
    (fun i => inclEAf D (fr.val i j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) :=
  Submodule.subset_span ⟨fun a => fr.val a j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

theorem eaf_mul_comm (a b : Lev.EAf D) : a * b = b * a := mul_comm a b

set_option maxHeartbeats 1000000 in
theorem hatL_colLat_of_int {n : ℕ} (fr : GL (Fin n) D.host.E) (z : Fin n → Lev.EAf D)
    (hz : ∀ i, z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  have e : (Formalism.UG.bc (inclEAf D) fr).val *ᵥ z =
      ∑ j, (⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j)) := by
    funext i
    rw [Finset.sum_apply]
    show ∑ j, (Formalism.UG.bc (inclEAf D) fr).val i j * z j =
      ∑ j, ((⟨z j, hz j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • (fun i => inclEAf D (fr.val i j))) i
    exact Finset.sum_congr rfl fun j _ => eaf_mul_comm _ _
  exact (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) e).mpr
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (col_mem_hatL fr j))

theorem mul_mem_spanIncl (𝔪 : Ideal (𝓞 D.host.E)) (a z : Lev.EAf D)
    (ha : a ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))))
    (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    a * z ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have h3 := Submodule.smul_mem _ (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ha
  have e : (⟨z, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) • a = a * z := mul_comm z a
  exact e ▸ h3

theorem adSwap_hatId (𝔪 : Ideal (𝓞 D.host.E)) (c : StandardLatticesGL3.AE D) (hc : c ∈ SqNum.hatId D 𝔪) :
    adSwap D c ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E))) := by
  have hle : SqNum.hatId D 𝔪 ≤ (Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))).toAddSubgroup.comap
        (adSwap D).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 fun y hy => ?_
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    have e : adSwap D (StandardLatticesGL3.inc D (b : D.host.E) * s) = inclEAf D (b : D.host.E) * adSwap D s :=
      (map_mul (adSwap D) _ _).trans (congrArg (· * adSwap D s) (adSwap_inc _))
    exact (congrArg (fun v => v ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) e).mpr
      (mul_mem_spanIncl 𝔪 _ _ (Submodule.subset_span ⟨b, hb, rfl⟩) (adSwap_mem_intAf s hs))
  exact hle hc

theorem hatL_smul_colLat {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (w : Fin n → Lev.EAf D)
    (hw : ∀ i, w i ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((fun b : 𝓞 D.host.E => inclEAf D (b : D.host.E)) '' (𝔪 : Set (𝓞 D.host.E)))) :
    (Formalism.UG.bc (inclEAf D) fr).val *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) :=
  GlobalTheory.T.frame_mulVec_completedIdeal_mem_completedIdealLattice fr 𝔪 w hw

theorem hatL_transport {n : ℕ} (uf : GL (Fin n) (Lev.EAf D)) (L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (h : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (y : Fin n → Lev.EAf D) (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • L)) :
    uf.val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) :=
  GlobalTheory.T.completedLatticeMap_idealMul_transport uf L Λ h 𝔪 y hy

theorem frConj_val {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ ((Formalism.UG.bc (adSwap D) k).val *ᵥ
      ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [frConj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem bc_adSwap_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    (Formalism.UG.bc (adSwap D) k).val i j = adSwap D (k.val i j) := rfl

theorem GL_mulVec_inv {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P.val *ᵥ (P⁻¹.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem GL_inv_mulVec {A : Type} [CommRing A] {n : ℕ} (P : GL (Fin n) A) (y : Fin n → A) :
    P⁻¹.val *ᵥ (P.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem frConj_sub {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D)) (y : Fin n → Lev.EAf D) :
    (frConj fr k).val *ᵥ y - y = (Formalism.UG.bc (inclEAf D) fr).val *ᵥ
      (((Formalism.UG.bc (adSwap D) k).val - 1) *ᵥ ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y)) := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, GL_mulVec_inv (Formalism.UG.bc (inclEAf D) fr) y,
    frConj_val fr k y]

theorem bc_adSwap_sub_one_apply {n : ℕ} (k : GL (Fin n) (StandardLatticesGL3.AE D)) (i j : Fin n) :
    ((Formalism.UG.bc (adSwap D) k).val - 1) i j = adSwap D ((k.val - 1) i j) := by
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
  congr 1
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  exacts [(map_one (adSwap D)).symm, (map_zero (adSwap D)).symm]

theorem frConj_stab {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, k.val i j ∈ StandardLatticesGL3.OhE D) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  rw [frConj_val]
  refine hatL_colLat_of_int fr _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (by rw [bc_adSwap_apply]; exact adSwap_mem_intAf _ (hk i j))
    (hatL_colLat_int fr y hy j)

theorem frConj_stab_iff {n : ℕ} (fr : GL (Fin n) D.host.E) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : StandardLatticesGL3.IntG D k) (y : Fin n → Lev.EAf D) :
    y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (frConj fr k).val *ᵥ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := by
  refine ⟨frConj_stab fr k (fun i j => (hk i j).1) y, fun h => ?_⟩
  have h2 := frConj_stab fr k⁻¹ (fun i j => (hk i j).2) _ h
  have e : (frConj fr k⁻¹).val *ᵥ ((frConj fr k).val *ᵥ y) = y := by
    rw [map_inv]; exact GL_inv_mulVec _ y
  exact e ▸ h2

theorem frConj_cong {n : ℕ} (fr : GL (Fin n) D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (k : GL (Fin n) (StandardLatticesGL3.AE D))
    (hk : ∀ i j, (k.val - 1) i j ∈ SqNum.hatId D 𝔪) (y : Fin n → Lev.EAf D)
    (hy : y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) :
    (frConj fr k).val *ᵥ y - y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • colLat fr) := by
  rw [frConj_sub fr k y]
  refine hatL_smul_colLat fr 𝔪 _ fun i => ?_
  show (∑ j, ((Formalism.UG.bc (adSwap D) k).val - 1) i j * ((Formalism.UG.bc (inclEAf D) fr)⁻¹.val *ᵥ y) j) ∈ _
  refine Submodule.sum_mem _ fun j _ => ?_
  have h4 := mul_mem_spanIncl 𝔪 _ _ (adSwap_hatId 𝔪 _ (hk i j)) (hatL_colLat_int fr y hy j)
  rw [bc_adSwap_sub_one_apply k i j]
  exact h4


set_option maxHeartbeats 1000000 in
theorem conj_mem_congLev : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (uf : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ uf.val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (k : StandardLatticesGL3.GA D V.rank), k ∈ GlobalTheory.NormSum.intG D V.rank → GlobalTheory.FunObj.SqNum.CongOne D 𝔪 k → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram → uf * GlobalTheory.FrameTransport.frConj fr k.1 * uf⁻¹ ∈ congLev D.sp.cm V.gram Λ 𝔪 := by
  intro D V fr uf Λ hL 𝔪 k hk hc hU
  have hM : ∀ x, x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      uf⁻¹.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) := fun x =>
    ((hL (uf⁻¹.val *ᵥ x)).trans (by rw [GL_mulVec_inv uf x])).symm
  have hg : ∀ x, (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x = uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x)) := by
    intro x
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hg' : ∀ x, uf⁻¹.val *ᵥ ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x) = (frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) := by
    intro x
    rw [hg x, GL_inv_mulVec]
  refine ⟨hU, fun x => ?_, fun x hx => ?_⟩
  · refine (hM x).trans ((frConj_stab_iff fr k.1 (intG_entries k hk) _).trans ?_)
    exact ((hM ((uf * frConj fr k.1 * uf⁻¹).val *ᵥ x)).trans
      (Iff.of_eq (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) (hg' x)))).symm
  · have hy := (hM x).1 hx
    have h5 := hatL_transport uf (colLat fr) Λ (fun v hv => (hL v).1 hv) 𝔪 _ (frConj_cong fr 𝔪 k.1 hc _ hy)
    have e : uf.val *ᵥ ((frConj fr k.1).val *ᵥ (uf⁻¹.val *ᵥ x) - uf⁻¹.val *ᵥ x) =
        (uf * frConj fr k.1 * uf⁻¹).val *ᵥ x - x := by
      exact (Matrix.mulVec_sub uf.val _ _).trans (congrArg₂ HSub.hSub (hg x).symm (GL_mulVec_inv uf x))
    exact Eq.mp (congrArg (fun v => v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ)) e) h5

end GlobalTheory.FrameTransport.Cong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterTrivialSubfieldKillsIdeleNorms
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
noncomputable section

namespace GlobalTheory.NuCharNorm

open Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.LocTriv
open GlobalTheory.Mem.Chr (finPartI unitIdl locF)
open GlobalTheory.NormSum.UnramHecke GlobalTheory.Mem.Col2.SplitChar

section General

variable {L : Type} [Field L] [NumberField L] {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem inf_upF (χ : HChar L) (k : Fˣ) : χ.inf (upF F k) = ∏ w : InfinitePlace F, χ.resInf w k := by
  classical
  rw [HChar.inf, MonoidHom.comp_apply, infDiag, MonoidHom.finsetProd_apply, map_prod,
    ← Finset.prod_fiberwise Finset.univ fun w : InfinitePlace L => w.comap (algebraMap F L)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [HChar.resInf_apply]
  exact Finset.prod_congr (by ext; simp [aboveInf]) fun _ _ => rfl

end General

theorem norm_killed (D : D7) (χ : HChar D.host.E) (ht : χ.TrivOn D.host.F) (M : ℕ) (hM : 0 < M)
    (hker : ∀ a : Ideles D.host.E, a ∈ unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) →
      (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤
        Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1)
    (x : (AE D)ˣ) : χ.1 (finIdl D (x * sgU D x)) = 1 := by
  have hfin : ∀ k : (D.host.F)ˣ, χ.1 (finIdl D (incU D (upF D.host.F k))) = 1 := fun k => by
    have h1 := χ.2.2 (upF D.host.F k)
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU] at h1
    have h2 : χ.inf (upF D.host.F k) = 1 := by
      rw [inf_upF]
      exact Finset.prod_eq_one fun w _ => ht.2 w k
    rw [HChar.inf, MonoidHom.comp_apply] at h2
    rw [h2, one_mul] at h1
    exact h1
  obtain ⟨n, hn, hx⟩ := GlobalTheory.HeckeVal.exists_denom D ((x⁻¹ : (AE D)ˣ) : AE D)
  obtain ⟨a, r, hr, e⟩ := exists_approx (x : AE D) (Nat.mul_pos (Nat.mul_pos prod_g_pos hM) hn)
  have hs : -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) ∈ OhE D := neg_mem (mul_mem hr hx)
  have h1 : inc D a * ((x⁻¹ : (AE D)ˣ) : AE D) - 1 =
      ((∏ i, D.host.g i : ℕ) : AE D) * ((M : AE D) * -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D)))) := by
    rw [Nat.cast_mul, Nat.cast_mul] at e
    linear_combination x.mul_inv - ((x⁻¹ : (AE D)ˣ) : AE D) * e
  generalize -(r * ((n : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D))) = s at hs h1
  generalize hG : ((∏ i, D.host.g i : ℕ) : AE D) = G at h1
  have hGm : G ∈ OhE D := hG ▸ natCast_mem _ _
  have hGs : sgA D G = G := hG ▸ map_natCast _ _
  have hMs : sgA D (M : AE D) = M := map_natCast _ _
  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.E (D.host.g_prime 0)
    have := vl_cong (mul_mem (natCast_mem _ M) hs) 0 v hv
    rw [hG, ← h1, map_zero, zero_mul, zero_sub, Valuation.map_neg, map_one] at this
    exact lt_irrefl _ this
  let z : (AE D)ˣ := incU D (Units.mk0 a ha) * x⁻¹
  have hz : (z : AE D) = 1 + G * ((M : AE D) * s) := eq_add_of_sub_eq' h1
  let w : (AE D)ˣ := z * sgU D z
  have hw : (w : AE D) - 1 = (M : AE D) * (G * (s + sgA D s + G * M * s * sgA D s)) := by
    have e1 : (w : AE D) = (z : AE D) * sgA D z := rfl
    rw [e1, hz, map_add (f := _), map_one, map_mul, map_mul, hGs, hMs]
    ring
  have hwM : ∀ P, vl D P ((w : AE D) - 1) ≤ vl D P (M : AE D) := fun P => by
    rw [hw, map_mul]
    exact mul_le_of_le_one_right' (vl_le (mul_mem hGm (add_mem (add_mem hs (sgA_mem D hs))
      (mul_mem (mul_mem (mul_mem hGm (natCast_mem _ _)) hs) (sgA_mem D hs)))) P)
  have hvM : ∀ P, vl D P (M : AE D) = Valued.v (((M : D.host.E) : P.adicCompletion D.host.E)) := fun P => by
    rw [vl_nat]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm
  obtain ⟨c, -, -, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  obtain ⟨b, hb, hun, hc⟩ := exists_of_balanced hu ((χ.1.comp (finPartI D.host.E)).ker)
    (fun v k => (MonoidHom.mem_ker).2 (GlobalTheory.Mem.KerDet.map_finPartI_locF ht v k)) (finIdl D w) (norm_balanced z)
  have hb' : χ.1 (finPartI D.host.E b) = 1 := (MonoidHom.mem_ker).1 hb
  have hc1 : χ.1 (finPartI D.host.E (b⁻¹ * finIdl D w)) = 1 := by
    refine hker _ hun (fun _ => rfl) fun P => ?_
    change Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ _
    rw [← hvM]
    by_cases hP : vl D P ((w : AE D) - 1) < 1
    · have h2 : valAt P (finIdl D w) = 1 := by
        rw [valAt_apply, ← sub_add_cancel ((finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P) 1, add_comm]
        exact Valuation.map_one_add_of_lt _ (by rw [vl_sub_one]; exact hP)
      have h3 : Units.map (ev P) (b⁻¹ * finIdl D w) = Units.map (ev P) (finIdl D w) := by
        rw [map_mul, map_inv, hc P h2, inv_one, one_mul]
      have h4 : ((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P =
          (finIdl D w : AdeleRing (𝓞 D.host.E) D.host.E).2 P := congrArg Units.val h3
      rw [h4, vl_sub_one]
      exact hwM P
    · have hM1 : vl D P (M : AE D) = 1 := le_antisymm (vl_le (natCast_mem _ _) P) ((not_lt.1 hP).trans (hwM P))
      rw [hM1]
      refine (Valuation.map_sub _ _ _).trans ?_
      have hP1 : Valued.v (((b⁻¹ * finIdl D w : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E).2 P) = 1 := hun P
      rw [hP1, map_one, max_self]
  have e2 : finPartI D.host.E (b⁻¹ * finIdl D w) = (finPartI D.host.E b)⁻¹ * finIdl D w := by
    rw [map_mul, map_inv, finPartI_finIdl]
  rw [e2, map_mul, map_inv, hb', inv_one, one_mul] at hc1
  obtain ⟨k, hk⟩ := exists_real_norm (Units.mk0 a ha)
  have h5 : χ.1 (finIdl D (incU D (Units.mk0 a ha) * sgU D (incU D (Units.mk0 a ha)))) = 1 := by
    rw [hk]
    exact hfin k
  have h6 : χ.1 (finIdl D ((incU D (Units.mk0 a ha) * x⁻¹) * sgU D (incU D (Units.mk0 a ha) * x⁻¹))) = 1 := hc1
  rw [map_mul (sgU D), mul_mul_mul_comm, map_inv, ← mul_inv, map_mul, map_mul, h5, one_mul, map_inv, map_inv,
    inv_eq_one] at h6
  exact h6

end GlobalTheory.NuCharNorm

theorem GlobalTheory.NuCharNorm.chi_norm_one : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.TrivOn D.host.F → (∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles D.host.E, a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E → (∀ w, (a : AdeleRing (𝓞 D.host.E) D.host.E).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 P - 1) ≤ Valued.v ((M : D.host.E) : P.adicCompletion D.host.E)) → χ.1 a = 1) → ∀ x : (AE D)ˣ, χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D (x * sgU D x)) = 1 :=
  fun D χ ht ⟨M, hM, h⟩ x => GlobalTheory.NuCharNorm.norm_killed D χ ht M hM h x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedInertKillsUnits
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open GlobalTheory.Mem.Col2.SplitChar

namespace GlobalTheory.UnrKill

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 K) ∈ P.asIdeal := by
  haveI := P.isPrime
  haveI : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨ringChar (𝓞 K ⧸ P.asIdeal), CharP.char_is_prime (𝓞 K ⧸ P.asIdeal) _, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]

theorem vl_nat_eq_one {D : D7} {q m : ℕ} (hm : Nat.Coprime m q) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : GlobalTheory.Mem.Chr.OverP D.host q v) : vl D v (m : AE D) = 1 := by
  refine le_antisymm (vl_le (natCast_mem _ _) v) (not_lt.1 fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have hab' := congrArg (Int.cast : ℤ → AE D) hab
  push_cast at hab'
  have h2 : vl D v ((a : AE D) * m) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt hlt
  have h3 : vl D v ((b : AE D) * q) < 1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left' (vl_le (intCast_mem _ _) v)).trans_lt (val_nat_lt hv)
  have h4 := Valuation.map_add_lt _ h2 h3
  rw [hab', map_one] at h4
  exact lt_irrefl _ h4

theorem vl_eq_zero_of_zeroAt {D : D7} {q : ℕ} {x : AE D} (h : ZeroAt D q x) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : GlobalTheory.Mem.Chr.OverP D.host q v) : vl D v x = 0 := by
  have hk : ∀ k : ℕ, vl D v x ≤ vl D v (q : AE D) ^ k := fun k => by
    obtain ⟨m, -, hm, s, hs, e⟩ := h k
    have h1 := vl_nat_eq_one hm hv
    rw [← one_mul (vl D v x), ← h1, ← map_mul, e, map_mul, map_pow]
    exact mul_le_of_le_one_right' (vl_le hs v)
  by_contra h0
  obtain ⟨k, hk'⟩ := exists_pow_lt₀ (val_nat_lt hv) (Units.mk0 _ h0)
  exact lt_irrefl _ ((hk k).trans_lt hk')

theorem unr_kill : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), (∀ P : HeightOneSpectrum (𝓞 D.host.E), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → χ.UnrAt P) → ∀ u : (AE D)ˣ, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D u) = 1 := by
  intro D χ hχ u hu hz
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E χ.1 χ.2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) ?_
  intro P x hx
  obtain ⟨q, hq, hqP⟩ := exists_prime_mem P
  by_cases hI : InertQ D q
  · have hunr := hχ P ⟨q, hq, hI, hqP⟩
    refine hunr x ?_
    show Valued.v (x : P.adicCompletion D.host.E) = 1
    rw [hx]
    exact finIdl_unit hu P
  · have h0 := vl_eq_zero_of_zeroAt (hz q hq hI) (v := P) hqP
    rw [← vl_sub_one, map_eq_zero, sub_eq_zero, ← hx] at h0
    have hx1 : x = 1 := Units.ext h0
    rw [hx1, map_one]
    exact map_one _

end GlobalTheory.UnrKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HTensSplitPair

theorem hTens_split_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = 0 → u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k, ∑ l, (-(JA.map τ * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) * (JB.map τ)ᵀ)) k l * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) k l := by
  first
  | exact @_root_.GlobalTheory.FourSumComposition.main
  | exact _root_.GlobalTheory.FourSumComposition.main
  | (apply _root_.GlobalTheory.FourSumComposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FourSumComposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FourSumComposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FourSumComposition.main ..)

end GlobalTheory.HTensSplitPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelCompatibilitiesStandardKernelDataTrueColum
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColRows

theorem kerTies_of_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), ColIn.JetsIn I → I.StdKer l Z t → HEq W B.wts → (I.rec7 l Z).s.Del = (Del : ℚ) → L.etaSz = ((I.rec7 l Z).R.m : ℝ) * (h0 : ℝ) → (t.cst (I.rec7 l Z).what₂.mu0).sharp = true → GlobalTheory.ColRows.KerTies t W Del h0 := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hJ hS hW hDel hEta hSharp
  obtain ⟨hAn, hMu, hM2⟩ := _root_.GlobalTheory.ColRows.analyticTie_of_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t hJ hS
  exact
    { host := _root_.GlobalTheory.ColRows.hostTie_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS
      wts := _root_.GlobalTheory.ColRows.weightTie_of_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW hDel hEta
      chr := _root_.GlobalTheory.ColRows.charTie_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t W Del h0 hS hW
      an := hAn
      mu0 := hMu
      sharp := hSharp
      m2 := hM2
      fld := fun u => _root_.GlobalTheory.ColRows.fieldOfDefinition_of_stdKer I hOk hP l Z L hT Gi Gl K Y cX ex t W hJ hS hW u _ }

end GlobalTheory.ColRows
end

