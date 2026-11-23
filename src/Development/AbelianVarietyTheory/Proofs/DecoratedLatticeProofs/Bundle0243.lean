module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePoint
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.InertFrameLoc

theorem cA_algebraMap_place (D : D7) (ε : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) ε) = algebraMap (AF D.host.F) (AE D) ε := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  show sigR _ _ _ = _
  simp [sigR]

theorem placeIdem_mul {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (a : AE D) : algebraMap (AF D.host.F) (AE D) ε * a = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hα : α = singleFin v 1 := FiniteAdeleRing.ext _ fun u => by
    change evalV D.host.F u α = evalV D.host.F u (singleFin v 1)
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self, h1]
    · rw [evalV_singleFin_ne e, h0 u e]
  have h2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = GlobalTheory.EmbChart.tensAt D.host.E v 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply, hα, Algebra.TensorProduct.one_def, GlobalTheory.EmbChart.tensAt_tmul]
    rfl
  rw [h2, GlobalTheory.EmbChart.tensAt_mul_right, one_mul]

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem pair_mem_intL (S : HSp D) {s : Fin S.rank → D.host.E} (hs : s ∈ L0c D S)
    {z : Fin S.rank → w.adicCompletion D.host.E} (hz : z ∈ latAt w (frameLat S)) :
    ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * z m ∈
      Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_mul, ← map_sum]
    have hX : ∑ k, s k • S.frame k ∈ S.L0 := hs
    have hY : ∑ m, y m • S.frame m ∈ S.L0 := (mem_frameLat S y).1 hy
    have hd : ∑ m, y m • S.frame m ∈ Formalism.HermitianLatticesTheory.dual S.hT S.L0 := by rw [S.baseLattice_isUnimodular]; exact hY
    have h1 := Submodule.mem_iInf _ |>.1 (Submodule.mem_iInf _ |>.1 hd (∑ k, s k • S.frame k)) hX
    rw [Submodule.mem_comap] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    have e : ∑ m, (∑ k, star (s k) * S.gram k m) * y m = algebraMap (𝓞 D.host.E) D.host.E o := by
      rw [ho]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.restrictScalars_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, Formalism.BasicNotions.HSpace.gram, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [starRingEnd_apply, RingHom.id_apply]
      ring
    rw [e]
    rw [GlobalTheory.InertLoc.mem_intL, GlobalTheory.Idele.valued_algebraMap]
    exact HeightOneSpectrum.valuation_le_one w o
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact add_mem hx hy
  | smul c x _ hx =>
    have e : ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * (c • x) m =
        (c : w.adicCompletion D.host.E) * ∑ m, algebraMap D.host.E (w.adicCompletion D.host.E) (∑ k, star (s k) * S.gram k m) * x m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Pi.smul_apply]
      show _ * ((c : w.adicCompletion D.host.E) * x m) = _
      ring
    rw [e]
    exact mul_mem (show Valued.v (c : w.adicCompletion D.host.E) ≤ 1 from c.2) hx

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

def piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_piW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (a : AE D) :
    secW hw h (piW hw h a) = GlobalTheory.EmbChart.tensAt D.host.E v (compFin D.host.F D.host.E v a) := by
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm
    (GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v a))) = _
  rw [RingEquiv.symm_apply_apply]

theorem piW_tmul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
    (m : D.host.E) : piW hw h (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      complMap h (evalV D.host.F v α) * algebraMap D.host.E (w.adicCompletion D.host.E) m := rfl

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem latO_frame_int (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {k : w.adicCompletion D.host.E} {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)}
    {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)} (hk : GlobalTheory.InertLoc.IsGen D w k)
    (haS : IsFrameAt w (frameLat S) aS) (haT : IsFrameAt w (frameLat T) aT) {u : WO S T}
    (hu : u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True)) (i : Fin T.rank) (j : Fin S.rank) :
    (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1)) i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  induction hu using AddSubgroup.closure_induction generalizing i j with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hx
    let c0 := complMap h (evalV D.host.F v α)
    let t' : Fin T.rank → w.adicCompletion D.host.E := fun l => algebraMap D.host.E _ (t l)
    let r : Fin S.rank → w.adicCompletion D.host.E :=
      fun m => algebraMap D.host.E _ (∑ l, star (s l) * S.gram l m)
    have e1 : Matrix.map (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ l, star (s l) * S.gram l j) :
        WO S T) (piW hw h) = (c0 * algebraMap D.host.E _ a) • vecMulVec t' r := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply, piW_tmul, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
        map_mul, map_mul]
      simp only [mul_assoc]
      rfl
    rw [e1, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, smul_smul, Matrix.smul_apply,
      vecMulVec_apply, smul_eq_mul]
    have h1 : c0 ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := complMap_mem h (hα v)
    have h2 : k⁻¹ * algebraMap D.host.E _ a ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := hk.2.2 a ha
    have h3 : ((aT⁻¹).1 *ᵥ t') i ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      refine (haT ((aT⁻¹).1 *ᵥ t')).2 ?_ i
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨t, (mem_frameLat T t).2 ht, rfl⟩
    have h4 : (r ᵥ* aS.1) j ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
      have hcol : (fun m => aS.1 m j) ∈ latAt w (frameLat S) := by
        have := (haS (Pi.single j 1)).1 fun l => by
          by_cases e : l = j
          · subst e; simp
          · simp [e]
        rwa [Matrix.mulVec_single_one] at this
      show ∑ m, r m * aS.1 m j ∈ _
      exact pair_mem_intL S hs hcol
    have e2 : k⁻¹ * (c0 * algebraMap D.host.E (w.adicCompletion D.host.E) a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) =
        c0 * (k⁻¹ * algebraMap D.host.E _ a) * (((aT⁻¹).1 *ᵥ t') i * (r ᵥ* aS.1) j) := by ring
    rw [e2]
    exact mul_mem (mul_mem h1 h2) (mul_mem h3 h4)
  | zero =>
    rw [Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, smul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.add_apply]
    exact add_mem (hx i j) (hy i j)
  | neg x _ hx =>
    rw [Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul, smul_neg, Matrix.neg_apply]
    exact neg_mem (hx i j)

end GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem exists_uPt_of_half : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ e e', IsPrimeIdem w e e' → ∀ u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True), IsHalf e u ∨ IsHalf (cA D e) u → ∃ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) ∧ uPt hw h k aS aT x = u := by
  intro D v w hw h S T k aS aT hk haS haT e e' he u hu hhalf
  obtain ⟨ε, hε, -, -, hee⟩ := GlobalTheory.VacFixInert.inert_data (GlobalTheory.WeilAtPlace.conjPl_eq_of_inert hw h)
  obtain ⟨rfl, -⟩ := hee e e' he
  rw [h] at hε
  have hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
    rcases hhalf with h1 | h1
    · exact h1
    · rwa [cA_algebraMap_place] at h1
  have hent : ∀ i j, secW hw h (piW hw h (u i j)) = u i j := fun i j => by
    rw [secW_piW, ← placeIdem_mul hε, hh i j]
  refine ⟨k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1), fun i j => latO_frame_int hw h hk haS haT hu i j, ?_⟩
  have e1 : k • ((aT.1 * (k⁻¹ • ((aT⁻¹).1 * u.map (piW hw h) * aS.1))) * (aS⁻¹).1) = u.map (piW hw h) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hk.1, one_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  ext i j
  rw [uPt, e1, Matrix.map_apply, Matrix.map_apply, hent]

end GlobalTheory.InertFrameLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeFrameLiftingSpanningVectorsMod
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftFrameMod

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

theorem det_one_sub_smul (c : R) (X : Matrix (Fin n) (Fin n) R) :
    ∃ a : R, (1 - c • X).det = 1 - c * a := by
  have h : Ideal.Quotient.mk (Ideal.span {c}) (1 - c • X).det = 1 := by
    rw [RingHom.map_det]
    have : (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix (1 - c • X) = 1 := by
      ext i j
      simp [Matrix.one_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c)]
    rw [this, Matrix.det_one]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {c})), Ideal.Quotient.eq] at h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨-a, by linear_combination -ha⟩

theorem isUnit_mix {e g : R} (he : e * e = e) (hu : ∀ a : R, IsUnit (1 - e * g * a))
    (M C X : Matrix (Fin n) (Fin n) R) (h : M * C = 1 - g • X) :
    IsUnit (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) := by
  have h1 : (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (e • C + (1 - e) • 1) = 1 - (e * g) • X := by
    rw [GlobalTheory.IdemSupport.mix_mul he, h, Matrix.one_mul, smul_sub, smul_smul, sub_add_eq_add_sub,
      GlobalTheory.IdemSupport.mix_self]
  obtain ⟨a, ha⟩ := det_one_sub_smul (e * g) X
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, ha] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ hu a : IsUnit _)

theorem exists_lift {A : Type} [CommRing A] (S : Subring A) (g : ℕ) {e t : S} (he : e * e = e) (ht : 1 - e = g * t)
    (hu : ∀ a : S, IsUnit (1 - e * g * a)) (Λ : Submodule S (Fin n → A)) (β₀ : GL (Fin n) A)
    (hβ : ∀ x, x ∈ Λ ↔ ∀ i, ((β₀⁻¹).val *ᵥ x) i ∈ S) (b : Fin n → Fin n → A) (hb : ∀ j, b j ∈ Λ)
    (hs : ∀ y ∈ Λ, y ∈ Submodule.span S (Set.range b) ⊔ Submodule.span S {y | ∃ x ∈ Λ, y = (g : A) • x}) :
    ∃ β : GL (Fin n) A, (∀ x, x ∈ Λ ↔ ∀ i, ((β⁻¹).val *ᵥ x) i ∈ S) ∧
      ∀ j, ∃ x ∈ Λ, (fun i => β.val i j) - b j = (g : A) • x := by
  have hback : ∀ v : Fin n → A, (β₀⁻¹).val *ᵥ (β₀.val *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have hback' : ∀ v : Fin n → A, β₀.val *ᵥ ((β₀⁻¹).val *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hint : ∀ v : Fin n → S, β₀.val *ᵥ (fun i => (v i : A)) ∈ Λ := fun v => (hβ _).2 fun i => by
    rw [hback]; exact (v i).2
  let M : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨((β₀⁻¹).val *ᵥ b j) i, (hβ _).1 (hb j) i⟩
  have hg : ∀ z ∈ Submodule.span S {y | ∃ x ∈ Λ, y = (g : A) • x}, ∃ x ∈ Λ, z = (g : A) • x := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, add_mem hx hy, (smul_add _ _ _).symm⟩
    | smul a x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact ⟨a • x, Λ.smul_mem a hx, smul_comm _ _ _⟩
  have hcol : ∀ k : Fin n, ∃ c r : Fin n → S, ∀ i, (M *ᵥ c) i = (1 : Matrix (Fin n) (Fin n) S) i k - g * r i := by
    intro k
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hs _ (hint fun i => (1 : Matrix (Fin n) (Fin n) S) i k))
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hy
    obtain ⟨x, hx, rfl⟩ := hg z hz
    refine ⟨c, fun i => ⟨_, (hβ x).1 hx i⟩, fun i => Subtype.ext ?_⟩
    have h1 := congrArg (fun v => ((β₀⁻¹).val *ᵥ v) i) hyz
    simp only [hback, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_sum,
      Finset.sum_apply] at h1
    have h2 : (((M *ᵥ c) i : S) : A) = ∑ j, c j • ((β₀⁻¹).val *ᵥ b j) i := by
      change S.subtype (∑ j, M i j * c j) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h2, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast, ← h1, add_sub_cancel_right]
  choose c r hcr using hcol
  obtain ⟨U, hU⟩ := isUnit_mix he hu M (Matrix.of fun i k => c k i) (Matrix.of fun i k => r k i) (by
    ext i k
    exact congrArg Subtype.val (hcr k i))
  have hmv : ∀ (V : GL (Fin n) S) (v : Fin n → A), (∀ i, v i ∈ S) →
      ∀ i, ((GeneralLinearGroup.map S.subtype V).val *ᵥ v) i ∈ S := fun V v hv i => by
    change ∑ j, (V.val i j : A) * v j ∈ S
    exact sum_mem fun j _ => mul_mem (V.val i j).2 (hv j)
  refine ⟨β₀ * GeneralLinearGroup.map S.subtype U, fun x => ?_, fun j => ?_⟩
  · rw [hβ, _root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec, ← map_inv]
    refine ⟨hmv _ _, fun h => ?_⟩
    have := hmv U _ h
    rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec] at this
  · refine ⟨_, hint fun i => t * ((1 : Matrix (Fin n) (Fin n) S) i j - M i j), ?_⟩
    have h1 : (fun i => (β₀ * GeneralLinearGroup.map S.subtype U).val i j) =
        β₀.val *ᵥ fun i => (U.val i j : A) := rfl
    rw [h1, ← hback' (b j), ← mulVec_sub, ← mulVec_smul]
    congr 1
    funext i
    have h2 : U.val i j - M i j = g * (t * ((1 : Matrix (Fin n) (Fin n) S) i j - M i j)) := by
      rw [hU, ← mul_assoc, ← ht]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have h3 := congrArg Subtype.val h2
    rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast] at h3
    exact h3

end Alg

open GlobalTheory.StdFrames GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

theorem valued_natCast_lt_one_iff {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : Q.adicCompletion E) < 1 ↔ (N : 𝓞 E) ∈ Q.asIdeal := by
  rw [← Q.valuation_lt_one_iff_mem (K := E) (N : 𝓞 E), ← Formalism.UG.P.levelaf_valued_algebraMap]
  simp

theorem exists_inv_of_valued {D : D7} (z : Ef D) (h : ∀ Q : Pl D.host.E, Valued.v (cpt Q z) = 1) :
    ∃ y ∈ OA D, z * y = 1 := by
  have hi : ∀ Q : Pl D.host.E, (cpt Q z)⁻¹ ∈ Q.adicCompletionIntegers D.host.E := fun Q => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]
  obtain ⟨y, hy⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
    (⟨fun Q => (cpt Q z)⁻¹, Filter.Eventually.of_forall hi⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  have h1 : ∀ Q : Pl D.host.E, cpt Q y = (cpt Q z)⁻¹ := fun Q => by
    change toAd D y Q = _
    rw [hy]
    rfl
  refine ⟨y, (mem_OA_iff y).2 fun Q => h1 Q ▸ hi Q, cpt_ext fun Q => ?_⟩
  rw [RingHom.map_mul, RingHom.map_one, h1, mul_inv_cancel₀]
  intro h0
  have := h Q
  rw [h0, Valuation.map_zero] at this
  exact zero_ne_one this

theorem coe_one_sub {A : Type} [CommRing A] (S : Subring A) (g : ℕ) (e a : S) :
    ((1 - e * g * a : S) : A) = 1 - e * g * a := by
  push_cast
  rfl

theorem one_sub_eq {A : Type} [CommRing A] (S : Subring A) {g : ℕ} {c e : A} (hc : (g : A) * c = 1) (he : e ∈ S)
    (ht : c * (1 - e) ∈ S) : (1 - ⟨e, he⟩ : S) = g * ⟨_, ht⟩ := by
  refine Subtype.ext ?_
  push_cast
  rw [← mul_assoc, hc, one_mul]

section Val

variable {A K Γ : Type} [CommRing A] [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (φ : A →+* K)

theorem val_quot_le {g : ℕ} {c e : A} (hc : (g : A) * c = 1) (h : φ e = 1 ∨ φ e = 0 ∧ v (g : K) = 1) :
    v (φ (c * (1 - e))) ≤ 1 := by
  rcases h with h | ⟨h, h1⟩
  · simp [h]
  · have h2 := congrArg (fun x => v (φ x)) hc
    simp only [map_mul, map_natCast, map_one, h1, one_mul] at h2
    simp [h, h2]

theorem val_one_sub {g : ℕ} {a e : A} (ha : v (φ a) ≤ 1) (h : φ e = 1 ∧ v (g : K) < 1 ∨ φ e = 0) :
    v (φ (1 - e * g * a)) = 1 := by
  rcases h with ⟨h, h1⟩ | h
  · rw [map_sub, map_one, map_mul, map_mul, map_natCast, h, one_mul]
    refine Valuation.map_one_sub_of_lt _ ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' ha).trans_lt h1
  · simp [h]

end Val

theorem quot_mem {D : D7} {g : ℕ} {c e : Ef D} (hc : (g : Ef D) * c = 1)
    (he1 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∈ Q.asIdeal → cpt Q e = 1)
    (he0 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q e = 0) : c * (1 - e) ∈ OA D :=
  (mem_OA_iff _).2 fun Q => by
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (val_quot_le Valued.v (cpt Q) hc ?_)
    by_cases hQ : (g : 𝓞 D.host.E) ∈ Q.asIdeal
    · exact Or.inl (he1 Q hQ)
    · exact Or.inr ⟨he0 Q hQ, le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
        (natCast_mem (Q.adicCompletionIntegers D.host.E) g))
        (not_lt.1 fun h => hQ ((valued_natCast_lt_one_iff Q g).1 h))⟩

theorem valued_one_sub {D : D7} {g : ℕ} {a e : Ef D} (ha : a ∈ OA D)
    (he1 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∈ Q.asIdeal → cpt Q e = 1)
    (he0 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q e = 0) (Q : Pl D.host.E) :
    Valued.v (cpt Q (1 - e * g * a)) = 1 := by
  refine val_one_sub Valued.v (cpt Q)
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((mem_OA_iff _).1 ha Q)) ?_
  by_cases hQ : (g : 𝓞 D.host.E) ∈ Q.asIdeal
  · exact Or.inl ⟨he1 Q hQ, (valued_natCast_lt_one_iff Q g).2 hQ⟩
  · exact Or.inr (he0 Q hQ)

theorem exists_idem_over (D : D7) {g : ℕ} (hg : g ≠ 0) :
    ∃ e c : Ef D, e * e = e ∧ e ∈ OA D ∧ (g : Ef D) * c = 1 ∧ c * (1 - e) ∈ OA D ∧
      ∀ a ∈ OA D, ∃ y ∈ OA D, (1 - e * g * a) * y = 1 := by
  obtain ⟨e, he, heO, he1, he0⟩ := exists_idem {Q : Pl D.host.E | (g : 𝓞 D.host.E) ∈ Q.asIdeal}
  obtain ⟨c, hc⟩ : ∃ c : Ef D, (g : Ef D) * c = 1 := by
    refine ⟨algebraMap D.host.E (Ef D) (g : D.host.E)⁻¹, ?_⟩
    rw [← map_natCast (algebraMap D.host.E (Ef D)), ← RingHom.map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hg),
      RingHom.map_one]
  exact ⟨e, c, he, heO, hc, quot_mem hc he1 he0, fun a ha => exists_inv_of_valued _ (valued_one_sub ha he1 he0)⟩

theorem idem_subring {A : Type} [CommRing A] (S : Subring A) {g : ℕ}
    (h : ∃ e c : A, e * e = e ∧ e ∈ S ∧ (g : A) * c = 1 ∧ c * (1 - e) ∈ S ∧
      ∀ a ∈ S, ∃ y ∈ S, (1 - e * g * a) * y = 1) :
    ∃ e t : S, e * e = e ∧ 1 - e = g * t ∧ ∀ a : S, IsUnit (1 - e * g * a) := by
  obtain ⟨e, c, he, heS, hc, ht, hu⟩ := h
  refine ⟨⟨e, heS⟩, ⟨_, ht⟩, Subtype.ext he, one_sub_eq S hc heS ht, fun a => ?_⟩
  obtain ⟨y, hy, h⟩ := hu a a.2
  refine IsUnit.of_mul_eq_one ⟨y, hy⟩ (Subtype.ext ?_)
  rw [MulMemClass.coe_mul, coe_one_sub]
  exact h

theorem hatL_eq_Lf (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => ⟨⟨y, hy⟩, h⟩, fun ⟨y, h⟩ => ⟨y.1, y.2, h⟩⟩

theorem exists_isLiftFrame : ∀ (D : D7) (g : ℕ), g ≠ 0 → ∀ b : ℕ → VA (instOf D), (∀ j, b j ∈ (instOf D).Lf) →
    (∀ y ∈ (instOf D).Lf, InMod (instOf D) g (Set.range fun j : Fin (instOf D).n => b j.val) y) →
    ∃ β, IsLiftFrame (instOf D) g b β := by
  intro D g hg b hb hs
  obtain ⟨e, t, he, ht, hu⟩ := idem_subring (IntAf (instOf D).F (instOf D).E) (g := g) (exists_idem_over D hg)
  generalize instOf D = I at *
  letI : Submodule.IsLattice I.E I.L := Submodule.IsLattice.of_fg I.E I.L_fg
  obtain ⟨β₀, h₀⟩ := GlobalTheory.latticeFrame.exists_frame I.F I.E I.n I.L ⟨I.L_span⟩
  obtain ⟨β, h1, h2⟩ := exists_lift (IntAf I.F I.E) g he ht hu I.Lf β₀ (fun x => hatL_eq_Lf I ▸ h₀ x)
    (fun j => b j.val) (fun j => hb j.val) hs
  exact ⟨β, fun x => (hatL_eq_Lf I).symm ▸ h1 x, fun j => Submodule.subset_span (h2 j)⟩

end GlobalTheory.LiftFrameMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairPosition
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSlot

theorem resS_sigInt_eq_zero_iff (D : D7) (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP (sigInt (instOf D) s) = 0 ↔ resS D.host.F (conjPl PP) s = 0 :=
  resS_sigS_eq_zero_iff (instOf D).cm (isConjPl_conjPl PP).symm s

theorem mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (PP : Pl E) (a : 𝓞 E) :
    a ∈ (conjPl PP).asIdeal ↔ starO a ∈ PP.asIdeal := Iff.rfl

theorem natCast_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (PP : Pl E) (N : ℕ) :
    (N : 𝓞 E) ∈ (conjPl PP).asIdeal ↔ (N : 𝓞 E) ∈ PP.asIdeal := by
  show starOHom (N : 𝓞 E) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem isConjPl_conjPl_lev (D : D7) (PP : Pl D.host.E) : Formalism.IndefR.Lev.IsConjPl (D := D) PP (conjPl PP) :=
  fun c hc => ⟨starO c, by rw [mem_conjPl, starO_starO]; exact hc, rfl⟩

theorem intersection_update_fsHerm_neg_one : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ R : Formalism.L2.Herm.intAf D.host.F D.host.E → Prop, (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ R s) → ∀ PP ∈ Pg, (∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, (PP' ≠ PP → resS D.host.F PP' s = 0) ∧ resS D.host.F PP' (sigInt (instOf D) s) = 0) ∧ R s) ∧ ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, resS D.host.F PP' s = 0 ∧ (PP' ≠ PP → resS D.host.F PP' (sigInt (instOf D) s) = 0)) ∧ R s := by
  intro D Pg hg hconj R hR PP hPP
  have hne : ∀ P ∈ Pg, ∀ P' ∈ Pg, conjPl P ≠ P' := fun P hP P' hP' h =>
    hconj P hP P' hP' (h ▸ isConjPl_conjPl_lev D P)
  constructor
  · obtain ⟨s, hs, hRs⟩ := hR PP (hg PP hPP)
    refine ⟨s, fun P hP => ⟨fun h => hs P (hg P hP) h, ?_⟩, hRs⟩
    rw [resS_sigInt_eq_zero_iff]
    exact hs _ ((natCast_mem_conjPl P _).2 (hg P hP)) (hne P hP PP hPP)
  · obtain ⟨s, hs, hRs⟩ := hR (conjPl PP) ((natCast_mem_conjPl PP _).2 (hg PP hPP))
    refine ⟨s, fun P hP => ⟨hs P (hg P hP) (hne PP hPP P hP).symm, fun h => ?_⟩, hRs⟩
    rw [resS_sigInt_eq_zero_iff]
    refine hs _ ((natCast_mem_conjPl P _).2 (hg P hP)) fun e => h ?_
    rw [← conjPl_conjPl P, e, conjPl_conjPl]

end GlobalTheory.ConjSlot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralTwistPrimeEqDeepFiniteSumStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → SumAgree Ch sel mu cst σ₀ P ι s W ν := by
  first | exact @GlobalTheory.TwSumAgree.sumAgree | exact GlobalTheory.TwSumAgree.sumAgree | (intros; apply GlobalTheory.TwSumAgree.sumAgree <;> assumption)
end

