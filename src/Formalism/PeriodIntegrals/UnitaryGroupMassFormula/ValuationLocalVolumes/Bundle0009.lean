module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IsCompactSpanRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TrOntoHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualContinuity.SdExistsHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0007

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CoordComb
section
noncomputable section

namespace PI.OmVg

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmLocU.Red
  Topology Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_pow_mem {ϖ : Fv F v} (hϖ : IsUnif v ϖ) {a : ℕ} (c : Fin a → Fv F v ⊗[F] E) :
    ∃ m : ℕ, ∀ i, sc (E := E) v (ϖ ^ m) * c i ∈ OEv (E := E) v := by
  obtain ⟨-, hπ, -⟩ := unif_spec v ϖ hϖ
  have hN : OEv (E := E) v ∈ 𝓝 (0 : Fv F v ⊗[F] E) := (isOpen_oEv v).mem_nhds (Orb.oev_zero v)
  obtain ⟨m, hm⟩ := PI.VolStabSW.eventually_smul_sub (Set.range c) (Set.finite_range c).isCompact
    (fun k => ϖ ^ k) hπ _ hN
  exact ⟨m, fun i => by rw [← smul_eq_sc]; exact hm _ ⟨i, rfl⟩⟩

variable (hSD : IsSDLoc σ J v Λ) {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e)
  (he1 : gramR (Fv F v) σ J e = 1)

theorem coord_comb {K : Type} [CommRing K] (π : OR (E := E) v →+* K) {a : ℕ} (x : lamA v Λ a)
    (d : Fin a → OR (E := E) v) (p : Fin n)
    (hw : hR (Fv F v) σ J (e p) (∑ i, (d i : Fv F v ⊗[F] E) • (x : TupV (E := E) v n a) i) ∈ OR (E := E) v) :
    π ⟨_, hw⟩ = ∑ i, π (d i) * phi σ J v Λ hSD he π a x i p := by
  have e1 : (⟨_, hw⟩ : OR (E := E) v) = ∑ i, d i * cf σ J v Λ hSD he x i p := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, cf_coe]
    rw [Orb.hR_sum_right σ J v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum]
  simp only [map_mul, phi_apply]


include he1 in
theorem ker_vec {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K}
    (hπ : IsRes σ v ϖ τ π) {w : Fin n → Fv F v ⊗[F] E} (hw : w ∈ latLoc (E := E) v Λ)
    (h0 : ∀ p, π ⟨hR (Fv F v) σ J (e p) w, (hSD _).1 hw _ (bas_mem v Λ he p)⟩ = 0) :
    ∃ w' ∈ latLoc (E := E) v Λ, w = sc (E := E) v ϖ • w' := by
  have hP : ∀ p, ∃ d ∈ OEv (E := E) v, hR (Fv F v) σ J (e p) w = sc (E := E) v ϖ * d :=
    fun p => (hπ.2.1 _).1 (h0 p)
  choose d hd hde using hP
  refine ⟨∑ p, d p • e p, (he _).2 ⟨d, hd, rfl⟩, ?_⟩
  rw [expand σ J v Λ he he1 hw, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hde, smul_smul]

end PI.OmVg
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertB
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
  PI.VolStabSW
open scoped TensorProduct

def CorOne {R : Type} [CommRing R] {a : ℕ} (T : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ i₀ : Fin a, (∀ j, T i₀ j = 0) ∧ (∀ j, T j i₀ = 0) ∧ IsUnit (T + Matrix.single i₀ i₀ 1).det

def FFInertB : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → CorOne T →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T ∧ LinearIndependent K X} : ℝ) =
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
        ∏ j ∈ Finset.Icc (M - a) M, (1 - (-1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))

def FFSplitB : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → CorOne T →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T ∧ LinearIndependent (k × k) X} : ℝ) =
      (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) *
        ∏ j ∈ Finset.Icc (M - a) M, (1 - (1 : ℝ) ^ j * (Nat.card k : ℝ) ^ (-(j : ℤ)))

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def RedP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (J' : Matrix (Fin n) (Fin n) K) (T' : Matrix (Fin a) (Fin a) K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          (∀ i j, σ' (J' j i) = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, σ' (T' j i) = T' i j) ∧ CorOne T' ∧
          Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → K // ffGram (σ' : K →+* K) J' X = T' ∧ LinearIndependent K X}) ∨
       (etaV (E := E) v = 1 ∧ ∃ (J' : Matrix (Fin n) (Fin n) (k × k)) (T' : Matrix (Fin a) (Fin a) (k × k)),
          (∀ i j, (J' j i).swap = J' i j) ∧ IsUnit J'.det ∧ (∀ i j, (T' j i).swap = T' i j) ∧ CorOne T' ∧
          Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) =
            Nat.card {X : Fin a → Fin n → k × k //
              ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J' X = T' ∧ LinearIndependent (k × k) X}))

theorem clsP_of (a : ℕ) (Y : TupV (E := E) v n a) (hR : RedP σ J ψ v Λ a Y) (hI : FFInertB) (hS : FFSplitB) :
    ClsP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have ha : a ≤ n := hG.2.2.2.2.1
  obtain ⟨k, _, _, hk, h⟩ := hR hG ϖ hϖ
  rcases h with ⟨hη, K, _, _, σ', J', T', hσ, h2, hne, hJ, hJu, hT, hTu, hc⟩ |
    ⟨hη, J', T', hJ, hJu, hT, hTu, hc⟩
  · rw [hc, hI k K σ' hσ h2 hne n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEtaB qv
    rw [hη]
    push_cast
    rfl
  · rw [hc, hS k n a ha J' hJ hJu T' hT hTu, hk]
    unfold prodEtaB qv
    rw [hη]
    push_cast
    rfl

end Gen

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FibPOfDual
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PrimDual (a : ℕ) : Prop :=
  StdHyp σ J ψ → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∀ y ∈ PrimT v Λ a, ∃ W ∈ LamT v Λ a, ∀ i j,
      hR (Fv F v) σ J (y i) (W j) = (if i = j then 1 else 0) ∧
        hR (Fv F v) σ J (W j) (y i) = (if i = j then 1 else 0)

def HensOntoP (a : ℕ) : Prop :=
  StdHyp σ J ψ → IsSDLoc σ J v Λ → UnramAt (E := E) v →
    (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    ∀ y ∈ PrimT v Λ a, ∀ S : HermR (Fv F v) σ a, S ∈ hermOE σ v a →
      ∃ W0 ∈ LamT v Λ a, crossM σ J y W0 = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))

theorem henselSurjective_of_primitiveDual (a : ℕ) (hD : PrimDual σ J ψ v Λ a) : HensOntoP σ J ψ v Λ a := by
  classical
  intro hS hSD hUn hL y hy S hS'
  obtain ⟨W, hW, hd⟩ := hD hS hSD hUn hL y hy
  obtain ⟨L, -, hLΛ⟩ := hL
  have hTr : TrOnto σ v := PI.OmLocU.Red.trOnto_holds σ J ψ v hS
  have hdiag : ∀ i, ∃ x ∈ OEv (E := E) v, x + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x = (S : Matrix (Fin a) (Fin a) _) i i :=
    fun i => hTr hUn _ (hS' i i) (S.2 i i)
  choose x hx hxs using hdiag
  set A : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then (S : Matrix (Fin a) (Fin a) _) i j else if i = j then x i else 0 with hAdef
  have hA : ∀ i j, A i j ∈ OEv (E := E) v := by
    intro i j
    simp only [hAdef]
    split_ifs
    · exact hS' i j
    · exact hx i
    · exact oEv_zero v
  have hAS : ∀ i j, A i j + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (A j i) = (S : Matrix (Fin a) (Fin a) _) i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [hAdef, h, not_lt.2 h.le, h.ne']
    · simp [hAdef, hxs]
    · simp only [hAdef, h, not_lt.2 h.le, h.ne, h.ne', if_false, if_true, zero_add]
      exact S.2 i j
  subst hLΛ
  refine ⟨fun j => ∑ k, A k j • W k, fun j => ?_, ?_⟩
  · exact Submodule.sum_mem _ fun k _ => oEv_smul_mem v L (hA k j) (hW k)
  · funext i j
    simp only [crossM]
    rw [hR_sum_smul_right, hR_sum_smul_left]
    have e1 : ∑ k, A k j * hR (Fv F v) σ J (y i) (W k) = A i j := by
      simp only [fun k => (hd i k).1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e2 : ∑ k, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (A k i) * hR (Fv F v) σ J (W k) (y j) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (A j i) := by
      simp only [fun k => (hd j k).2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [e1, e2, hAS]

theorem fiberHensel_of_henselOnto (a : ℕ) (Y : TupV (E := E) v n a) (h : HensOntoP σ J ψ v Λ a) :
    FibHensP σ J ψ v Λ a Y := by
  intro hG ϖ hϖ hσ hJ y hy hyT
  obtain ⟨h0, -, hint⟩ := unif_spec v ϖ hϖ
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  refine ⟨dH σ J v hσ hJ y, fun k => ?_, fun k Z hZ W hW => ?_⟩
  · ext S
    constructor
    · rintro ⟨W, hW, rfl⟩
      obtain ⟨W0, hW0, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hW
      rw [mem_hN σ v ϖ h0]
      intro i j
      refine ⟨crossM σ J y W0 i j, ?_, ?_⟩
      · exact oEv_add v (hR_mem_oEv σ J v Λ hSD (hy.1 i) (hW0 j)) (hR_mem_oEv σ J v Λ hSD (hW0 i) (hy.1 j))
      · rw [coe_dH, crossM_smul_right]
    · intro hS
      obtain ⟨S0, hS0, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hS
      obtain ⟨W0, hW0, hc⟩ := h hG.1 hSD hG.2.2.2.1 hG.2.1 y hy S0 hS0
      refine AddSubgroup.mem_map.2 ⟨ϖ ^ (k + 1) • W0, (PI.VolStabSW.mem_smulSub _ _ _).2 ⟨W0, hW0, rfl⟩, ?_⟩
      apply Subtype.ext
      funext i j
      rw [coe_dH, crossM_smul_right, hc, PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, smul_eq_sc]
  · apply rem_mem σ J v Λ hSD ϖ h0 hint hZ hW
    show gramR (Fv F v) σ J (y + Z + W) - gramR (Fv F v) σ J (y + Z) -
      (gramR (Fv F v) σ J (y + W) - gramR (Fv F v) σ J y - gramR (Fv F v) σ J W) = _
    exact gram_rem σ J y Z W

theorem fibP_of_dual (a : ℕ) (Y : TupV (E := E) v n a) (hC : PrimCos σ J ψ v Λ a) (hD : PrimDual σ J ψ v Λ a) :
    FibP σ J ψ v Λ a Y :=
  fibP_of σ J ψ v Λ a Y hC (fiberHensel_of_henselOnto σ J ψ v Λ a Y (henselSurjective_of_primitiveDual σ J ψ v Λ a hD))

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulERight
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem hR_smulE_right (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_sum_right {ι : Type} (s : Finset ι) (x : Fin n → Fv F v ⊗[F] E) (f : ι → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ i ∈ s, f i) = ∑ i ∈ s, hR (Fv F v) σ J x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hR_zero_right σ J v x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hR_add_right, ih]

theorem oev_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, _, rfl⟩ := hy
      rw [← map_mul]
      exact Submodule.subset_span ⟨a * b, trivial, by simp⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

end Gen

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem lat_oev_smul (v : PlX X) {c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hc : c ∈ OEv (E := X.B.I.E) v)
    {x : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E} (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    c • x ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨o, _, rfl⟩ := hc
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨o • l, X.B.I.L.smul_mem o hl, ?_⟩
      funext i
      simp only [ratV, Pi.smul_apply, smul_eq_mul]
      rw [← map_mul]
      rfl
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
    | smul d x _ h =>
      beta_reduce
      beta_reduce at h
      have e : inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • (d • x) =
          d • (inclR (F := X.B.I.F) (Fv X.B.I.F v) (o : X.B.I.E) • x) := by
        funext i
        change _ * ((d : Fv X.B.I.F v) • x i) = (d : Fv X.B.I.F v) • (_ * x i)
        rw [mul_smul_comm]
      rw [e]; exact Submodule.smul_mem _ d h
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add c c' _ _ h1 h2 => rw [add_smul]; exact Submodule.add_mem _ h1 h2
  | smul d c _ h =>
    have e : (d • c) • x = d • (c • x) := by
      funext i
      change ((d : Fv X.B.I.F v) • c) * x i = (d : Fv X.B.I.F v) • (c * x i)
      rw [smul_mul_assoc]
    rw [e]; exact Submodule.smul_mem _ d h

abbrev zi : Fin (D.R.rS + 1 + D.R.rS) := Fin.castAdd D.R.rS (Fin.last D.R.rS)

theorem gramE_entry (j i : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i = if i = piv D.R.rS j then cD X u' j else 0 := by
  rw [gram_eq, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm]
  by_cases h : i = piv D.R.rS j
  · rw [if_pos h.symm, if_pos h, mul_one]
  · rw [if_neg (fun e => h e.symm), if_neg h, mul_zero]

def OmVMem : Prop := ∀ (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)), yTup X u' v i ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

def OmVZPrim : Prop :=
  ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal → ∀ c : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E,
    c • yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) → c ∈ OEv (E := X.B.I.E) v

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVScaleHolds
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain PI.DegenerateSiegelWeil.Scale PI.NcVal.OmVc2 PI.VolStabSW PI.VolStabSW.TensAllW
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem scl_ne_zero (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : scl X v i ≠ 0 := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [scl, Fin.append_left]; exact OmW.alp_ne_zero v _ _
  · rw [scl, Fin.append_right]; exact inv_ne_zero (OmW.alp_ne_zero v _ _)

theorem scl_piv (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) :
    scl X v (OmW.piv D.R.rS i) = (scl X v i)⁻¹ := by
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) a
    · rw [OmW.pivot_castAdd_last, scl, Fin.append_left, OmW.alp_last, inv_one]
    · rw [OmW.piv_e, scl, Fin.append_left, Fin.append_right]
  · rw [OmW.piv_f, scl, Fin.append_left, Fin.append_right, inv_inv]

def dU (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)ˣ where
  val := sc (E := X.B.I.E) v (scl X v i)
  inv := sc (E := X.B.I.E) v (scl X v i)⁻¹
  val_inv := by
    rw [sc, sc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (scl_ne_zero X v i), one_mul,
      Algebra.TensorProduct.one_def]
  inv_val := by
    rw [sc, sc, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ (scl_ne_zero X v i), one_mul,
      Algebra.TensorProduct.one_def]

theorem dU_piv (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) : dU X v (OmW.piv D.R.rS i) = (dU X v i)⁻¹ := by
  apply Units.ext
  show sc (E := X.B.I.E) v (scl X v (OmW.piv D.R.rS i)) = sc (E := X.B.I.E) v (scl X v i)⁻¹
  rw [scl_piv]

theorem yTup_eq (v : PlX X) :
    yTup X u' v = mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _)
      (ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) := by
  show _ = mulTup (Matrix.diagonal fun i => (dU X v i : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) _
  rw [mulTup_diagonal]
  funext j i
  rfl

theorem gram_ratTup (v : PlX X) :
    gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) = localGramMatrixFrame X u' v := by
  funext a b
  exact OmW.hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J _ a b

theorem act_mulTup {K : Type} [CommRing K] {a M : ℕ} (g : Matrix (Fin M) (Fin M) K) (f : Fin a → K)
    (Y : Fin a → Fin M → K) :
    (fun j => g.mulVec (mulTup (Matrix.diagonal f) Y j)) = mulTup (Matrix.diagonal f) (fun j => g.mulVec (Y j)) := by
  rw [mulTup_diagonal, mulTup_diagonal]
  funext j i
  show g.mulVec (f j • Y j) i = f j * g.mulVec (Y j) i
  rw [Matrix.mulVec_smul]
  rfl

theorem orbit_eq (v : PlX X) :
    {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} =
      mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) ''
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))} := by
  have hc : ∀ k : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J,
      k • yTup X u' v = mulTup ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _)
        (k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))) := by
    intro k
    rw [yTup_eq]
    exact act_mulTup _ _ _
  ext Y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, (hc k).symm⟩
  · rintro ⟨Z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (hc k).symm⟩

theorem omVScale_holds : OmVScale X u' ψ := by
  intro h1 h2 v
  have hS := OmW.omVStd_holds X ψ h1 h2
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := PI.VolStabSW.sigma_invol _ hS.1.2.2.2
  have hJ : ∀ i j, X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j := hS.2.1.1
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [hS.1.2.2.1]; norm_num)
  rw [orbit_eq]
  unfold omAt
  split_ifs with hT
  swap
  · rfl
  unfold omFam
  split_ifs with hfib
  swap
  · rfl
  have := PI.VolStabSW.secondCountable_Fv X.B.I.F v
  have := PI.VolStabSW.locallyCompact_Fv X.B.I.F v
  have : SecondCountableTopology (Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS))
      (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :=
    inferInstanceAs (SecondCountableTopology (Fin (D.R.rS + 1 + D.R.rS) → Fin (D.R.rS + 1 + D.R.rS) →
      Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E))
  have : SecondCountableTopology (HermR (Fv X.B.I.F v) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hEx := PI.SelfDualBridge.W.sdExists_holds X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS) (Fin 1) hS
  have hμ : SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Fv X.B.I.F v) (psiV X.B.I.F ψ v)
      (D.R.rS + 1 + D.R.rS) (dX X.B.I.cm.sig X.B.I.J ψ v (D.R.rS + 1 + D.R.rS)) := by
    unfold dX; rw [dite_eq_left hEx.1]; exact hEx.1.choose_spec
  have hν : SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Fv X.B.I.F v) (psiV X.B.I.F ψ v) (D.R.rS + 1 + D.R.rS)
      (dT X.B.I.cm.sig ψ v (D.R.rS + 1 + D.R.rS)) := by
    unfold dT; rw [dite_eq_left hEx.2.1]; exact hEx.2.1.choose_spec
  have := hμ.1
  have := hν.1
  have hπ : ∀ i, (Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) ((Function.Involutive.toPerm _
      (OmW.piv_invol D.R.rS)) i) = i := fun i => OmW.piv_invol D.R.rS i
  have hd : ∀ i, dU X v ((Function.Involutive.toPerm _ (OmW.piv_invol D.R.rS)) i) = (dU X v i)⁻¹ :=
    fun i => dU_piv X v i
  have hfix : hermMap (Fv X.B.I.F v) X.B.I.cm.sig hσ
      ((diagUnit (dU X v) : (Matrix _ _ _)ˣ) : Matrix _ _ _) ⟨localGramMatrixFrame X u' v, hT⟩ = ⟨localGramMatrixFrame X u' v, hT⟩ := by
    apply Subtype.ext
    rw [hermMap_coe]
    show _ * localGramMatrixFrame X u' v * _ = localGramMatrixFrame X u' v
    have hg := OmW.omVGram_holds X u' v
    rw [yTup_eq, PI.NcVal.OmVc1.gramMulTup_holds _ _ _ _ _ _ _ _ _, gram_ratTup] at hg
    exact hg
  have key := fib_image_mulTup X.B.I.cm.sig hσ X.B.I.J hJ (Fv X.B.I.F v) PI.NcVal.OmVc1.gramMulTup_holds
    (PI.VolStabSW.isOpen_units_Fv X.B.I.F v) (lip_field _) _ _ hfib.choose hfib.choose_spec
    (diagUnit (dU X v)) ⟨localGramMatrixFrame X u' v, hT⟩ hfix
    {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}
  rw [cTup_eq_one (Fv X.B.I.F v) (dU X v) _ hπ hd, cHerm_eq_one X.B.I.cm.sig hσ (Fv X.B.I.F v) (dU X v) _ hπ hd]
    at key
  simp only [ENNReal.coe_one, one_mul] at key
  exact key.symm

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmVc
end
end

