module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InducedProductCommutesFamilyProduct
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ProdReorder
section SlopeTestRemainingChoices
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_single_equiv {dτ : Fin 1 → ℕ} (τ : ∀ a, Irr k (dτ a)) (e : (Σ a, Fin (dτ a)) ≃ Fin (dτ 0)) :
    Nonempty ((multiProd e fun a => (τ a).π).Equiv (τ 0).π) := by
  have A := multiProd_head (k := k) (fun a => (τ a).π) e (by simp : dτ 0 + 0 = dτ 0)
          (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin (dτ a.succ)) (Fin 0))
  have B := ind₂_unit_right (k := k) (by simp : dτ 0 + 0 = dτ 0) (τ 0).π (τ 0).smooth (fun a : Fin 0 => (τ a.succ).π) (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin (dτ a.succ)) (Fin 0))
  exact A.elim fun a => B.elim fun b => ⟨a.trans b⟩

theorem commutes_multiProd_single {p : ℕ} (x : Irr k p) {dτ : Fin 1 → ℕ} (τ : ∀ a, Irr k (dτ a)) (hc : Commutes x (τ 0)) (N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin (dτ 0)) (h₁ : p + dτ 0 = N) (h₂ : dτ 0 + p = N) : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  have M := multiProd_single_equiv τ e
  have s1 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₁) (extTensor x.π (τ 0).π))) := ind₂_congr h₁ (eqv_refl _) M
  have s2 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (τ 0).π)).Equiv (ind₂ (stdSum h₂) (extTensor (τ 0).π x.π))) := hc N h₁ h₂
  have s3 : Nonempty ((ind₂ (stdSum h₂) (extTensor (τ 0).π x.π)).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := ind₂_congr h₂ (eqv_symm M) (eqv_refl _)
  exact s1.elim fun a => s2.elim fun b => s3.elim fun c => ⟨(a.trans b).trans c⟩

theorem commutes_ind₂_of_head {p d T' T N : ℕ} (x : Irr k p) (y : Irr k d) {W : Type} [AddCommGroup W] [Module ℂ W]
    (R : Representation ℂ (GL (Fin T') k) W) (sR : IsSmooth R) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (P : Representation ℂ (GL (Fin T) k) Y) (h : d + T' = T) (H : Nonempty (P.Equiv (ind₂ (stdSum h) (extTensor y.π R))))
    (hc : Commutes x y)
    (IH : ∀ M (g₁ : p + T' = M) (g₂ : T' + p = M),
      Nonempty ((ind₂ (stdSum g₁) (extTensor x.π R)).Equiv (ind₂ (stdSum g₂) (extTensor R x.π))))
    (h₁ : p + T = N) (h₂ : T + p = N) :
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π P)).Equiv (ind₂ (stdSum h₂) (extTensor P x.π))) := by
  have hA2 : (p + d) + T' = N := by omega
  have hB1 : d + p = p + d := Nat.add_comm _ _
  have h₄ : d + (p + T') = N := by omega
  have hD : T' + p = p + T' := Nat.add_comm _ _
  have s1 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π P)).Equiv
      (ind₂ (stdSum h₁) (extTensor x.π (ind₂ (stdSum h) (extTensor y.π R))))) :=
    ind₂_congr h₁ (eqv_refl x.π) H
  have s2 : Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (ind₂ (stdSum h) (extTensor y.π R)))).Equiv
      (ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum (rfl : p + d = p + d)) (extTensor x.π y.π)) R))) :=
    (ind₂_assoc' (k := k) rfl hA2 h h₁ x.π y.π R x.smooth y.smooth sR).elim fun a => ⟨a.symm⟩
  have s3 : Nonempty ((ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum (rfl : p + d = p + d)) (extTensor x.π y.π)) R)).Equiv
      (ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum hB1) (extTensor y.π x.π)) R))) :=
    ind₂_congr hA2 (hc (p + d) rfl hB1) (eqv_refl R)
  have s4 : Nonempty ((ind₂ (stdSum hA2) (extTensor (ind₂ (stdSum hB1) (extTensor y.π x.π)) R)).Equiv
      (ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum (rfl : p + T' = p + T')) (extTensor x.π R))))) :=
    ind₂_assoc' (k := k) hB1 hA2 rfl h₄ y.π x.π R y.smooth x.smooth sR
  have s5 : Nonempty ((ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum (rfl : p + T' = p + T')) (extTensor x.π R)))).Equiv
      (ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum hD) (extTensor R x.π))))) :=
    ind₂_congr h₄ (eqv_refl y.π) (IH _ rfl hD)
  have s6 : Nonempty ((ind₂ (stdSum h₄) (extTensor y.π (ind₂ (stdSum hD) (extTensor R x.π)))).Equiv
      (ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h) (extTensor y.π R)) x.π))) :=
    (ind₂_assoc' (k := k) h h₂ hD h₄ y.π R x.π y.smooth sR x.smooth).elim fun a => ⟨a.symm⟩
  have s7 : Nonempty ((ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h) (extTensor y.π R)) x.π)).Equiv
      (ind₂ (stdSum h₂) (extTensor P x.π))) :=
    ind₂_congr h₂ (H.elim fun a => ⟨a.symm⟩) (eqv_refl x.π)
  exact s1.elim fun a1 => s2.elim fun a2 => s3.elim fun a3 => s4.elim fun a4 => s5.elim fun a5 =>
    s6.elim fun a6 => s7.elim fun a7 => ⟨a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7)))))⟩

end SlopeTestRemainingChoices

section Succ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem commutes_multiProd_succ {p s : ℕ} (x : Irr k p)
    (ih : ∀ (dτ : Fin s → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))))
    (dτ : Fin (s + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)) (hc : ∀ a, Commutes x (τ a)) (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N) :
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  have key : ∀ (S : ℕ) (e' : (Σ a : Fin s, Fin (dτ a.succ)) ≃ Fin S) (h : dτ 0 + S = T),
      Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
    intro S e' h
    have H := multiProd_head (k := k) (fun a => (τ a).π) e h e'
    have sR : IsSmooth (multiProd e' fun a : Fin s => (τ a.succ).π) :=
      GlobalTheory.SmGL.isSmooth_parInd e' (piTensor fun a : Fin s => (τ a.succ).π)
    exact commutes_ind₂_of_head x (τ 0) _ sR _ h H (hc 0)
      (fun M g₁ g₂ => ih (fun a => dτ a.succ) (fun a => τ a.succ) (fun a => hc a.succ) _ M e' g₁ g₂) h₁ h₂
  have h : dτ 0 + ∑ a : Fin s, dτ a.succ = T := by
    have := Fintype.card_congr e
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    rw [← this]
    exact (Fin.sum_univ_succ _).symm
  exact key _ (finSigmaFinEquiv (n := fun a : Fin s => dτ a.succ)) h
end Succ

theorem commutes_multiProd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p u : ℕ) (x : Irr k p) (dτ : Fin (u + 1) → ℕ) (τ : ∀ a, Irr k (dτ a)), (∀ a, Commutes x (τ a)) → ∀ (T N : ℕ) (e : (Σ a, Fin (dτ a)) ≃ Fin T) (h₁ : p + T = N) (h₂ : T + p = N), Nonempty ((ind₂ (stdSum h₁) (extTensor x.π (multiProd e fun a => (τ a).π))).Equiv (ind₂ (stdSum h₂) (extTensor (multiProd e fun a => (τ a).π) x.π))) := by
  intro k _ _ _ _ p u x
  induction u with
  | zero =>
    intro dτ τ hc T N e h₁ h₂
    have hT : T = dτ 0 := by
      have := Fintype.card_congr e
      simpa [Fintype.card_sigma] using this.symm
    subst hT
    exact commutes_multiProd_single x τ (hc 0) N e h₁ h₂
  | succ u ih =>
    exact commutes_multiProd_succ x ih

end GlobalTheory.ProdReorder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorPreservesLevelInvariants
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG
noncomputable section

namespace GlobalTheory.InertInvar

open scoped TensorProduct

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)}

theorem compAt_mem_tensInt (x : AL L) (hx : x ∈ ALint L) :
    compAt L v x ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      refine ⟨⟨(y : L), y, rfl⟩, ?_⟩
      show _ = compAt L v ((y : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L))
      rw [GlobalTheory.InertUmax.compAt_tmul]
      rfl
    · apply Subring.subset_closure
      right
      refine ⟨⟨a v, ha v⟩, ?_⟩
      show _ = compAt L v ((1 : L) ⊗ₜ[maximalRealSubfield L] a)
      rw [GlobalTheory.InertUmax.compAt_tmul]
  exact key hx

theorem loc_entries_int (Dv : InertDatum L n v w) (z : GAf L n) (hz : z ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈
      intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hm : ∀ k l, ((Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (z : GL (Fin n) (AL L))) : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) (w.adicCompletion L)) k l ∈ intL (w.adicCompletion L) := by
    intro k l
    have hzk : ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := hz k l
    exact (Dv.integ _).1 (compAt_mem_tensInt (v := v) _ hzk)
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hm l k)) (hP k j)

theorem compAt_conjAL (x : AL L) :
    compAt L v (conjAL L x) =
      Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) (compAt L v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [conjAL, compAt, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem loc_mem_GU (Dv : InertDatum L n v w) (z : GAf L n) : Dv.loc z ∈ Formalism.UG.GU Dv.σw n := by
  set φ : AL L →+* w.adicCompletion L :=
    (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L).comp
      (compAt L v) with hφ
  set Y : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map φ with hY
  have hφc : ∀ x, φ (conjAL L x) = Dv.σw (φ x) := by
    intro x
    simp only [hφ, RingHom.comp_apply, compAt_conjAL]
    exact Dv.comm _
  have hz : ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      conjT (conjAL L) ((z.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := z.2
  have hYY : Y * Formalism.UG.cT Dv.σw Y = 1 := by
    have := congrArg (fun M => M.map φ) hz
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero φ) (map_one φ)] at this
    rw [← this]
    congr 1
    ext i j
    simp [Formalism.UG.cT, conjT, hY, hφc]
  have hYY' : Formalism.UG.cT Dv.σw Y * Y = 1 := mul_eq_one_comm.1 hYY
  set P : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L))
  set Pi : Matrix (Fin n) (Fin n) (w.adicCompletion L) :=
    ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L))
  have hPPi : P * Pi = 1 := by simp [P, Pi]
  have hPi : Formalism.UG.cT Dv.σw Pi * Formalism.UG.cT Dv.σw P = 1 := by
    rw [← Formalism.UG.cT_mul, hPPi, Formalism.UG.cT_one]
  have hloc : ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      Pi * Y * P := rfl
  show Formalism.UG.cT Dv.σw ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) *
      Formalism.UG.antiJ (w.adicCompletion L) n * ((Dv.loc z : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) _) =
    Formalism.UG.antiJ (w.adicCompletion L) n
  rw [hloc, ← Dv.Panti, Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  change Formalism.UG.cT Dv.σw P * (Formalism.UG.cT Dv.σw Y * Formalism.UG.cT Dv.σw Pi) * (Formalism.UG.cT Dv.σw P * P) * (Pi * Y * P) =
    Formalism.UG.cT Dv.σw P * P
  calc Formalism.UG.cT Dv.σw P * (Formalism.UG.cT Dv.σw Y * Formalism.UG.cT Dv.σw Pi) * (Formalism.UG.cT Dv.σw P * P) * (Pi * Y * P)
      = Formalism.UG.cT Dv.σw P * Formalism.UG.cT Dv.σw Y * (Formalism.UG.cT Dv.σw Pi * Formalism.UG.cT Dv.σw P) * (P * Pi) * Y * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv.σw P * (Formalism.UG.cT Dv.σw Y * Y) * P := by
        rw [hPi, hPPi]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv.σw P * P := by rw [hYY', Matrix.mul_one]

theorem loc_mem_KU (Dv : InertDatum L n v w) (z : GAf L n) (hz : z ∈ Umax L n) :
    (⟨Dv.loc z, loc_mem_GU Dv z⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  apply GlobalTheory.SatInd.DCoset.mem_KU_of_entries
  · intro i j
    exact (Valuation.mem_integer_iff _ _).1 (loc_entries_int Dv z hz i j)
  · intro i j
    have e : (((⟨Dv.loc z, loc_mem_GU Dv z⟩ : Formalism.UG.GU Dv.σw n)⁻¹ : Formalism.UG.GU Dv.σw n) :
        GL (Fin n) (w.adicCompletion L)) = Dv.loc z⁻¹ := by
      show (Dv.loc z)⁻¹ = GlobalTheory.SatInd.CosetFin.locHom Dv z⁻¹
      rw [map_inv]; rfl
    rw [e]
    exact (Valuation.mem_integer_iff _ _).1 (loc_entries_int Dv z⁻¹ (inv_mem hz) i j)

theorem hval_mul_KU (Dv : InertDatum L n v w) (h : Formalism.UG.GU Dv.σw n → ℂ)
    (hbi : IsBiInv (Formalism.UG.KU Dv.σw n) h) (k₁ k₂ : Formalism.UG.GU Dv.σw n)
    (hk₁ : k₁ ∈ Formalism.UG.KU Dv.σw n) (hk₂ : k₂ ∈ Formalism.UG.KU Dv.σw n) (m : GL (Fin n) (w.adicCompletion L)) :
    Dv.hval h ((k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂) = Dv.hval h m := by
  unfold InertDatum.hval
  by_cases hm : m ∈ Formalism.UG.GU Dv.σw n
  · have hm' : (k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂ ∈ Formalism.UG.GU Dv.σw n :=
      mul_mem (mul_mem k₁.2 hm) k₂.2
    rw [dite_eq_left hm', dite_eq_left hm]
    have := hbi ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ ⟨m, hm⟩
    exact this
  · have hm' : (k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂ ∉ Formalism.UG.GU Dv.σw n := by
      intro h'
      apply hm
      have e : m = (k₁⁻¹ : Formalism.UG.GU Dv.σw n) * ((k₁ : GL (Fin n) (w.adicCompletion L)) * m * k₂) *
          (k₂⁻¹ : Formalism.UG.GU Dv.σw n) := by
        simp [mul_assoc]
      rw [e]
      exact mul_mem (mul_mem (k₁⁻¹).2 h') (k₂⁻¹).2
    rw [dite_eq_right hm', dite_eq_right hm]

end GlobalTheory.InertInvar

open GlobalTheory.InertInvar GlobalTheory.SatInd.CosetFin in
theorem GlobalTheory.heckeFunI_rt_invariant : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → (∀ u ∈ U, ∃ a b : GAf L n, u = a * b ∧ a ∈ U ∧ TrivOutside {v} a ∧ b ∈ U ∧ ∀ x : GAf L n, TrivOutside {v} x → x * b = b * x) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W], ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ κ ∈ U, NG.rt L n κ (heckeFunI L n U Dv h f) = heckeFunI L n U Dv h f := by
  intro L _ _ _ n v w Dv U hU hsplit W _ _ h hh f hf κ hκ
  obtain ⟨a, b, rfl, haU, hat, hbU, hbc⟩ := hsplit κ hκ
  have hfr : ∀ r ∈ U, ∀ y, f (y * r) = f y := fun r hr y => congrFun (hf r hr) y
  have haM : a ∈ Umax L n := (hU a hat).1 haU
  have hbi : IsBiInv (KU Dv.σw n) h := hh.1

  have h1 : ∀ g, heckeFunI L n U Dv h f (g * (a * b)) = heckeFunI L n U Dv h f (g * a) := by
    intro g
    unfold heckeFunI
    refine finsum_congr fun c => ?_
    split_ifs with hc
    · congr 1
      have e : g * (a * b) * hc.choose = g * a * hc.choose * b := by
        simp only [mul_assoc]
        rw [← hbc _ hc.choose_spec.2]
      rw [e, hfr b hbU]
    · rfl

  have h2 : ∀ g, heckeFunI L n U Dv h f (g * a) = heckeFunI L n U Dv h f g := by
    intro g
    unfold heckeFunI
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U))
    refine finsum_congr fun c => ?_
    have hac : (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U) c = a • c := rfl
    by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
    · obtain ⟨x0, hx0, hx0t⟩ := id hc
      have hc' : ∃ y : GAf L n, (y : GAf L n ⧸ U) = (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U) c ∧
          TrivOutside {v} y :=
        ⟨a * x0, by rw [hac, ← hx0, MulAction.Quotient.smul_mk, smul_eq_mul], trivOutside_mul hat hx0t⟩
      rw [dite_eq_left hc, dite_eq_left hc']
      set x := hc.choose with hxdef
      set y := hc'.choose with hydef
      have hx := hc.choose_spec
      have hy := hc'.choose_spec
      rw [← hxdef] at hx
      rw [← hydef] at hy
      have hq : ((a * x : GAf L n) : GAf L n ⧸ U) = (y : GAf L n ⧸ U) := by
        rw [hy.1, hac, ← hx.1, MulAction.Quotient.smul_mk, smul_eq_mul]
      have hrU : (a * x)⁻¹ * y ∈ U := QuotientGroup.eq.1 hq
      have hrt : TrivOutside {v} ((a * x)⁻¹ * y) :=
        trivOutside_mul (trivOutside_inv (trivOutside_mul hat hx.2)) hy.2
      have hrM : (a * x)⁻¹ * y ∈ Umax L n := (hU _ hrt).1 hrU
      have hye : y = a * x * ((a * x)⁻¹ * y) := by group
      have hloc : Dv.loc y = Dv.loc a * Dv.loc x * Dv.loc ((a * x)⁻¹ * y) := by
        conv_lhs => rw [hye]
        show locHom Dv _ = locHom Dv a * locHom Dv x * locHom Dv _
        rw [map_mul, map_mul]
      have hfy : f (g * y) = f (g * a * x) := by
        conv_lhs => rw [hye]
        rw [← hfr _ hrU (g * a * x)]
        simp only [mul_assoc]
      rw [hfy, hloc, hval_mul_KU Dv h hbi ⟨Dv.loc a, loc_mem_GU Dv a⟩ ⟨Dv.loc _, loc_mem_GU Dv _⟩
        (loc_mem_KU Dv a haM) (loc_mem_KU Dv _ hrM) (Dv.loc x)]
    · have hc' : ¬ ∃ y : GAf L n, (y : GAf L n ⧸ U) = (MulAction.toPerm a : GAf L n ⧸ U ≃ GAf L n ⧸ U) c ∧
          TrivOutside {v} y := by
        rintro ⟨y, hy1, hy2⟩
        refine hc ⟨a⁻¹ * y, ?_, trivOutside_mul (trivOutside_inv hat) hy2⟩
        have e : ((a⁻¹ * y : GAf L n) : GAf L n ⧸ U) = a⁻¹ • (y : GAf L n ⧸ U) := by
          rw [MulAction.Quotient.smul_mk, smul_eq_mul]
        rw [e, hy1, hac]
        exact inv_smul_smul a c
      rw [dite_eq_right hc, dite_eq_right hc']
  funext g
  show heckeFunI L n U Dv h f (g * (a * b)) = heckeFunI L n U Dv h f g
  rw [h1, h2]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorPreservesRightTranslationStabl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

namespace GlobalTheory.HeckeStab

theorem heckeFunI_mem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (S : Submodule ℂ (GAf L n → W)), (∀ g, ∀ f ∈ S, NG.rt L n g f ∈ S) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), ∀ f ∈ S, heckeFunI L n U Dv h f ∈ S := by
  classical
  intro L _ _ _ n v w Dv U hUv W _ _ S hS h hh f hf
  have hfin : Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧
      Dv.hval h (Dv.loc x) ≠ 0} :=
    _root_.GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv (_root_.GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram) (_root_.GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hUv h hh
  have key : heckeFunI L n U Dv h f = ∑ c ∈ hfin.toFinset,
      (if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        Dv.hval h (Dv.loc hc.choose) else 0) •
      NG.rt L n (if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
        hc.choose else 1) f := by
    funext g
    unfold heckeFunI
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · simp only [dif_pos hc]
        rfl
      · simp only [dif_neg hc, zero_smul]
        rfl
    · intro c hc0
      rw [Function.mem_support] at hc0
      by_cases hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x
      · rw [dif_pos hc] at hc0
        rw [Set.Finite.coe_toFinset]
        refine ⟨hc.choose, hc.choose_spec.1, hc.choose_spec.2, fun h0 => hc0 ?_⟩
        rw [h0, zero_smul]
      · exact absurd (dif_neg hc) hc0
  rw [key]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hS _ f hf)

end GlobalTheory.HeckeStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLocalIntegralOfMemLatticeStabilizer
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

noncomputable section

open TensorProduct

namespace GlobalTheory.InertUmaxInt

variable (L : Type) [Field L] [NumberField L] [IsCMField L]


omit [IsCMField L] in
theorem compAt_mem_tensInt (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {x : AL L}
    (hx : x ∈ ALint L) :
    compAt L v x ∈ tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L))
      (intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, GlobalTheory.InertUmax.compAt_tmul]
      exact Subring.subset_closure (Or.inl ⟨⟨(y : L), y, rfl⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, GlobalTheory.InertUmax.compAt_tmul]
      exact Subring.subset_closure (Or.inr ⟨⟨a v, ha v⟩, rfl⟩)
  exact key hx

end GlobalTheory.InertUmaxInt


open GlobalTheory.InertUmaxInt in
theorem GlobalTheory.InertUmaxInt.loc_integral_of_mem_Umax : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ u : GAf L n, u ∈ Umax L n → ∀ i j, ((Dv.loc u : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j ∈ intL (w.adicCompletion L) := by
  intro L _ _ _ n v w Dv u hu i j
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have he : ∀ k l, Dv.e (compAt L v ((u.1 : Matrix (Fin n) (Fin n) (AL L)) k l)) ∈
      intL (w.adicCompletion L) := fun k l =>
    (Dv.integ _).1 (compAt_mem_tensInt L v (hu k l))
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (he l k)) (hP k j)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleSmoothPullbackPadicRingIso
section
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys

theorem continuous_glMap {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map he
  · have : (fun x : GL (Fin n) ℚ_[g] => ((Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom x)⁻¹ : GL (Fin n) F).val) =
        fun x => (x⁻¹).val.map e := by
      funext x; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map he

theorem irrSm_pullback (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)) :
    IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  set φ := Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom with hφ
  have hsurj : Function.Surjective φ := fun y =>
    ⟨Matrix.GeneralLinearGroup.map (n := Fin n) e.symm.toRingHom y, by
      ext i j; simp [hφ]⟩
  refine ⟨⟨GlobalTheory.SmGL.nontrivial_of_irreducible σ.irr, fun W hW => ?_⟩, fun v => ?_⟩
  · have hW' : ∀ y, ∀ v ∈ W, σ.ρ y v ∈ W := fun y v hv => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact hW x v hv
    haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
    let S : Subrepresentation σ.ρ := ⟨W, fun y v hv => hW' y v hv⟩
    rcases eq_bot_or_eq_top S with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  · exact (σ.smooth v).preimage (continuous_glMap e he n)

end GlobalTheory.SerSys
end

