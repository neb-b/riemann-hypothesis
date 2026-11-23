module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix Pointwise Formalism.UG

namespace GlobalTheory.DefiniteDense

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infPt (y : UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E))) : UA E n :=
  ⟨infGL E n y.1, infGL_mem_UA y.1 (by
    have h : cT (starRingEnd (Cinf E)) (y.1 : Matrix (Fin n) (Fin n) (Cinf E)) * 1 * y.1 = 1 := y.2
    rw [mul_one] at h
    exact h)⟩

theorem continuous_infPt : Continuous (infPt (E := E) (n := n)) :=
  (GlobalTheory.DefU.continuous_infGL.comp continuous_subtype_val).subtype_mk _

theorem mem_closure_rat_fin (x : UA E n) (hx : x ∈ infU E n) :
    x ∈ closure ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) := by
  have hne : ∃ z, (IsCMField.complexConj E : E →+* E) z ≠ z := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext h)
  have hd := GlobalTheory.RealApprox.dense_unitary (GlobalTheory.CuspRep.InfType.diagInf E) (IsCMField.complexConj E : E →+* E)
    (starRingEnd (Cinf E)) (fun z => (pInf_complexConj z).symm) (fun z => IsCMField.complexConj_apply_apply E z) hne
    (fun z => star_star z) continuous_star GlobalTheory.CuspRep.InfType.denseRange_diagInf Units.isOpen
    (fun z hz => by obtain ⟨u, rfl⟩ := hz; exact NormedRing.inverse_continuousAt u)
    (1 : Matrix (Fin n) (Fin n) E)
    (by rw [Formalism.UG.cT, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]) (by simp)
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at hd
  have hp : ∀ a : Ad E, pInf E (conjAd E a) = starRingEnd (Cinf E) (pInf E a) := fun a => (infEq E).symm_apply_apply _
  have hM : GeneralLinearGroup.map (pInf E) x.1 ∈ UJ (starRingEnd (Cinf E)) (1 : Matrix (Fin n) (Fin n) (Cinf E)) := by
    have h0 : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1 = 1 := x.2
    rw [mul_one] at h0
    have e : cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) =
        (cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E))).map (pInf E) := by
      ext i j
      simp [Formalism.UG.cT, hp]
    change cT (starRingEnd (Cinf E)) ((x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E)) * 1 *
      (x.1 : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1
    rw [e, mul_one, ← Matrix.map_mul, h0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hxe : infPt ⟨_, hM⟩ = x := by
    refine Subtype.ext (ga_ext ?_ ?_)
    · exact pInf_infGL _
    · exact (pFin_infGL _).trans hx.symm
  rw [← hxe]
  refine closure_mono ?_ (image_closure_subset_closure_image continuous_infPt ⟨_, hd ⟨_, hM⟩, rfl⟩)
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨γ, hγ, hγh⟩ := Subgroup.mem_map.1 hh
  have hγ0 : cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * 1 * γ = 1 := hγ
  rw [mul_one] at hγ0
  have hr : ratGL E n γ ∈ UA E n := by
    have e : cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) =
        (cT (IsCMField.complexConj E : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (algebraMap E (Ad E)) := by
      ext i j
      simp [Formalism.UG.cT, conjAd_algebraMap]
    change cT (conjAd E) ((γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E))) * 1 *
      (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (Ad E)) = 1
    rw [e, mul_one, ← Matrix.map_mul, hγ0, Matrix.map_one _ (map_zero _) (map_one _)]
  let r : UA E n := ⟨ratGL E n γ, hr⟩
  have hrU : r ∈ ratU E n := Subgroup.mem_subgroupOf.2 ⟨γ, rfl⟩
  have hk : r⁻¹ * infPt h ∈ finU (E := E) (n := n) := by
    have e1 : GeneralLinearGroup.map (pInf E) (ratGL E n γ) = h.1 := by
      rw [← hγh]
      exact Units.ext rfl
    change GeneralLinearGroup.map (pInf E) ((ratGL E n γ)⁻¹ * infGL E n h.1) = 1
    rw [map_mul, map_inv, e1, pInf_infGL, inv_mul_cancel]
  exact ⟨r, hrU, r⁻¹ * infPt h, hk, mul_inv_cancel_left r _⟩

theorem eq_zero_of_finU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (φ : UA L n → ℂ),
    IsAutFormU φ → (∀ y ∈ finU (E := L) (n := n), φ y = 0) → φ = 0 := by
  intro L _ _ _ n φ hφ h0
  have hS : ((ratU L n : Set (UA L n)) * (finU (E := L) (n := n) : Set (UA L n))) ⊆ {g | φ g = 0} := by
    rintro _ ⟨γ, hγ, k, hk, rfl⟩
    change φ (γ * k) = 0
    rw [hφ.left γ hγ k]
    exact h0 k hk
  have hZ : IsClosed {g : UA L n | φ g = 0} := isClosed_eq hφ.cont continuous_const
  funext g
  obtain ⟨k, hk, x, hx, rfl⟩ := GlobalTheory.DefU.exists_finU_mul_infU L n g
  rw [GlobalTheory.DefU.fin_mul_inf hk hx]
  have hc : Continuous (· * k : UA L n → UA L n) := continuous_mul_const k
  have hxk : x * k ∈ closure ((ratU L n : Set (UA L n)) * (finU (E := L) (n := n) : Set (UA L n))) := by
    refine closure_mono ?_ (image_closure_subset_closure_image hc ⟨x, mem_closure_rat_fin x hx, rfl⟩)
    rintro _ ⟨_, ⟨γ, hγ, k', hk', rfl⟩, rfl⟩
    exact ⟨γ, hγ, k' * k, (finU (E := L) (n := n)).mul_mem hk' hk, (mul_assoc _ _ _).symm⟩
  exact hZ.closure_subset_iff.2 hS hxk

end GlobalTheory.DefiniteDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteLeOfClosureClasses
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
  GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

namespace GlobalTheory.DiscClosure

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}


variable (E N) in
def autSub : Submodule ℂ (Sm E N) where
  carrier := {φ | IsAutForm φ}
  zero_mem' := isAutForm_const (Submodule.zero_mem _)
  add_mem' := fun {φ ψ} h h' => by
    simpa using GlobalTheory.CuspFormLin.isAutForm_smul_add 1 h h'
  smul_mem' := fun c φ h => by
    simpa using GlobalTheory.CuspFormLin.isAutForm_smul_add c h (isAutForm_const (Submodule.zero_mem _))


variable (μ : Measure (GA E N)) in
def squareIntegrableSmoothSubmoduleGL : Submodule ℂ (Sm E N) where
  carrier := {φ | MemL2Quotient (latticeGL E N) μ φ.1}
  zero_mem' := ⟨fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ hγ g => by
    change φ.1 (γ * g) + ψ.1 (γ * g) = φ.1 g + ψ.1 g
    rw [h.1 γ hγ g, h'.1 γ hγ g], h.2.add h'.2⟩
  smul_mem' := fun c φ h => ⟨fun γ hγ g => by
    change c * φ.1 (γ * g) = c * φ.1 g
    rw [h.1 γ hγ g], h.2.const_smul c⟩

def stabSub (φ : Sm E N) : Subgroup (GL (Fin N) (Af E)) where
  carrier := {k | finRep E N k φ = φ}
  mul_mem' := fun {a b} ha hb => by
    change finRep E N (a * b) φ = φ
    have ha' : finRep E N a φ = φ := ha
    have hb' : finRep E N b φ = φ := hb
    rw [map_mul, Module.End.mul_apply, hb', ha']
  one_mem' := by
    change finRep E N 1 φ = φ
    rw [map_one]; rfl
  inv_mem' := fun {a} ha => by
    change finRep E N a⁻¹ φ = φ
    have ha' : finRep E N a φ = φ := ha
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

end GlobalTheory.DiscClosure

namespace GlobalTheory.DiscClosure

open GlobalTheory.PRep GlobalTheory.CuspRep.LocEx GlobalTheory.DiscLocEx

end GlobalTheory.DiscClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianEqIffSiegelParabolicCoset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SWLagSame

open GlobalTheory.RawLift GlobalTheory.SWLagTerms GlobalTheory.Doubling

variable {D : D7}

theorem gram_conjT (W : HSp D) : W.gramᴴ = W.gram :=
  Matrix.ext fun i j => W.herm.eq (W.frame j) (W.frame i)

theorem gram_det_unit (W : HSp D) : IsUnit W.gram.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ v : Fin W.rank → D.host.E, W.gram *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h0 : ∑ j, v j • W.frame j = 0 := by
      apply W.nondeg.2
      intro x
      rw [← W.frame.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at hi
      calc _ = (starRingEnd D.host.E) (W.frame.repr x i) * ∑ j, W.hT (W.frame i) (W.frame j) * v j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hi, mul_zero]
    funext j
    exact Fintype.linearIndependent_iff.1 W.frame.linearIndependent v h0 j
  intro a b hab
  exact sub_eq_zero.1 (key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self]))

theorem hAdj_eq (W : HSp D) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    hAdj W M = W.gram⁻¹ * Mᴴ * W.gram := rfl

theorem hAdj_mul (W : HSp D) (M N : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    hAdj W (M * N) = hAdj W N * hAdj W M := by
  simp only [hAdj_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc W.gram W.gram⁻¹, Matrix.mul_nonsing_inv _ (gram_det_unit W), Matrix.one_mul]

theorem hAdj_hAdj (W : HSp D) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : hAdj W (hAdj W M) = M := by
  simp only [hAdj_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, gram_conjT,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (gram_det_unit W), Matrix.nonsing_inv_mul _ (gram_det_unit W),
    Matrix.mul_one]

def rowD₁ (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (GlobalTheory.SWLagTerms.blk W g).toBlocks₁₁ - (GlobalTheory.SWLagTerms.blk W g).toBlocks₂₁

def rowD₂ (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (GlobalTheory.SWLagTerms.blk W g).toBlocks₂₂ - (GlobalTheory.SWLagTerms.blk W g).toBlocks₁₂

theorem frameOf_eq (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    frameOf W g = (hAdj W (rowD₂ W g), hAdj W (rowD₁ W g)) := rfl

theorem blk_mul (W : HSp D) (h g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    GlobalTheory.SWLagTerms.blk W (h * g) = GlobalTheory.SWLagTerms.blk W h * GlobalTheory.SWLagTerms.blk W g := by
  simp only [GlobalTheory.SWLagTerms.blk, Matrix.submatrix_mul_equiv]

section Blocks

variable {K : Type} [Field K] {r : ℕ}

theorem toBlocks_mul_parts (X Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    (X * Y).toBlocks₁₁ = X.toBlocks₁₁ * Y.toBlocks₁₁ + X.toBlocks₁₂ * Y.toBlocks₂₁ ∧
    (X * Y).toBlocks₁₂ = X.toBlocks₁₁ * Y.toBlocks₁₂ + X.toBlocks₁₂ * Y.toBlocks₂₂ ∧
    (X * Y).toBlocks₂₁ = X.toBlocks₂₁ * Y.toBlocks₁₁ + X.toBlocks₂₂ * Y.toBlocks₂₁ ∧
    (X * Y).toBlocks₂₂ = X.toBlocks₂₁ * Y.toBlocks₁₂ + X.toBlocks₂₂ * Y.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.mul_apply,
      Fintype.sum_sum_type]

theorem keeps_iff_common (H G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (hG : IsUnit G.det) :
    H.toBlocks₂₁ + H.toBlocks₂₂ = H.toBlocks₁₁ + H.toBlocks₁₂ ↔
      ∃ Q, (H * G).toBlocks₁₁ - (H * G).toBlocks₂₁ = Q * (G.toBlocks₁₁ - G.toBlocks₂₁) ∧
        (H * G).toBlocks₂₂ - (H * G).toBlocks₁₂ = Q * (G.toBlocks₂₂ - G.toBlocks₁₂) := by
  obtain ⟨e11, e12, e21, e22⟩ := toBlocks_mul_parts H G
  rw [e11, e12, e21, e22]
  constructor
  · intro kd
    have h22 : H.toBlocks₂₂ = H.toBlocks₁₁ + H.toBlocks₁₂ - H.toBlocks₂₁ := by rw [← kd]; abel
    refine ⟨H.toBlocks₁₁ - H.toBlocks₂₁, ?_, ?_⟩ <;> rw [h22] <;> noncomm_ring
  · rintro ⟨Q, h1, h2⟩
    set X := H.toBlocks₁₁ - H.toBlocks₂₁ - Q
    set Y := H.toBlocks₂₂ - H.toBlocks₁₂ - Q
    have hm : Matrix.fromBlocks X (-Y) (0 : Matrix (Fin r) (Fin r) K) 0 * G = 0 := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks G]
      rw [Matrix.fromBlocks_multiply]
      have a1 : X * G.toBlocks₁₁ + -Y * G.toBlocks₂₁ = 0 := by
        simp only [X, Y]; rw [← sub_eq_zero] at h1; rw [← h1]; noncomm_ring
      have a2 : X * G.toBlocks₁₂ + -Y * G.toBlocks₂₂ = 0 := by
        simp only [X, Y]; rw [← sub_eq_zero] at h2; rw [← neg_eq_zero, ← h2]; noncomm_ring
      rw [a1, a2]
      simp
    have h0 : Matrix.fromBlocks X (-Y) (0 : Matrix (Fin r) (Fin r) K) 0 = 0 := by
      have := Matrix.mul_nonsing_inv_cancel_right G (Matrix.fromBlocks X (-Y) (0 : Matrix (Fin r) (Fin r) K) 0) hG
      rw [hm, Matrix.zero_mul] at this
      exact this.symm
    rw [← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at h0
    have hX : X = 0 := h0.1
    have hY : Y = 0 := neg_eq_zero.1 h0.2.1
    have e1 : H.toBlocks₁₁ = H.toBlocks₂₁ + Q := sub_eq_zero.1 (by rw [← sub_sub]; exact hX)
    have e2 : H.toBlocks₂₂ = H.toBlocks₁₂ + Q := sub_eq_zero.1 (by rw [← sub_sub]; exact hY)
    rw [e1, e2]; abel

end Blocks

theorem lag_eq_iff (W : HSp D) {Y Y' : Lag W}
    {C C' : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hY : IsLagFrame W Y C) (hY' : IsLagFrame W Y' C') :
    Y = Y' ↔ ∃ B, C'.1 = C.1 * B ∧ C'.2 = C.2 * B := by
  have hcol : ∀ (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E)
      (B : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (j : Fin W.rank),
      ((fun a => (C.1 * B) a j), (fun a => (C.2 * B) a j)) = ∑ k, B k j • ((fun a => C.1 a k), (fun a => C.2 a k)) := by
    intro C B j
    ext a <;> simp [Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, mul_comm]
  constructor
  · rintro rfl
    have hmem : ∀ j, ((fun a => C'.1 a j), (fun a => C'.2 a j)) ∈
        Submodule.span D.host.E (Set.range fun k => ((fun a => C.1 a k), (fun a => C.2 a k))) := by
      intro j
      rw [IsLagFrame] at hY hY'
      rw [hY, ← hY']
      exact Submodule.subset_span ⟨j, rfl⟩
    choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun D.host.E).1 (hmem j)
    refine ⟨Matrix.of fun k j => c j k, ?_, ?_⟩
    · refine Matrix.ext fun a j => ?_
      have := congrArg (fun p => p.1 a) (hc j)
      simp [Prod.fst_sum, Finset.sum_apply] at this
      rw [Matrix.mul_apply]; simpa [mul_comm] using this.symm
    · refine Matrix.ext fun a j => ?_
      have := congrArg (fun p => p.2 a) (hc j)
      simp [Prod.snd_sum, Finset.sum_apply] at this
      rw [Matrix.mul_apply]; simpa [mul_comm] using this.symm
  · rintro ⟨B, h1, h2⟩
    have hle : Y'.1 ≤ Y.1 := by
      rw [IsLagFrame] at hY hY'
      rw [← hY, ← hY', Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [h1, h2]
      rw [hcol]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (Y'.2.1.trans Y.2.1.symm)).symm

theorem frame_iff (W : HSp D) (g g' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    (∃ B, (frameOf W g').1 = (frameOf W g).1 * B ∧ (frameOf W g').2 = (frameOf W g).2 * B) ↔
      ∃ Q, rowD₁ W g' = Q * rowD₁ W g ∧ rowD₂ W g' = Q * rowD₂ W g := by
  simp only [frameOf_eq]
  constructor
  · rintro ⟨B, h1, h2⟩
    refine ⟨hAdj W B, ?_, ?_⟩
    · rw [← hAdj_hAdj W (rowD₁ W g'), h2, hAdj_mul, hAdj_hAdj]
    · rw [← hAdj_hAdj W (rowD₂ W g'), h1, hAdj_mul, hAdj_hAdj]
  · rintro ⟨Q, h1, h2⟩
    exact ⟨hAdj W Q, by rw [h2, hAdj_mul], by rw [h1, hAdj_mul]⟩

theorem keeps_iff_rows (W : HSp D) (g g' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (hg : IsUnit g.det) :
    KeepsDiag finSumFinEquiv (g' * g⁻¹) ↔ ∃ Q, rowD₁ W g' = Q * rowD₁ W g ∧ rowD₂ W g' = Q * rowD₂ W g := by
  have hb : IsUnit (GlobalTheory.SWLagTerms.blk W g).det := by
    rw [GlobalTheory.SWLagTerms.blk, Matrix.det_submatrix_equiv_self]; exact hg
  have := keeps_iff_common (GlobalTheory.SWLagTerms.blk W (g' * g⁻¹)) (GlobalTheory.SWLagTerms.blk W g) hb
  rw [← blk_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hg] at this
  exact this

theorem keeps_map_iff {K A : Type} [CommRing K] [CommRing A] (f : K →+* A) (hf : Function.Injective f) {n ι : Type}
    (e : n ⊕ n ≃ ι) (M : Matrix ι ι K) : KeepsDiag e (M.map f) ↔ KeepsDiag e M := by
  rw [GlobalTheory.Doubling.keepsDiag_iff e, GlobalTheory.Doubling.keepsDiag_iff e]
  simp only [Matrix.map_apply, ← map_add (f := _), hf.eq_iff]

theorem sameClass : ∀ (D : D7) (W : HSp D) (γ γ' : GA D (GlobalTheory.Doubling.dblSp W)) (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) (g₀' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ' = g₀'.map (incA D) → ∀ (Y Y' : Lag W), IsLagFrame W Y (frameOf W g₀) → IsLagFrame W Y' (frameOf W g₀') → (Y = Y' ↔ γ' * γ⁻¹ ∈ GlobalTheory.Doubling.siegel W) := by
  intro D W γ γ' g₀ g₀' hγ hγ' Y Y' hY hY'
  have hinj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  haveI := hinj.nontrivial
  have hu : IsUnit (g₀.map (incA D)).det := by
    rw [← hγ, ← Matrix.isUnit_iff_isUnit_det]
    exact (matHom (GlobalTheory.Doubling.dblSp W) γ).isUnit
  have hg₀ : IsUnit g₀.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h := hu
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h
    exact not_isUnit_zero h
  have h1 : mt _ γ⁻¹ * mt _ γ = 1 := by
    show (matHom (GlobalTheory.Doubling.dblSp W) γ⁻¹).val * (matHom (GlobalTheory.Doubling.dblSp W) γ).val = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : (g₀⁻¹).map (incA D) * g₀.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg₀, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hγ] at h1
  have hinv : mt _ γ⁻¹ = (g₀⁻¹).map (incA D) := by
    rw [← Matrix.mul_nonsing_inv_cancel_right _ (mt _ γ⁻¹) hu, h1, ← h2, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  have hmt : mt _ (γ' * γ⁻¹) = (g₀' * g₀⁻¹).map (incA D) := by
    rw [Matrix.map_mul, ← hγ', ← hinv]
    show (matHom (GlobalTheory.Doubling.dblSp W) (γ' * γ⁻¹)).val = (matHom (GlobalTheory.Doubling.dblSp W) γ').val * (matHom (GlobalTheory.Doubling.dblSp W) γ⁻¹).val
    rw [map_mul, Units.val_mul]
  rw [lag_eq_iff W hY hY', frame_iff, ← keeps_iff_rows W g₀ g₀' hg₀, ← keeps_map_iff (incA D) hinj, ← hmt]
  exact GlobalTheory.Doubling.mem_siegelOf.symm

end GlobalTheory.SWLagSame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePartMulDefiniteUnitaryInfinitePoint
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RatFinPart

theorem exists_gq_mul_infU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) :
    ∀ γ ∈ ratU L n, ∃ (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom ∧
      γ * (F.j γQ)⁻¹ ∈ infU L n := by
  intro γ hγ
  obtain ⟨γ₀, hγ₀⟩ := (Subgroup.mem_subgroupOf).1 hγ
  set σ : L →+* L := (IsCMField.complexConj L : L →+* L) with hσ
  have hU := γ.2
  change Formalism.UG.cT (conjAd L) ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
    ((γ.1 : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) = 1 at hU
  rw [← hγ₀] at hU
  have h2 : Matrix.transpose ((γ₀ : Matrix (Fin n) (Fin n) L).map σ) * (γ₀ : Matrix (Fin n) (Fin n) L) = 1 := by
    have hinj : Function.Injective (algebraMap L (Ad L)) := fun x y h => by
      obtain ⟨w⟩ : Nonempty (InfinitePlace L) := inferInstance
      have := congrArg (fun z => pInf L z w) h
      simp only [pInf_algebraMap] at this
      exact w.embedding.injective this
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), ← hU, Matrix.mul_one]
    congr 1
    ext i j
    simp [Formalism.UG.cT, ratGL, conjAd_algebraMap, hσ]
  have hu : (γ₀ : Matrix (Fin n) (Fin n) L) * conjT σ γ₀ = 1 := mul_eq_one_comm.1 h2
  let g : GL (Fin n) (AL L) := Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom γ₀
  have hcj : ∀ x : L, conjAL L (x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) =
      σ x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) := fun x => rfl
  have hg : g ∈ ReciprocityTheory.Aut.GA L n := by
    change (g : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) = 1
    have e : conjT (conjAL L) (g : Matrix (Fin n) (Fin n) (AL L)) =
        (conjT σ (γ₀ : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom := by
      ext i j
      simp [conjT, g, hcj]
    rw [e]
    change (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom * _ = 1
    rw [← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hq : (⟨g, hg⟩ : ReciprocityTheory.Aut.GA L n) ∈ GQ L n := by
    rw [GQ, Subgroup.mem_subgroupOf]
    exact ⟨γ₀, hu, rfl⟩
  let x : GAf L n := ⟨g, hg⟩
  refine ⟨⟨x, hq⟩, γ₀, hγ₀.symm, rfl, ?_⟩
  rw [infU, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
  ext s t : 2
  refine FiniteAdeleRing.ext _ fun w => ?_
  have hl := F.loc x w s t
  have e1 : (cLoc w (F.j x) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) s t =
      pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w := rfl
  change pFin L ((γ.1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w =
    pFin L (((F.j x).1 : Matrix (Fin n) (Fin n) (Ad L)) s t) w
  rw [← e1, hl, ← hγ₀]
  change pFin L (algebraMap L (Ad L) ((γ₀ : Matrix (Fin n) (Fin n) L) s t)) w =
    F.κ ((γ₀ : Matrix (Fin n) (Fin n) L) s t ⊗ₜ 1) w
  rw [F.left]
  rfl

end GlobalTheory.RatFinPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstColumnInvFiniteMemCompactOnSupportStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstColumn_inv_finite_mem_compact_on_support : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := by
  first | (exact @GlobalTheory.NmUnfCol.finite_first_col_inv_compact) | (exact GlobalTheory.NmUnfCol.finite_first_col_inv_compact) | (intros; apply GlobalTheory.NmUnfCol.finite_first_col_inv_compact  <;> assumption)
end

