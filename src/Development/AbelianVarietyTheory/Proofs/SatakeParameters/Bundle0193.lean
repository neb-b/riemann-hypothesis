module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InductionInStagesTwoFactorsEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0129
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattened
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section
open ValuativeRel Matrix GlobalTheory.SmGL.MultiIrr GlobalTheory.LocGL
open scoped TensorProduct

namespace GlobalTheory.SmGL.Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_equiv_right {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] (h : a ⊕ b ≃ n) (A : Representation ℂ (GL a k) V)
    {B : Representation ℂ (GL b k) W} {B' : Representation ℂ (GL b k) U} (φ : B.Equiv B') :
    Nonempty ((ind₂ h (extTensor A B)).Equiv (ind₂ h (extTensor A B'))) := by
  refine ⟨parIndEquiv _ (compEquiv (.mk (φ.toLinearEquiv.lTensor V) fun g => ?_) _)⟩
  refine TensorProduct.ext' fun v w => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.lTensor_tmul, extTensor_tmul]
  congr 1
  exact φ.toIntertwiningMap.isIntertwining _ _ _ _

theorem piTensor_tmulEquivDep {β₀ β₁ : Type} {Γ X : β₀ ⊕ₗ β₁ → Type} [∀ c, Group (Γ c)]
    [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (ρ : ∀ c, Representation ℂ (Γ c) (X c)) (g : ∀ c, Γ c)
    (x : (⨂[ℂ] i, X (toLex (.inl i))) ⊗[ℂ] (⨂[ℂ] j, X (toLex (.inr j)))) :
    piTensor ρ g (PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c)) x) =
      PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
      (TensorProduct.map (piTensor (fun i => ρ (toLex (.inl i))) fun i => g (toLex (.inl i)))
        (piTensor (fun j => ρ (toLex (.inr j))) fun j => g (toLex (.inr j))) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact map_zero (piTensor ρ g)
  | add x y hx hy => simp only [map_add (f := _)]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hx, hy]; rfl)
  | tmul v w =>
    induction v using PiTensorProduct.induction_on with
    | add v v' hv hv' => simp only [TensorProduct.add_tmul, map_add (f := _)]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hv, hv']; rfl)
    | smul_tprod c v =>
      induction w using PiTensorProduct.induction_on with
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add (f := _)]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hw, hw']; rfl)
      | smul_tprod c' w =>
        have key : piTensor ρ g (PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
            (PiTensorProduct.tprod ℂ v ⊗ₜ PiTensorProduct.tprod ℂ w)) =
            PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
              (PiTensorProduct.tprod ℂ (fun a => ρ (toLex (.inl a)) (g (toLex (.inl a))) (v a)) ⊗ₜ
                PiTensorProduct.tprod ℂ (fun a => ρ (toLex (.inr a)) (g (toLex (.inr a))) (w a))) := by
          rw [PiTensorProduct.tmulEquivDep_apply, PiTensorProduct.tmulEquivDep_apply]
          refine (piTensor_tprod ρ g _).trans ?_
          congr 1
          funext i
          rcases i with i | i <;> rfl
        simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, TensorProduct.map_tmul,
          piTensor_tprod]
        rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
          ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul, map_smul, ← key]
        exact (LinearMap.map_smul _ _ _).trans (congrArg _ (LinearMap.map_smul _ _ _))

def splitEquiv {s : ℕ} (t : Fin (s + 1) → ℕ) :
    (Fin (t 0) ⊕ₗ Σₗ i : Fin s, Fin (t i.succ)) ≃ Σₗ a, Fin (t a) where
  toFun c := Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a)))
    (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c)
  invFun c := Fin.cases (motive := fun a => Fin (t a) → Fin (t 0) ⊕ₗ Σₗ i : Fin s, Fin (t i.succ))
    (fun j => toLex (.inl j)) (fun i j => toLex (.inr (toLex ⟨i, j⟩))) (ofLex c).1 (ofLex c).2
  left_inv c := by
    rcases c with j | ⟨i, j⟩ <;> rfl
  right_inv c := by
    obtain ⟨a, j⟩ := c
    induction a using Fin.cases <;> rfl

theorem stages_equiv (s : ℕ) : ∀ (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)]
    (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)) (n : Type) [Fintype n] [DecidableEq n]
    (e : (Σ a, Fin (d a)) ≃ n),
    ∃ E : (Σ c : (Σₗ a, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n,
      Nonempty ((multiProd e fun a => multiProd (e' a) (ρ a)).Equiv
        (multiProd E fun c => ρ (ofLex c).1 (ofLex c).2)) := by
  induction s with
  | zero =>
    intro d t d' e' X _ _ ρ n _ _ e
    haveI : IsEmpty n := ⟨fun x => (e.symm x).1.elim0⟩
    haveI : IsEmpty (Σₗ a : Fin 0, Fin (t a)) := ⟨fun c => (ofLex c).1.elim0⟩
    haveI : IsEmpty (Σ c : (Σₗ a : Fin 0, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) :=
      ⟨fun x => (ofLex x.1).1.elim0⟩
    let E : (Σ c : (Σₗ a : Fin 0, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n :=
      Equiv.equivOfIsEmpty _ _
    exact ⟨E, _root_.GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty (k := k) _ _ _ _⟩
  | succ s ih =>
    intro d t d' e' X _ _ ρ n _ _ e
    have E1 := multiProd_succ_equiv (k := k) (m := fun a => Fin (d a))
      (X := fun a => IndSp (e' a) (piTensor (ρ a))) e fun a => multiProd (e' a) (ρ a)
    obtain ⟨E1⟩ := E1
    have E2 := ih (fun i => d i.succ) (fun i => t i.succ) (fun i => d' i.succ) (fun i => e' i.succ)
      (fun i => X i.succ) (fun i => ρ i.succ) _ (Equiv.refl _)
    obtain ⟨Er, ⟨E2⟩⟩ := E2
    let mS : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) → Type :=
      fun c => Fin (d' (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)
    let Es : (Σ c, mS c) ≃ n := (Equiv.sumSigmaDistrib fun x => mS (toLex x)).trans
      ((Equiv.sumCongr (e' 0) Er).trans ((headTail _).trans e))
    have E4 := _root_.GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv (k := k) (m := mS)
      (a := Fin (d 0)) (b := Σ i : Fin s, Fin (d i.succ)) (V := ⨂[ℂ] b, X 0 b) (W := ⨂[ℂ] c : Σₗ i : Fin s, Fin (t i.succ), X (ofLex c).1.succ (ofLex c).2)
      (U := ⨂[ℂ] c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)), X (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2) Es ((headTail _).trans e) (e' 0) Er
      (fun _ _ => rfl) (fun _ _ => rfl) (piTensor (ρ 0))
      (piTensor fun c : Σₗ i : Fin s, Fin (t i.succ) => ρ (ofLex c).1.succ (ofLex c).2)
      (piTensor fun c => ρ (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)

      (PiTensorProduct.tmulEquivDep ℂ fun c => X (ofLex (splitEquiv t (toLex c))).1 (ofLex (splitEquiv t (toLex c))).2)
      fun g x => piTensor_tmulEquivDep (X := fun c => X (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)
        (fun c => ρ (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2) g x
    obtain ⟨E4⟩ := E4
    have E2' : (multiProd (Equiv.refl _) fun i : Fin s => multiProd (e' i.succ) (ρ i.succ)).Equiv
        (parInd (m := fun j => mS (toLex (Sum.inr j))) Er (piTensor fun c : Σₗ i : Fin s, Fin (t i.succ) => ρ (ofLex c).1.succ (ofLex c).2)) := E2
    have E3 := ind₂_equiv_right ((headTail fun i => Fin (d i)).trans e)
      (parInd (α := Fin (t 0)) (m := fun i => mS (toLex (Sum.inl i))) (e' 0) (piTensor (ρ 0))) E2'
    obtain ⟨E3⟩ := E3
    let Esig : (Σ c : (Σₗ a, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n :=
      (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2))
        (splitEquiv t)).symm.trans Es
    have E5 := _root_.GlobalTheory.SmGL.BlockRename.multiProd_rename (k := k) (splitEquiv t) (_root_.GlobalTheory.lexSumSplit_strictMono s t) (splitEquiv t).surjective
      Esig Es (fun c' x => congrArg Es ((Equiv.sigmaCongrLeft
        (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2)) (splitEquiv t)).symm_apply_apply ⟨c', x⟩).symm) fun c => ρ (ofLex c).1 (ofLex c).2
    obtain ⟨E5⟩ := E5
    exact ⟨Esig, ⟨E1.symm.trans (E3.trans (E4.trans E5.symm))⟩⟩

theorem isSubquotient_multiProd_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ)
    (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type)
    [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)]
    (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)) (_ : ∀ a b, IsSmooth (ρ a b)) :
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a))
        (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := by
  have hφ := stages_equiv (k := k) s d t d' e' X ρ (Fin n) e
  obtain ⟨E0, ⟨φ⟩⟩ := hφ
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2)) F).trans E0
  have hψ := _root_.GlobalTheory.SmGL.BlockRename.multiProd_rename (k := k) F (_root_.GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => ρ (ofLex c).1 (ofLex c).2
  obtain ⟨ψ⟩ := hψ
  exact ⟨E, .of_injective (φ.trans ψ).toIntertwiningMap (φ.trans ψ).toLinearEquiv.injective⟩

end GlobalTheory.SmGL.Stages
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem conj_sqrtMinusD : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h2 := D.host.conjE_apply D.host.φ₀ D.host.sqrtMinusD
  have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h2, map_neg, h3]
  simp

theorem sqrtMinusD_mul_self : D.host.sqrtMinusD * D.host.sqrtMinusD = -((D.host.d : ℕ) : D.host.E) := by
  rw [← sq]
  exact D.host.sqd_sq

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj]

theorem mem_F_iff (x : D.host.E) : x ∈ D.host.F ↔ D.host.conj x = x :=
  D.host.conjE_mem_hostF_iff x

theorem d_ne_zero : ((D.host.d : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero

theorem sqrtMinusD_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have := sqrtMinusD_mul_self D
  rw [h, zero_mul, eq_comm, neg_eq_zero] at this
  exact d_ne_zero D this

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem hypEFK : Formalism.MainNotions.SphericalInertData.HypEFK D := by
  rw [Formalism.MainNotions.SphericalInertData.HypEFK, eq_top_iff]
  intro x _
  set c := D.host.conj
  set s := D.host.sqrtMinusD
  have hs : s ≠ 0 := sqrtMinusD_ne_zero D
  have hcs : c s = -s := conj_sqrtMinusD D
  have hcc : c (c x) = x := conj_conj D x
  have hu : (x + c x) / 2 ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x + c x) / 2) = _
    rw [map_div₀, map_add (f := _), hcc, map_ofNat, add_comm]
  have hv : (x - c x) / (2 * s) ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x - c x) / (2 * s)) = _
    rw [map_div₀, map_sub, map_mul, hcc, map_ofNat, hcs]
    field_simp
    ring
  have hK : s ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hx : x = (x + c x) / 2 + (x - c x) / (2 * s) * s := by
    field_simp
    ring
  rw [hx]
  refine add_mem (Subfield.subset_closure (Or.inl hu))
    (mul_mem (Subfield.subset_closure (Or.inl hv)) (Subfield.subset_closure (Or.inr hK)))

theorem two_le_finrank : 2 ≤ Module.finrank ℚ D.host.F := by
  have h := D.host.finrank_hostF
  show 2 ≤ Module.finrank ℚ (D.host.F)
  rw [h]
  have := D.R.ord_pos
  omega

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits Polynomial

variable (D : D7)

theorem d_eq : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by
  have := D.host.hyp.2.2.2.1; omega⟩

theorem isIntegral_half (y : D.host.E) (hy : y * y = -((D.host.d : ℕ) : D.host.E)) :
    IsIntegral ℤ ((1 + y) / 2) := by
  obtain ⟨m, hm⟩ := d_eq D
  refine ⟨X ^ 2 - X + C (2 * (m : ℤ)), ?_, ?_⟩
  · have : (X ^ 2 - X + C (2 * (m : ℤ)) : ℤ[X]) = X ^ 2 + (C (2 * (m : ℤ)) - X) := by ring
    rw [this]
    refine (monic_X_pow 2).add_of_left ?_
    refine lt_of_le_of_lt (degree_sub_le _ _) ?_
    rw [degree_X_pow, degree_X]
    refine max_lt (lt_of_le_of_lt degree_C_le (by norm_num)) (by norm_num)
  · have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, algebraMap_int_eq, eq_intCast]
    push_cast
    rw [hd] at hy
    linear_combination (1/4 : D.host.E) * hy

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem isSplitPl_of_two_mem (w : PlE D.host) (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    IsSplitPl D.host w := by
  set s := D.host.sqrtMinusD
  have hss : s * s = -((D.host.d : ℕ) : D.host.E) := sqrtMinusD_mul_self D
  have hss' : (-s) * (-s) = -((D.host.d : ℕ) : D.host.E) := by rw [neg_mul_neg]; exact hss
  have hcs : D.host.conj s = -s := conj_sqrtMinusD D
  obtain ⟨m, hm⟩ := d_eq D
  let α : 𝓞 D.host.E := ⟨(1 + s) / 2, isIntegral_half D s hss⟩
  let β : 𝓞 D.host.E := ⟨(1 + -s) / 2, isIntegral_half D (-s) hss'⟩
  have hα : ((α : 𝓞 D.host.E) : D.host.E) = (1 + s) / 2 := rfl
  have hβ : ((β : 𝓞 D.host.E) : D.host.E) = (1 + -s) / 2 := rfl
  have hsum : α + β = 1 := by
    apply RingOfIntegers.ext
    show (1 + s) / 2 + (1 + -s) / 2 = ((1 : 𝓞 D.host.E) : D.host.E)
    push_cast
    ring
  have hprod : α * β = ((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have key : ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) = 2 * (m : D.host.E) := by
      exact (map_mul (algebraMap (𝓞 D.host.E) D.host.E) _ _).trans (by rw [map_natCast, map_natCast]; norm_num)
    show (1 + s) / 2 * ((1 + -s) / 2) = ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)
    rw [key]
    have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    rw [hd] at hss
    linear_combination (-1/4 : D.host.E) * hss
  have hcα : D.host.conj ((α : 𝓞 D.host.E) : D.host.E) = ((β : 𝓞 D.host.E) : D.host.E) := by
    rw [hα, hβ, map_div₀, map_add (f := _), map_one, hcs, map_ofNat]
  have hcβ : D.host.conj ((β : 𝓞 D.host.E) : D.host.E) = ((α : 𝓞 D.host.E) : D.host.E) := by
    rw [← hcα, conj_conj]
  have hne : ∀ x y : 𝓞 D.host.E, x + y = 1 → x ∈ w.asIdeal → y ∉ w.asIdeal := by
    intro x y hxy hx hy
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem hx hy))
  have hmem : α * β ∈ w.asIdeal := by
    rw [hprod]; exact Ideal.mul_mem_right _ _ h2
  rcases w.isPrime.mem_or_mem hmem with ha | hb
  · refine ⟨α, ha, fun y hy => ?_⟩
    have : y = β := RingOfIntegers.coe_injective (hy.trans hcα)
    rw [this]; exact hne α β hsum ha
  · refine ⟨β, hb, fun y hy => ?_⟩
    have : y = α := RingOfIntegers.coe_injective (hy.trans hcβ)
    rw [this]; exact hne β α (by rw [add_comm]; exact hsum) hb

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

theorem jointCond_of_definite : ∀ D : D7, (∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)) →
    GlobalDatumCompatibility D := by
  intro D hdef
  refine ⟨hypEFK D, ⟨two_le_finrank D, fun w hw h2 => hw (isSplitPl_of_two_mem D w h2)⟩, hdef⟩

end GlobalTheory.DesignBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead
open scoped TensorProduct

namespace GlobalTheory.ProdReorder

section Eqv

variable {G V W U : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}

theorem eqv_trans (h₁ : Nonempty (ρ.Equiv σ)) (h₂ : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) :=
  h₁.elim fun a => h₂.elim fun b => ⟨a.trans b⟩

theorem eqv_symm (h : Nonempty (ρ.Equiv σ)) : Nonempty (σ.Equiv ρ) := h.map Representation.Equiv.symm

theorem eqv_refl (ρ : Representation ℂ G V) : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩

end Eqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_placing {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e e' : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π)) :=
  (Placing.parInd_jac_placing k α n m e e' _).1 _

theorem ind₂_congr {r t N : ℕ} (h : r + t = N) {V V' W W' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {π₁ : Representation ℂ (GL (Fin r) k) V} {σ₁ : Representation ℂ (GL (Fin r) k) V'}
    {π₂ : Representation ℂ (GL (Fin t) k) W} {σ₂ : Representation ℂ (GL (Fin t) k) W'}
    (φ₁ : Nonempty (π₁.Equiv σ₁)) (φ₂ : Nonempty (π₂.Equiv σ₂)) :
    Nonempty ((ind₂ (stdSum h) (extTensor π₁ π₂)).Equiv (ind₂ (stdSum h) (extTensor σ₁ σ₂))) := by
  subst h
  exact φ₁.elim fun a => φ₂.elim fun b => ⟨LocGL.prod₂Equiv a b⟩

theorem ind₂_assoc' {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M')
    (h₄ : r + M' = N) {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (π₁ : Representation ℂ (GL (Fin r) k) V₁)
    (π₂ : Representation ℂ (GL (Fin s) k) V₂) (π₃ : Representation ℂ (GL (Fin t) k) V₃)
    (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃) :
    Nonempty ((ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h₁) (extTensor π₁ π₂)) π₃)).Equiv
      (ind₂ (stdSum h₄) (extTensor π₁ (ind₂ (stdSum h₃) (extTensor π₂ π₃))))) := by
  subst h₁ h₃ h₂
  exact Stages.prod₂_assoc k r s t V₁ V₂ V₃ π₁ π₂ π₃ s₁ s₂ s₃

theorem multiProd_head {s : ℕ} {d : Fin (s + 1) → ℕ} {X : Fin (s + 1) → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) {T N : ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) (h : d 0 + T = N) (e' : (Σ a : Fin s, Fin (d a.succ)) ≃ Fin T) :
    Nonempty ((multiProd e π).Equiv
      (ind₂ (stdSum h) (extTensor (π 0) (multiProd e' fun a : Fin s => π a.succ)))) := by
  have hT : T = ∑ a : Fin s, d a.succ := by
    have := Fintype.card_congr e'
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    exact this.symm
  subst hT h
  have A := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := k) d (Fin.sum_univ_succ d) π
  have B := multiProd_placing (k := k) e (stdBlocks d (Fin.sum_univ_succ d)) π
  have C := multiProd_placing (k := k) (stdBlocks (fun i : Fin s => d i.succ) rfl) e' fun a => π a.succ
  exact A.elim fun A => B.elim fun B => C.elim fun C =>
    ⟨B.trans (A.symm.trans (LocGL.prod₂Equiv (Representation.Equiv.refl (π 0)) C))⟩

theorem multiProd_empty {d d' : Fin 0 → ℕ} {X X' : Fin 0 → Type} [iX : ∀ a, AddCommGroup (X a)]
    [mX : ∀ a, Module ℂ (X a)] [iX' : ∀ a, AddCommGroup (X' a)] [mX' : ∀ a, Module ℂ (X' a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d' a)) k) (X' a))
    {t : ℕ} (e : (Σ a, Fin (d a)) ≃ Fin t) (e' : (Σ a, Fin (d' a)) ≃ Fin t) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π')) := by
  obtain rfl : d = d' := funext fun a => a.elim0
  obtain rfl : X = X' := funext fun a => a.elim0
  obtain rfl : iX = iX' := funext fun a => a.elim0
  obtain rfl : mX = mX' := funext fun a => a.elim0
  obtain rfl : π = π' := funext fun a => a.elim0
  exact multiProd_placing e e' π

theorem ind₂_unit_right {r t : ℕ} (h : r + t = r) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) {d : Fin 0 → ℕ} {X : Fin 0 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (e : (Σ a, Fin (d a)) ≃ Fin t) :
    Nonempty ((ind₂ (stdSum h) (extTensor π (multiProd e τ))).Equiv π) := by
  let f : (Σ _ : Fin 1, Fin r) ≃ Fin r :=
    { toFun := Sigma.snd
      invFun := fun i => ⟨0, i⟩
      left_inv := fun ⟨a, i⟩ => by obtain rfl := Subsingleton.elim a 0; rfl
      right_inv := fun _ => rfl }
  let e' : (Σ a : Fin 0, Fin r) ≃ Fin t :=
    (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin r) (Σ a, Fin (d a))).trans e
  have A := LocGL.nonempty_equiv_multiProd_one hπ f fun _ _ => rfl
  have B := multiProd_head (k := k) (d := fun _ : Fin 1 => r) (fun _ => π) f h e'
  have C := ind₂_congr h (eqv_refl π) (multiProd_empty (k := k) (fun a : Fin 0 => π) τ e' e)
  exact eqv_symm (eqv_trans A (eqv_trans B C))

theorem multiProd_comp_congr {s u : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) {f g : Fin u → Fin s} (hfg : f = g)
    {T : ℕ} (e : (Σ i, Fin (d (f i))) ≃ Fin T) (e' : (Σ i, Fin (d (g i))) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (σ (f i)).π).Equiv (multiProd e' fun i => (σ (g i)).π)) := by
  subst hfg
  exact multiProd_placing e e' _

def sigmaPart {s s₁ s₂ : ℕ} (d : Fin s → ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s)
    (hb : Function.Bijective (Sum.elim ι₁ ι₂)) :
    (Σ a, Fin (d a)) ≃ (Σ i, Fin (d (ι₁ i))) ⊕ (Σ j, Fin (d (ι₂ j))) :=
  (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) (Equiv.ofBijective _ hb)).symm.trans
    (Equiv.sumSigmaDistrib fun x => Fin (d (Sum.elim ι₁ ι₂ x)))

def Commutes {p q : ℕ} (x : Irr k p) (y : Irr k q) : Prop :=
  ∀ (N : ℕ) (h₁ : p + q = N) (h₂ : q + p = N),
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π y.π)).Equiv (ind₂ (stdSum h₂) (extTensor y.π x.π)))

theorem Commutes.symm {p q : ℕ} {x : Irr k p} {y : Irr k q} (h : Commutes x y) : Commutes y x :=
  fun N h₁ h₂ => (h N h₂ h₁).map Representation.Equiv.symm

end GlobalTheory.ProdReorder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsCommonNaturalRepresentationStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordConditions_common_natural_representation : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL), Roomy L C₀ → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.PtIn i r ρ π → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∃ (ε : ℤˣ) (g : ZMod (RecS.nLet i w hw) → D.R.GG), IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ RecS.WordBase L HW i r ρ π w hw Cx hG (recWord L (liftIdx D i) ε g) := by
  first | exact @GlobalTheory.HTW.Rec.recS_wordBase_natural | exact GlobalTheory.HTW.Rec.recS_wordBase_natural | (intros; apply GlobalTheory.HTW.Rec.recS_wordBase_natural <;> assumption)
end

