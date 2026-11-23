module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkStab
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkStab :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (T : Module.End ℂ (S4 F)) (N N' : Submodule ℂ (S4 F)), N' ≤ Vac δ → (∀ φ ∈ N, T φ ∈ N') →
    (∀ w i φ, T (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (T φ) ∨ χ = O.d w' j (T φ)}) → ∀ m, ∀ φ ∈ O.Fk N m, T φ ∈ O.Fk N' m := by
  intro F _ _ _ δ O T N N' hN' hN hT m
  induction m with
  | zero => exact hN
  | succ m ih =>
    have hb := fkBasic F O
    have hmono : O.Fk N' m ≤ O.Fk N' (m + 1) := hb.1 N' N' le_rfl m (m + 1) (Nat.le_succ m)
    have key : O.Fk N (m + 1) ≤ (O.Fk N' (m + 1)).comap T := by
      have hu : O.Fk N (m + 1) = O.Fk N m ⊔ ⨆ w, ⨆ i, (O.Fk N m).map (O.x w i) := rfl
      rw [hu]
      refine sup_le (fun φ hφ => hmono (ih φ hφ)) (iSup_le fun w => iSup_le fun i => ?_)
      rintro _ ⟨φ, hφ, rfl⟩
      have hs : Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (T φ) ∨ χ = O.d w' j (T φ)} ≤ O.Fk N' (m + 1) := by
        refine Submodule.span_le.2 ?_
        rintro χ ⟨w', j, rfl | rfl⟩
        · exact hb.2.1 N' m w' j _ (ih φ hφ)
        · exact fkD F δ O N' hN' m w' j _ (ih φ hφ)
      exact hs (hT w i φ)
    exact fun φ hφ => key hφ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FockOps
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

private def stab {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F) :
    Subalgebra ℂ (Module.End ℂ (S4 F)) where
  carrier := {T | ∀ φ ∈ Fock δ, T φ ∈ Fock δ}
  mul_mem' := fun ha hb φ h => ha _ (hb φ h)
  add_mem' := fun ha hb φ h => Submodule.add_mem _ (ha φ h) (hb φ h)
  algebraMap_mem' := fun c φ h => by
    rw [Module.algebraMap_end_apply]
    exact Submodule.smul_mem _ c h

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.fockOps :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Ops F), ∀ φ ∈ Fock D.δ, (∀ w i, O.x w i φ ∈ Fock D.δ) ∧ (∀ w i, O.d w i φ ∈ Fock D.δ) ∧ (∀ w, O.e D.δ w φ ∈ Fock D.δ) ∧
    (∀ w, O.f D.δ w φ ∈ Fock D.δ) ∧ (∀ w, O.h w φ ∈ Fock D.δ) ∧ (∀ τ i j, O.dE D τ i j φ ∈ Fock D.δ) ∧ ∀ Y, O.dL D Y φ ∈ Fock D.δ := by
  intro F E _ _ _ _ _ _ _ D O
  have hx : ∀ w i, O.x w i ∈ stab D.δ := fun w i => (fkLe F D.δ O).1 w i
  have hd : ∀ w i, O.d w i ∈ stab D.δ := by
    intro w i φ hφ
    obtain ⟨Λ, m, h⟩ := fockEx F E D O {φ} (Set.finite_singleton φ)
      (fun ψ hψ => (Set.mem_singleton_iff.1 hψ) ▸ hφ)
    exact (fkLe F D.δ O).2 _ inf_le_left (m + 1)
      (fkD F D.δ O _ inf_le_left m w i φ (h φ (Set.mem_singleton φ)))
  have he : ∀ w, O.e D.δ w ∈ stab D.δ := fun w =>
    Subalgebra.smul_mem _ (sub_mem (sub_mem (mul_mem (hx w 2) (hx w 2))
      (Subalgebra.smul_mem _ (mul_mem (hx w 3) (hx w 3)) _)) (mul_mem (hx w 1) (hx w 0))) _
  have hf : ∀ w, O.f D.δ w ∈ stab D.δ := fun w =>
    Subalgebra.smul_mem _ (sub_mem (sub_mem (Subalgebra.smul_mem _ (mul_mem (hd w 2) (hd w 2)) _)
      (Subalgebra.smul_mem _ (mul_mem (hd w 3) (hd w 3)) _)) (mul_mem (hd w 1) (hd w 0))) _
  have hh : ∀ w, O.h w ∈ stab D.δ := fun w =>
    add_mem (sum_mem fun i _ => mul_mem (hx w i) (hd w i)) (ofNat_mem _ 2)
  have hX : ∀ τ a b, O.X D τ a b ∈ stab D.δ := by
    intro τ a b
    fin_cases a <;> fin_cases b
    · exact hx _ 1
    · exact add_mem (hx _ 2) (Subalgebra.smul_mem _ (hx _ 3) _)
    · exact sub_mem (hx _ 2) (Subalgebra.smul_mem _ (hx _ 3) _)
    · exact hx _ 0
  have hDX : ∀ τ a b, O.DX D τ a b ∈ stab D.δ := by
    intro τ a b
    fin_cases a <;> fin_cases b
    · exact hd _ 1
    · exact Subalgebra.smul_mem _ (add_mem (hd _ 2) (Subalgebra.smul_mem _ (hd _ 3) _)) _
    · exact Subalgebra.smul_mem _ (sub_mem (hd _ 2) (Subalgebra.smul_mem _ (hd _ 3) _)) _
    · exact hd _ 0
  have hE : ∀ τ i j, O.dE D τ i j ∈ stab D.δ := by
    intro τ i j
    refine sub_mem (neg_mem ?_) (sum_mem fun b _ => mul_mem (hX τ j b) (hDX τ i b))
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hL : ∀ Y, O.dL D Y ∈ stab D.δ := fun Y =>
    sum_mem fun τ _ => sum_mem fun i _ => sum_mem fun j _ => Subalgebra.smul_mem _ (hE τ i j) _
  intro φ hφ
  exact ⟨fun w i => hx w i φ hφ, fun w i => hd w i φ hφ, fun w => he w φ hφ, fun w => hf w φ hφ,
    fun w => hh w φ hφ, fun τ i j => hE τ i j φ hφ, fun Y => hL Y φ hφ⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.ProdEntries
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private noncomputable def infPart {F : Type} [Field F] [NumberField F] (b : A F) : A F := ⟨b.1, 0⟩

private theorem cm {F : Type} [Field F] [NumberField F] (a b : G1 F) :
    ((a * b : G1 F) : Matrix (Fin 2) (Fin 2) (A F)) = a.1 * b.1 := rfl

private theorem nU_coe {F : Type} [Field F] [NumberField F] (b : A F) :
    ((nU b : G1 F) : Matrix (Fin 2) (Fin 2) (A F)) = !![1, b; 0, 1] := rfl

private theorem wW_coe (F : Type) [Field F] [NumberField F] :
    ((wW F : G1 F) : Matrix (Fin 2) (Fin 2) (A F)) = !![0, 1; -1, 0] := rfl

private theorem pi_nU {F : Type} [Field F] [NumberField F] (pi : G1 F →* G1 F)
    (h1 : ∀ g, FinOne (pi g)) (h2 : ∀ g i j, (pi g i j).1 = (g i j).1) (b : A F) :
    pi (nU b) = nU (infPart b) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => Prod.ext ((h2 _ i j).trans ?_) ((h1 _ i j).trans ?_)
  · fin_cases i <;> fin_cases j <;> simp [nU, infPart]
  · fin_cases i <;> fin_cases j <;> simp [nU, infPart]

private theorem nU_inv' {F : Type} [Field F] [NumberField F] (b : A F) : (nU b)⁻¹ = nU (-b) := by
  refine inv_eq_of_mul_eq_one_right (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  simp only [cm, nU_coe, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

private theorem wW_inv' (F : Type) [Field F] [NumberField F] : (wW F)⁻¹ = wW F * wW F * wW F := by
  refine inv_eq_of_mul_eq_one_right (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)
  simp only [cm, wW_coe, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

private theorem prod_entries {F : Type} [Field F] [NumberField F] (e : A F) (he : e * e = e) :
    ((nU e * (wW F * nU e * (wW F * wW F * wW F)) * nU e : G1 F) : Matrix (Fin 2) (Fin 2) (A F)) =
      !![1 - e, e; -e, 1 - e] := by
  simp only [cm, nU_coe, wW_coe, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · rw [he]; ring
  · rw [he]; linear_combination (-1 : A F) * he
  · rw [he]; ring

private theorem pi_wW {F : Type} [Field F] [NumberField F] (pi : G1 F →* G1 F)
    (h1 : ∀ g, FinOne (pi g)) (h2 : ∀ g i j, (pi g i j).1 = (g i j).1) :
    pi (wW F) = nU (infPart 1) * (wW F * nU (infPart 1) * (wW F)⁻¹) * nU (infPart 1) := by
  have he : infPart (1 : A F) * infPart 1 = infPart 1 :=
    Prod.ext (by change ((1 : A F) * 1).1 = (1 : A F).1; rw [mul_one])
      (by change (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0; exact mul_zero _)
  have a1 : (1 - infPart 1 : A F).1 = 0 := by
    change (1 : A F).1 - (1 : A F).1 = 0
    exact sub_self _
  have a2 : (1 - infPart 1 : A F).2 = (1 : A F).2 := by
    change (1 : A F).2 - 0 = _
    exact sub_zero _
  have a3 : (-infPart 1 : A F).1 = (-1 : A F).1 := rfl
  have a4 : (-infPart 1 : A F).2 = 0 := by
    change -(0 : FiniteAdeleRing (𝓞 F) F) = 0
    exact neg_zero
  have a5 : (infPart 1 : A F).1 = (1 : A F).1 := rfl
  have a6 : (infPart 1 : A F).2 = 0 := rfl
  rw [wW_inv']
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [prod_entries _ he]
  refine Prod.ext ((h2 _ i j).trans ?_) ((h1 _ i j).trans ?_)
  · fin_cases i <;> fin_cases j <;> simp [wW, a1, a3, a5]
  · fin_cases i <;> fin_cases j <;> simp [a2, a4, a6]

private def keep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D)
    (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)) : Submonoid (G1 F) where
  carrier := {g | ∀ φ ∈ Fix D.δ Λ, W.Om g φ ∈ Fix D.δ Λ}
  one_mem' := fun φ h => by
    rw [map_one]
    exact h
  mul_mem' := fun {a b} ha hb φ h => by
    rw [map_mul]
    exact ha _ (hb _ h)

private theorem mem_keep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {D : Dat F E} (W : Weil D)
    (Λ : OpenAddSubgroup (FiniteAdeleRing (𝓞 F) F)) (g : G1 F) :
    g ∈ keep W Λ ↔ ∀ φ ∈ Fix D.δ Λ, W.Om g φ ∈ Fix D.δ Λ := Iff.rfl

theorem UpperTheory.ConvolutionTheory.R2.Fo.omFix :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (g : G1 F), FinOne g → ∀ Λ, ∀ φ ∈ Fix D.δ Λ, W.Om g φ ∈ Fix D.δ Λ := by
  intro F E _ _ _ _ _ _ _ D W g hg Λ φ hφ
  obtain ⟨pi, pf, -, hp⟩ := proj F
  have h1 : ∀ g, FinOne (pi g) := fun g => (hp g).1
  have h2 : ∀ g i j, (pi g i j).1 = (g i j).1 := fun g => (hp g).2.2.2.1
  have hw : wW F ∈ keep W Λ := (mem_keep W Λ _).2 fun φ h => (fixGen F E D W Λ φ h).1
  have hn : ∀ b : A F, b.2 = 0 → nU b ∈ keep W Λ := fun b hb =>
    (mem_keep W Λ _).2 fun φ h => (fixGen F E D W Λ φ h).2 b hb
  have hwi : (wW F)⁻¹ ∈ keep W Λ := by
    rw [wW_inv']
    exact mul_mem (mul_mem hw hw) hw
  have hpn : ∀ b, pi (nU b) ∈ keep W Λ := fun b => by
    rw [pi_nU pi h1 h2]
    exact hn _ rfl
  have hpw : pi (wW F) ∈ keep W Λ := by
    rw [pi_wW pi h1 h2]
    exact mul_mem (mul_mem (hn _ rfl) (mul_mem (mul_mem hw (hn _ rfl)) hwi)) (hn _ rfl)
  have hpwi : pi (wW F)⁻¹ ∈ keep W Λ := by
    rw [wW_inv', map_mul, map_mul]
    exact mul_mem (mul_mem hpw hpw) hpw
  let T : Subgroup (G1 F) :=
    { carrier := {y | pi y ∈ keep W Λ ∧ pi y⁻¹ ∈ keep W Λ}
      one_mem' := ⟨by rw [map_one]; exact one_mem _, by rw [inv_one, map_one]; exact one_mem _⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨by rw [map_mul]; exact mul_mem ha.1 hb.1, by rw [_root_.mul_inv_rev, map_mul]; exact mul_mem hb.2 ha.2⟩
      inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩ }
  have hT : Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) ≤ T := by
    refine (Subgroup.closure_le T).2 ?_
    rintro _ (⟨b, rfl⟩ | rfl)
    · exact ⟨hpn b, by rw [nU_inv']; exact hpn _⟩
    · exact ⟨hpw, hpwi⟩
  have hgT : g ∈ T := hT (by rw [(gen F).1]; exact Subgroup.mem_top g)
  have hpg : pi g = g := Matrix.SpecialLinearGroup.ext _ _ fun i j =>
    Prod.ext (h2 g i j) ((h1 g i j).trans (hg i j).symm)
  have hk : g ∈ keep W Λ := by
    have := hgT.1
    rwa [hpg] at this
  exact (mem_keep W Λ g).1 hk φ hφ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.StepInv
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private lemma cw_add' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (a b : A F) :
    cw w (a + b) = cw w a + cw w b := by
  simp [cw, map_add (f := _)]

private lemma cw_mul' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (a b : A F) :
    cw w (a * b) = cw w a * cw w b := by
  simp [cw, map_mul]

private lemma cw_one' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) :
    cw w (1 : A F) = 1 := by
  simp [cw, map_one]

private lemma cw_zero' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) :
    cw w (0 : A F) = 0 := by
  simp [cw, map_zero]

private lemma cw_neg' {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (a : A F) :
    cw w (-a) = -cw w a := by
  simp [cw, map_neg]

private lemma step_mul {M : Type} [AddCommGroup M] [Module ℂ M] (d p X Y : Module.End ℂ M)
    (a b c e a' b' c' e' : ℂ)
    (h₁ : d * X = X * (a • d + b • p)) (h₂ : p * X = X * (c • d + e • p))
    (k₁ : d * Y = Y * (a' • d + b' • p)) (k₂ : p * Y = Y * (c' • d + e' • p)) :
    d * (X * Y) = (X * Y) * ((a * a' + b * c') • d + (a * b' + b * e') • p) ∧
      p * (X * Y) = (X * Y) * ((c * a' + e * c') • d + (c * b' + e * e') • p) := by
  constructor
  · rw [← mul_assoc, h₁, mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, k₁, k₂]
    simp only [mul_add, mul_smul_comm, smul_add, smul_smul, add_smul, mul_assoc]
    abel
  · rw [← mul_assoc, h₂, mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, k₁, k₂]
    simp only [mul_add, mul_smul_comm, smul_add, smul_smul, add_smul, mul_assoc]
    abel

private lemma step_inv {M : Type} [AddCommGroup M] [Module ℂ M] (d p X X' : Module.End ℂ M)
    (a b c e : ℂ) (hd : a * e - b * c = 1) (hl : X' * X = 1) (hr : X * X' = 1)
    (h₁ : d * X = X * (a • d + b • p)) (h₂ : p * X = X * (c • d + e • p)) :
    d * X' = X' * (e • d + (-b) • p) ∧ p * X' = X' * ((-c) • d + a • p) := by
  have k₁ : (e • d + (-b) • p) * X = X * d := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h₁, h₂, ← mul_smul_comm, ← mul_smul_comm, ← mul_add]
    congr 1
    have : e • (a • d + b • p) + (-b) • (c • d + e • p) = (a * e - b * c) • d := by
      module
    rw [this, hd, one_smul]
  have k₂ : ((-c) • d + a • p) * X = X * p := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h₁, h₂, ← mul_smul_comm, ← mul_smul_comm, ← mul_add]
    congr 1
    have : (-c) • (a • d + b • p) + a • (c • d + e • p) = (a * e - b * c) • p := by
      module
    rw [this, hd, one_smul]
  constructor
  · calc d * X' = X' * (X * d) * X' := by rw [← mul_assoc, hl, one_mul]
      _ = X' * (e • d + (-b) • p) := by rw [← k₁, mul_assoc, mul_assoc, hr, mul_one]
  · calc p * X' = X' * (X * p) * X' := by rw [← mul_assoc, hl, one_mul]
      _ = X' * ((-c) • d + a • p) := by rw [← k₂, mul_assoc, mul_assoc, hr, mul_one]

private lemma ent_mul {R : Type} [CommRing R] (g h : Matrix.SpecialLinearGroup (Fin 2) R) :
    (g * h) 0 0 = g 0 0 * h 0 0 + g 0 1 * h 1 0 ∧ (g * h) 0 1 = g 0 0 * h 0 1 + g 0 1 * h 1 1 ∧
      (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 ∧ (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private lemma ent_inv {R : Type} [CommRing R] (g : Matrix.SpecialLinearGroup (Fin 2) R) :
    g⁻¹ 0 0 = g 1 1 ∧ g⁻¹ 0 1 = -g 0 1 ∧ g⁻¹ 1 0 = -g 1 0 ∧ g⁻¹ 1 1 = g 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem UpperTheory.ConvolutionTheory.R2.Fo.Heisenberg₂ :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (g : G1 F) w i,
    O.d w i * W.Om g = W.Om g * (cw w (g 0 0) • O.d w i + cw w (g 0 1) • O.p D.δ w i) ∧
    O.p D.δ w i * W.Om g = W.Om g * (cw w (g 1 0) • O.d w i + cw w (g 1 1) • O.p D.δ w i) := by
  intro F E _ _ _ _ _ _ _ D W O g
  have hg : g ∈ Subgroup.closure (Set.range (nU (F := F)) ∪ {wW F}) := by
    rw [(UpperTheory.ConvolutionTheory.R2.gen F).1]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    intro w i
    rcases hx with ⟨b, rfl⟩ | hx
    · have hp : O.p D.δ w i * W.Om (nU b) = W.Om (nU b) * O.p D.δ w i := by
        have hx := fun k => (dN F E D W O w k b).2
        fin_cases i
        all_goals
          simp only [Ops.p]
          show (_ • O.x w _) * _ = _ * (_ • O.x w _)
          rw [smul_mul_assoc, mul_smul_comm, hx]
      refine ⟨?_, ?_⟩
      · simpa [nU, cw_one', cw_zero'] using (dN F E D W O w i b).1
      · simpa [nU, cw_one', cw_zero'] using hp
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨?_, ?_⟩
      · simpa [wW, cw_one', cw_zero'] using dW F E D W O w i
      · simpa [wW, cw_one', cw_zero', cw_neg'] using pW F E D W O w i
  | one =>
    intro w i
    simp [cw_one', cw_zero']
  | mul x y _ _ hx hy =>
    intro w i
    obtain ⟨h₁, h₂⟩ := hx w i
    obtain ⟨k₁, k₂⟩ := hy w i
    obtain ⟨e₁, e₂, e₃, e₄⟩ := ent_mul x y
    have := step_mul _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ k₁ k₂
    rw [map_mul, e₁, e₂, e₃, e₄]
    simpa only [cw_add', cw_mul'] using this
  | inv x _ hx =>
    intro w i
    obtain ⟨h₁, h₂⟩ := hx w i
    obtain ⟨e₁, e₂, e₃, e₄⟩ := ent_inv x
    have hdet : cw w (x 0 0) * cw w (x 1 1) - cw w (x 0 1) * cw w (x 1 0) = 1 := by
      have h := x.det_coe
      rw [Matrix.det_fin_two] at h
      have := congrArg (cw w) h
      rw [sub_eq_add_neg, cw_add', cw_neg', cw_mul', cw_mul', cw_one'] at this
      rw [sub_eq_add_neg]
      exact this
    have hl : W.Om x⁻¹ * W.Om x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have hr : W.Om x * W.Om x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have := step_inv _ _ _ _ _ _ _ _ hdet hl hr h₁ h₂
    rw [e₁, e₂, e₃, e₄, cw_neg', cw_neg']
    exact this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XaCommCoord
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section Abstract

variable {A : Type*} [Ring A] [Algebra ℂ A]

private def Xa (θ : ℂ) (x : Fin 4 → A) : Fin 2 → Fin 2 → A :=
  ![![x 1, x 2 + θ • x 3], ![x 2 - θ • x 3, x 0]]

private noncomputable def Da (θ : ℂ) (d : Fin 4 → A) : Fin 2 → Fin 2 → A :=
  ![![d 1, (2 : ℂ)⁻¹ • (d 2 + θ⁻¹ • d 3)], ![(2 : ℂ)⁻¹ • (d 2 - θ⁻¹ • d 3), d 0]]

private lemma Xa_comm_coord (θ : ℂ) {x y : Fin 4 → A} (h : ∀ i j, Commute (x i) (y j)) (a b : Fin 2) (j : Fin 4) :
    Commute (Xa θ x a b) (y j) := by
  fin_cases a <;> fin_cases b
  · exact h 1 j
  · exact (h 2 j).add_left ((h 3 j).smul_left θ)
  · exact (h 2 j).sub_left ((h 3 j).smul_left θ)
  · exact h 0 j

private lemma Xa_comm (θ : ℂ) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) (a b c d : Fin 2) :
    Commute (Xa θ x a b) (Xa θ x c d) := by
  have h' := Xa_comm_coord θ h a b
  fin_cases c <;> fin_cases d
  · exact h' 1
  · exact (h' 2).add_right ((h' 3).smul_right θ)
  · exact (h' 2).sub_right ((h' 3).smul_right θ)
  · exact h' 0

private lemma Da_comm_coord (θ : ℂ) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) (a b : Fin 2) (j : Fin 4) :
    Commute (Da θ x a b) (x j) := by
  fin_cases a <;> fin_cases b
  · exact h 1 j
  · exact ((h 2 j).add_left ((h 3 j).smul_left θ⁻¹)).smul_left _
  · exact ((h 2 j).sub_left ((h 3 j).smul_left θ⁻¹)).smul_left _
  · exact h 0 j

private lemma Da_comm (θ : ℂ) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) (a b c d : Fin 2) :
    Commute (Da θ x a b) (Da θ x c d) := by
  have h' := Da_comm_coord θ h a b
  fin_cases c <;> fin_cases d
  · exact h' 1
  · exact ((h' 2).add_right ((h' 3).smul_right θ⁻¹)).smul_right _
  · exact ((h' 2).sub_right ((h' 3).smul_right θ⁻¹)).smul_right _
  · exact h' 0

private lemma Da_Xa (θ : ℂ) (hθ : θ ≠ 0) {x d : Fin 4 → A}
    (hw : ∀ i j, d i * x j = x j * d i + if i = j then 1 else 0) (a b c e : Fin 2) :
    Da θ d a b * Xa θ x c e = Xa θ x c e * Da θ d a b + if a = c ∧ b = e then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp only [Xa, Da, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, hw] <;>
    simp <;> match_scalars <;> field_simp <;> ring

private lemma Xa_det (θ c : ℂ) (hc : θ ^ 2 = c) {x : Fin 4 → A} (h : ∀ i j, Commute (x i) (x j)) :
    Xa θ x 0 1 * Xa θ x 1 0 - Xa θ x 0 0 * Xa θ x 1 1 = x 2 * x 2 - c • (x 3 * x 3) - x 1 * x 0 := by
  have h32 : x 3 * x 2 = x 2 * x 3 := h 3 2
  subst hc
  simp only [Xa, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, h32]
  match_scalars <;> ring

private lemma Da_det (θ c : ℂ) (hθ : θ ≠ 0) (hc : θ ^ 2 = c) {d : Fin 4 → A} (h : ∀ i j, Commute (d i) (d j)) :
    Da θ d 0 1 * Da θ d 1 0 - Da θ d 0 0 * Da θ d 1 1 =
      (4 : ℂ)⁻¹ • (d 2 * d 2) - (4 * c)⁻¹ • (d 3 * d 3) - d 1 * d 0 := by
  have h32 : d 3 * d 2 = d 2 * d 3 := h 3 2
  subst hc
  simp only [Da, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul, h32]
  match_scalars <;> field_simp <;> ring

private lemma Xa_Da_sum (θ : ℂ) (hθ : θ ≠ 0) (x d : Fin 4 → A) :
    ∑ a, ∑ b, Xa θ x a b * Da θ d a b = ∑ i, x i * d i := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_four, Xa, Da, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  match_scalars <;> field_simp <;> ring

end Abstract

theorem UpperTheory.ConvolutionTheory.R2.Fo.weylX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (τ : E →+* ℂ),
    (∀ a b c d, O.X D τ a b * O.X D τ c d = O.X D τ c d * O.X D τ a b) ∧ (∀ a b c d, O.DX D τ a b * O.DX D τ c d = O.DX D τ c d * O.DX D τ a b) ∧
    (∀ a b c d, O.DX D τ a b * O.X D τ c d = O.X D τ c d * O.DX D τ a b + if a = c ∧ b = d then 1 else 0) ∧
    O.e D.δ (pl F τ) = cc • (O.X D τ 0 1 * O.X D τ 1 0 - O.X D τ 0 0 * O.X D τ 1 1) ∧
    O.f D.δ (pl F τ) = (-cc⁻¹) • (O.DX D τ 0 1 * O.DX D τ 1 0 - O.DX D τ 0 0 * O.DX D τ 1 1) ∧
    O.h (pl F τ) = (∑ a, ∑ b, O.X D τ a b * O.DX D τ a b) + 2 := by
  intro F E _ _ _ _ _ _ _ D W O τ
  obtain ⟨hsq, -, hθ⟩ := (coordMk F E D).2.1 τ
  have hx : ∀ i j, Commute (O.x (pl F τ) i) (O.x (pl F τ) j) := fun i j => (weyl F O _ _ i j).1
  have hd : ∀ i j, Commute (O.d (pl F τ) i) (O.d (pl F τ) j) := fun i j => dComm F E D W O _ _ i j
  have hw : ∀ i j, O.d (pl F τ) i * O.x (pl F τ) j = O.x (pl F τ) j * O.d (pl F τ) i + if i = j then 1 else 0 := by
    intro i j
    simpa using (weyl F O (pl F τ) (pl F τ) i j).2
  have eX : O.X D τ = Xa (τ D.θ) (O.x (pl F τ)) := rfl
  have eD : O.DX D τ = Da (τ D.θ) (O.d (pl F τ)) := rfl
  rw [eX, eD]
  refine ⟨fun a b c d => Xa_comm _ hx a b c d, fun a b c d => Da_comm _ hd a b c d,
    fun a b c d => Da_Xa _ hθ hw a b c d, ?_, ?_, ?_⟩
  · rw [Xa_det _ _ hsq hx]; rfl
  · rw [Da_det _ _ hθ hsq hd]; rfl
  · rw [Xa_Da_sum _ hθ]; rfl
end

