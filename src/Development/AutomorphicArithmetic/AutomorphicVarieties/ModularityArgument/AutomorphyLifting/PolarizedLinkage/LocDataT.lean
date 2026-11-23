module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LLocData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.Zero.LLC
open GlobalTheory.PRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.LocalCharacterData

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem psi_val (ψ : Fin n → kˣ →* ℂˣ) (χ : (Fin n → kˣ) →* ℂˣ)
    (hχ : torusChar ψ = χ * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom))
    (x : kˣ) (i : Fin n) :
    (ψ i x : ℂ) = (resCard k : ℂ) ^ (((i : ℕ) : ℤ) * ord k x) * χ (Pi.mulSingle i x) * (absPow k (((n : ℂ) - 1) / 2) x : ℂ) := by
  have h1 : torusChar ψ (Pi.mulSingle i x) = ψ i x := by
    rw [torusChar_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  have hd : ∀ (t : Fin n → kˣ) j, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t j) = t j := fun t =>
    congrFun ((leviTorus k (Fin n)).left_inv t)
  have h2 : deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (Pi.mulSingle i x)) =
      absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) x := by
    rw [deltaHalf_apply, Finset.prod_eq_single i, hd, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [hd, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  have h3 : (modExp (fun _ : Fin n => Unit) i : ℂ) / 2 = -((i : ℕ) : ℂ) + ((n : ℂ) - 1) / 2 := by
    rw [modExp_fin _ (fun _ => by simp)]
    push_cast
    ring
  have h4 : (absPow k (-((i : ℕ) : ℂ)) x : ℂ) = (resCard k : ℂ) ^ (((i : ℕ) : ℤ) * ord k x) := by
    rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
    congr 1
    ring
  rw [← h1, hχ]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
  erw [h2]
  rw [h3, absPow_add, MonoidHom.mul_apply, Units.val_mul, h4]
  ring

private theorem unlinked_of_gen (ψ : Fin n → kˣ →* ℂˣ) (hψ : ∀ i, IsSmoothChar (ψ i)) (χ : (Fin n → kˣ) →* ℂˣ)
    (hχ : torusChar ψ = χ * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom))
    (x : kˣ) (hx : ord k x = 1) (α : Fin n → ℂ)
    (hα : ∀ i, α i = (resCard k : ℂ) ^ (i : ℕ) * χ (Pi.mulSingle i x))
    (hgen : ∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (resCard k : ℂ) * α i') :
    GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ψ hψ) := by
  have hq2 : 2 ≤ resCard k := Finite.one_lt_card (α := 𝓀[k])
  have hq0 : (resCard k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hq1 : (resCard k : ℂ) ≠ 1 := fun e => by
    have : resCard k = 1 := by exact_mod_cast e
    omega
  have hab : (absPow k 1 x : ℂ) * (resCard k : ℂ) = 1 := by
    rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, hx, Complex.cpow_one]
    simp [hq0]
  intro y hy z hz e
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
  have e1 : (ψ i x : ℂ) = ψ j x * (absPow k ((1 : ℂ)) x : ℂ) := by
    rw [e]
    simp
  rw [psi_val ψ χ hχ x i, psi_val ψ χ hχ x j, hx, mul_one, mul_one, zpow_natCast, zpow_natCast, ← hα, ← hα] at e1
  have hu : (absPow k (((n : ℂ) - 1) / 2) x : ℂ) ≠ 0 := Units.ne_zero _
  have e2 : α i = α j * (absPow k ((1 : ℂ)) x : ℂ) := by
    apply mul_right_cancel₀ hu
    rw [e1]
    ring
  have e3 : α j = (resCard k : ℂ) * α i := by
    rw [e2]
    linear_combination (-α j) * hab
  have hne : α i ≠ 0 := by
    rw [hα]
    exact mul_ne_zero (pow_ne_zero _ hq0) (Units.ne_zero _)
  by_cases hij : j = i
  · subst hij
    have : (1 : ℂ) = resCard k := mul_right_cancel₀ hne ((one_mul _).trans e3)
    exact hq1 this.symm
  · exact (hgen j i hij).2 e3

end Loc

end UpperTheory.V.Z.Win.LocalCharacterData

namespace UpperTheory.V.Z.Win.LocalCharacterData

section WD

open Polynomial

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (k := w.adicCompletion E) → WD h} {n : ℕ}

private theorem support_chars (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hψ : ∀ i, IsSmoothChar (ψ i)) (hs : IsSubquotient σ.ρ (prinSeries ψ)) :
    HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (GlobalTheory.RoadU.chars ψ hψ) :=
  (hasSupport_of_isCuspSupport (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries (k := w.adicCompletion E)
    ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ hψ hs)).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)

private theorem jqRecV (L : LawsV a ha ε rc) (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (hψ : ∀ i, IsSmoothChar (ψ i)) (hs : IsSubquotient σ.ρ (prinSeries ψ))
    (g : Weil h) :
    (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol g = ∏ i, (X - C ((ψ i (a g) : ℂˣ) : ℂ)) := by
  rw [L.supp _ _ (support_chars σ ψ hψ hs) g, GlobalTheory.RoadU.chars, Multiset.map_map, Finset.prod_eq_multiset_prod]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  simp only [Function.comp_apply]
  rw [L.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

private theorem nuCharV (L : LawsV a ha ε rc) (σ : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (χ : (Fin n → (w.adicCompletion E)ˣ) →* ℂˣ) (hψ : ∀ i, IsSmoothChar (ψ i))
    (hχ : torusChar ψ = χ * ((deltaHalf (w.adicCompletion E) fun _ : Fin n => Unit).comp
      (leviTorus (w.adicCompletion E) (Fin n)).toMonoidHom))
    (hs : IsSubquotient σ.ρ (prinSeries ψ)) (g : Weil h) :
    (rc (algNorm σ)).charPol g = ∏ i : Fin n, (X - C ((resCard (w.adicCompletion E) : ℂ) ^
      (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) * (χ (Pi.mulSingle i (a g)) : ℂ))) := by
  have H := jqRecV L σ ψ hψ hs g
  rw [algNorm, L.nu_eq]
  generalize rc (IrrGL.of σ.ρ σ.smooth σ.irred) = x at H ⊢
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.charPol_mk] at H
  rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, ← GlobalTheory.SatChar.absPow_art ha ((1 - (n : ℝ)) / 2) g]
  let u : ℂ := absPow (w.adicCompletion E) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) (a g)
  have hu : u ≠ 0 := Units.ne_zero _
  have hscale : (u • b.ρ g).charpoly = (b.ρ g).charpoly.scaleRoots u := by
    apply Polynomial.funext
    intro x
    have hx : x = u * (u⁻¹ * x) := by rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
    rw [hx, scaleRoots_eval_mul, LinearMap.charpoly_natDegree, LinearMap.eval_charpoly,
      LinearMap.eval_charpoly, ← LinearMap.det_smul, smul_sub, Module.algebraMap_end_eq_smul_id,
      Module.algebraMap_end_eq_smul_id, smul_smul]
  let scale : ℂ[X] →* ℂ[X] := {
    toFun := fun p => p.scaleRoots u
    map_one' := one_scaleRoots u
    map_mul' := fun p q => mul_scaleRoots_of_noZeroDivisors p q u }
  have hprod : (u • b.ρ g).charpoly = ∏ i, (X - C ((ψ i (a g) : ℂ) * u)) := by
    rw [hscale, H]
    change scale (∏ i, (X - C (ψ i (a g) : ℂ))) = _
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => X_sub_C_scaleRoots _ _
  rw [hprod]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  have e1 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  have e2 : (absPow (w.adicCompletion E) (((n : ℂ) - 1) / 2) (a g) : ℂ) *
      (absPow (w.adicCompletion E) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) (a g) : ℂ) = 1 := by
    rw [← Units.val_mul, ← MonoidHom.mul_apply, ← absPow_add, e1, val_absPow, Complex.cpow_zero]
  rw [psi_val ψ χ hχ (a g) i]
  linear_combination ((resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) *
    (χ (Pi.mulSingle i (a g)) : ℂ)) * e2

end WD

end UpperTheory.V.Z.Win.LocalCharacterData

