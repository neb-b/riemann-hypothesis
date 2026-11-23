module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import GroundTheory.AutomorphicForms.TensorProductTheorem.CuspidalRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalTwists.Reduce

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapAct
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.capAct :
    UpperTheory.V.Cj.S.CapAct := by
  intro E _ _ _ a t u
  have h0 : ∀ w : Cm.UC E a, Commute (cap (a := a) t u) (Cm.uC E a w) := fun w => by
    rw [← Cm.uC_capC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (Cm.capC_mem_center t u) w).symm (Cm.uC E a)
  have h1 : ∀ g, Commute (cap (a := a) t u) (rt E a g) := fun g =>
    GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (Cm.cap_mem_Zalg t u) g
  refine ⟨h1, fun o => ?_, fun z => ?_, fun t' u' => ?_⟩
  · cases o with
    | fin k => exact h1 _
    | cpt k => exact h1 _
    | lie X =>
      have := h0 (Cm.ιC E a X)
      rw [Cm.uC_ιC] at this
      exact this
  · have := h0 (1 ⊗ₜ z)
    rwa [Cm.uC_tmul, one_smul] at this
  · have := h0 (Cm.capC t' u')
    rwa [Cm.uC_capC] at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapArith
section
open Polynomial

namespace UpperTheory.V.Cj.S

private theorem eq_of_prod_eq (m n : Multiset ℂ) (h : ∀ u : ℂ, (m.map (u + ·)).prod = (n.map (u + ·)).prod) : m = n := by
  have key : ∀ (k : Multiset ℂ) (u : ℂ),
      (((k.map fun x => -x).map fun x => X - C x).prod).eval u = (k.map (u + ·)).prod := by
    intro k u
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun x _ => ?_
    simp
  have hp : ((m.map fun x => -x).map fun x => X - C x).prod = ((n.map fun x => -x).map fun x => X - C x).prod :=
    Polynomial.funext fun u => by rw [key, key, h]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem capArith : CapArith := by
  intro m m₁ m₂ α β h
  refine eq_of_prod_eq _ _ fun u => ?_
  rw [← h u, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_map, Multiset.map_map]
  congr 2
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring
  · exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp]; ring

end UpperTheory.V.Cj.S
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapBlock
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem cast_ne_nat {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

private theorem std_eq (r s : ℕ) : GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) = finSumFinEquiv :=
  Equiv.ext fun _ => rfl

open UpperTheory.V.Af.Fin in
private theorem lev_left {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, 1) = emb (e1 r s) x := by
  refine Units.ext ?_
  rw [GlobalTheory.SmGL.val_emb₂, coe_emb, std_eq]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have := matrixExtendByZero_apply (e1 r s) (x.val - 1) i j
    simp only [orderedCechToCatCochainsOne_apply_valueAtSubset] at this
    simp [this, Matrix.one_apply]
  · rw [Matrix.add_apply, matrixExtendByZero_apply_of_outside_col _ _ _ fun k => (cast_ne_nat k j).symm]
    simp [Matrix.one_apply, cast_ne_nat]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cast_ne_nat k i).symm]
    simp [Matrix.one_apply, (cast_ne_nat _ _).symm]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => (cast_ne_nat k i).symm]
    simp [Matrix.one_apply]

open UpperTheory.V.Af.Fin in
private theorem lev_right {R : Type} [CommRing R] {r s : ℕ} (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (1, y) = emb (e2 r s) y := by
  refine Units.ext ?_
  rw [GlobalTheory.SmGL.val_emb₂, coe_emb, std_eq]
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => cast_ne_nat i k]
    simp [Matrix.one_apply]
  · rw [Matrix.add_apply, extendByZero_apply_eq_zero_of_row_not_mem _ _ fun k => cast_ne_nat i k]
    simp [Matrix.one_apply, cast_ne_nat]
  · rw [Matrix.add_apply, matrixExtendByZero_apply_of_outside_col _ _ _ fun k => cast_ne_nat j k]
    simp [Matrix.one_apply, (cast_ne_nat _ _).symm]
  · have := matrixExtendByZero_apply (e2 r s) (y.val - 1) i j
    simp only [alternatingToOrderedCechDegreeTwo_apply_valueAtSubset] at this
    simp [this, Matrix.one_apply]

private theorem lev_eq_blk {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, y) = blk x y := by
  rw [blk, ← lev_left, ← lev_right, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem UpperTheory.V.Cj.S.capBlock :
    UpperTheory.V.Cj.S.CapBlock := by
  intro E _ _ _ r s ψ hψ t u x y
  have h := GlobalTheory.CompanionTheory.CTFin.CapFactor.cap_levi E r s t u ψ (fun X g => by
    have e : unip X = unipGL (fun p : UPos (r + s) r => X ⟨p.1, p.2.1, p.2.2⟩) := Units.ext rfl
    rw [e]
    exact hψ _ g) (x, y)
  rw [lev_eq_blk] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapOfEig
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.capOfEig :
    UpperTheory.V.Cj.S.CapOfEig := by
  intro E _ _ _ a φ h0 hc
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  have key : ∀ t : E →+* ℂ, ∃ m : Multiset ℂ, Multiset.card m = a ∧
      ∀ u : ℂ, cap t u φ = (m.map (u + ·)).prod • φ := fun t => by
    obtain ⟨m, hm, h⟩ := GlobalTheory.CuspRep.exists_multiset_qdet (Eop (a := a) t) (((a : ℂ) - 1) / 2) φ f hf
    refine ⟨m, hm, fun u => ?_⟩
    obtain ⟨c, h1⟩ := hc t u
    have h2 : f (cap t u φ) = _ := h u
    rw [h1, map_smul, hf, smul_eq_mul, mul_one] at h2
    rw [h1, h2]
  choose m hm h using key
  exact ⟨m, fun t => ⟨hm t, h t⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapRel
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem slice_cap (h : UpperTheory.V.Cj.S.Slice) {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n : ℕ}
    (e : Fin a ↪ Fin n) (g : GA E n) :
    ∃ f : Sm E n →ₗ[ℂ] Sm E a, (∀ ψ x, (f ψ).1 x = ψ.1 (g * emb e x)) ∧
      ∀ t u ψ, cap t u (f ψ) = f (capB e t u ψ) := by
  obtain ⟨f, hf, hE⟩ := h E a n e g
  exact ⟨f, hf, fun t u ψ => (UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ (hE t) _ ψ).symm⟩

theorem UpperTheory.V.Cj.S.capRel :
    UpperTheory.V.Cj.S.Slice → UpperTheory.V.Cj.S.CapBlock → UpperTheory.V.Cj.S.CapRel := by
  intro hS hB E _ _ _ r s ψ hψ t u
  refine ⟨res (capB (e1 r s) t (u - (s : ℂ) / 2) ψ).1, fun y => ?_, fun x => ?_⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e1 r s) (emb (e2 r s) y)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = fun x => res φ.1 x y := fun φ => funext fun x => by
      rw [hf, res, blk, UpperTheory.V.Af.Fin.emb_comm]
    exact ⟨f ψ, key ψ, by rw [hc, key]⟩
  · obtain ⟨f, hf, hc⟩ := slice_cap hS (e2 r s) (emb (e1 r s) x)
    have key : ∀ φ : Sm E (r + s), (f φ).1 = res φ.1 x := fun φ => funext fun y => hf φ y
    refine ⟨f _, key _, ?_⟩
    rw [hc, key]
    exact funext fun y => (hB E r s ψ hψ t u x y).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiBasic
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing in
private theorem one_mem_centerU (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    UniversalEnvelopingAlgebra.ι ℝ (UpperTheory.V.Cm.lieEq E a (oneL E a)) ∈ (isExpLieAlgebra E a).centerU := by
  refine Subalgebra.mem_center_iff.2 fun u => ?_
  induction u using GroundTheory.Automorphic.AutomorphicForm.UEnv.induction with
  | halg r => exact Algebra.commutes r _
  | hι Y =>
    have h : ⁅Y, UpperTheory.V.Cm.lieEq E a (oneL E a)⁆ = 0 := by
      refine Subtype.ext ?_
      rw [LieSubalgebra.coe_bracket, UpperTheory.V.Cm.lieEq_oneL, Ring.lie_def, mul_one, one_mul, sub_self]
      rfl
    rw [← sub_eq_zero, ← Ring.lie_def, ← LieHom.map_lie, h, map_zero]
  | hmul x y hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  | hadd x y hx hy => rw [add_mul, mul_add, hx, hy]

private theorem scalar_of_mem_Zalg {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (m : (E →+* ℂ) → Multiset ℂ) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ c : ℂ, ∀ φ ∈ CI a m, z φ = c • φ := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨t, u, rfl⟩ := hz
    exact ⟨_, fun φ hφ => (mem_CI.1 hφ).2 t u⟩
  | algebraMap r => exact ⟨r, fun φ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, fun φ hφ => by rw [LinearMap.add_apply, hc φ hφ, hd φ hφ, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨d * c, fun φ hφ => by rw [Module.End.mul_apply, hd φ hφ, map_smul, hc φ hφ, mul_smul]⟩

theorem UpperTheory.V.Cj.S.ciBasic :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.CiBasic := by
  intro hc E _ _ _ a m
  refine ⟨fun o φ hφ => mem_CI.2 ⟨UpperTheory.V.Cm.isCuspForm_act o (mem_CI.1 hφ).1, fun t u => ?_⟩, ?_⟩
  · have h := LinearMap.congr_fun ((hc E a t u).2.1 o).eq φ
    rw [Module.End.mul_apply, Module.End.mul_apply, (mem_CI.1 hφ).2 t u, map_smul] at h
    exact h
  · rw [← UpperTheory.V.Cm.uTC_ι]
    exact scalar_of_mem_Zalg m (UpperTheory.V.Cm.uTC_mem_Zalg (one_mem_centerU E a))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CiCompl
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem stable_twist (χ : HChar E) {U : Submodule ℂ (Sm E a)} (h : _root_.GlobalTheory.CuspRep.IsStable U) :
    _root_.GlobalTheory.CuspRep.IsStable (U.map (mulChi a χ).toLinearMap) := by
  rintro o _ ⟨φ, hφ, rfl⟩
  exact ⟨_, add_mem (U.smul_mem _ (h o φ hφ)) (U.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩

private theorem map_twist_inv (χ : HChar E) (U : Submodule ℂ (Sm E a)) :
    (U.map (mulChi a χ).toLinearMap).map (mulChi a χ⁻¹).toLinearMap = U := by
  rw [← Submodule.map_comp]
  have : (mulChi a χ⁻¹).toLinearMap ∘ₗ (mulChi a χ).toLinearMap = LinearMap.id := LinearMap.ext fun φ => by
    change mulChi a χ⁻¹ (mulChi a χ φ) = φ
    rw [← mulChi_mul, mul_inv_cancel, mulChi_one]
  rw [this, Submodule.map_id]

private theorem exists_twist (ha : 1 ≤ a) (c : ℂ) :
    ∃ χ : HChar E, dchi χ (Matrix.of (oneL E a)).trace = -c := by
  have hn : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨Model.absC E (-c / (a * (2 * Fintype.card (InfinitePlace E)))), ?_⟩
  have e : (Matrix.of (oneL E a)).trace = a • (1 : Cinf E) := by
    change Matrix.trace (1 : Matrix (Fin a) (Fin a) (Cinf E)) = _
    simp
  rw [e, map_nsmul, GlobalTheory.GKCoh.Tests.dchi_absC_one, nsmul_eq_mul]
  push_cast
  field_simp

private theorem compl_zero {C : Submodule ℂ (Sm E a)} (hc : ∀ φ ∈ C, IsCuspForm φ)
    (h0 : ∀ φ ∈ C, lie E a (oneL E a) φ = 0) (hs : _root_.GlobalTheory.CuspRep.IsStable C) {U : Submodule ℂ (Sm E a)} (hU : U ≤ C)
    (hsU : _root_.GlobalTheory.CuspRep.IsStable U) : ∃ D ≤ C, _root_.GlobalTheory.CuspRep.IsStable D ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C := by
  have hr : C ≤ LinearMap.range (UpperTheory.V.Cm.ofCusp E a) := fun φ h => UpperTheory.V.Cm.mem_range_ofCusp.2 (hc φ h)
  have hz : C.comap (UpperTheory.V.Cm.ofCusp E a) ≤ GroundTheory.Automorphic.AutomorphicForm.centralCuspForms E a :=
    fun ψ h => UpperTheory.V.Cm.mem_centralCuspForms_of (h0 _ h)
  have st := UpperTheory.V.Cm.stab_comap hsU
  obtain ⟨D, -, d2, d3, d4, d5, d6⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_compl_centralCuspForms
    (U.comap (UpperTheory.V.Cm.ofCusp E a)) ((Submodule.comap_mono hU).trans hz) st.ρ st.σ st.τ
  have hUe : (U.comap (UpperTheory.V.Cm.ofCusp E a)).map (UpperTheory.V.Cm.ofCusp E a) = U :=
    Submodule.map_comap_eq_self (hU.trans hr)
  have hD : _root_.GlobalTheory.CuspRep.IsStable (D.map (UpperTheory.V.Cm.ofCusp E a)) := UpperTheory.V.Cm.isStable_map ⟨d2, d3, d4⟩
  refine ⟨D.map (UpperTheory.V.Cm.ofCusp E a) ⊓ C, inf_le_right, fun o φ h => ⟨hD o φ h.1, hs o φ h.2⟩, ?_, ?_⟩
  · rw [← inf_assoc, ← hUe, ← Submodule.map_inf _ UpperTheory.V.Cm.ofCusp_injective, d5, Submodule.map_bot, bot_inf_eq]
  · rw [← sup_inf_assoc_of_le _ hU, inf_eq_right, ← hUe, ← Submodule.map_sup, d6]
    exact (Submodule.map_comap_eq_self hr).ge.trans (Submodule.map_mono hz)

end

theorem UpperTheory.V.Cj.S.ciCompl :
    UpperTheory.V.Cj.S.CiBasic → UpperTheory.V.Cj.S.CiCompl := by
  intro hb E _ _ _ a ha m U hU hsU
  obtain ⟨hs, c, hc⟩ := hb E a m
  obtain ⟨χ, hχ⟩ := exists_twist (E := E) ha c
  obtain ⟨D, d1, d2, d3, d4⟩ := compl_zero (C := (CI a m).map (mulChi a χ).toLinearMap)
    (by rintro _ ⟨φ, h, rfl⟩; exact (mem_CI.1 h).1.mulChi χ)
    (by
      rintro _ ⟨φ, h, rfl⟩
      rw [LinearEquiv.coe_coe, lie_mulChi, hc φ h, hχ, neg_smul, add_neg_cancel, map_zero])
    (stable_twist χ hs) (Submodule.map_mono hU) (stable_twist χ hsU)
  refine ⟨D.map (mulChi a χ⁻¹).toLinearMap, (Submodule.map_mono d1).trans (map_twist_inv χ _).le,
    stable_twist _ d2, ?_, ?_⟩
  · rw [← map_twist_inv χ U, ← Submodule.map_inf _ (mulChi a χ⁻¹).injective, d3, Submodule.map_bot]
  · rw [← map_twist_inv χ U, ← Submodule.map_sup, d4, map_twist_inv]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CtCap
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.ctCap :
    UpperTheory.V.Cj.S.CtCap := by
  intro E _ _ _ n r φ hφ
  have ha := (UpperTheory.V.Cm.isAutForm_iff φ).1 hφ
  obtain ⟨f, hf, hfu⟩ := UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping E n r
  let φ' : GroundTheory.Automorphic.AutomorphicForm.automorphicForms E n := ⟨φ.1, ha⟩
  refine ⟨(UpperTheory.V.Cm.smEq E n).symm (f φ'), hf φ', fun X g => ?_, fun t u => ?_⟩
  · rw [UpperTheory.V.Cm.coe_smEq_symm, hf]
    exact UpperTheory.constantTerm_unipotent_left_invariant E n r φ.1 ha.isLeftInvariant X g
  · obtain ⟨p, -, q, -, e⟩ := UpperTheory.V.Cm.mem_Zalg_iff.1 (UpperTheory.V.Cm.cap_mem_Zalg (a := n) t u)
    have h := hf (GroundTheory.Automorphic.AutomorphicForm.uActionAF E n p φ' +
      Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E n q φ')
    rw [map_add (f := _), map_smul, hfu, hfu] at h
    rw [e]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CtSat
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.ctSat :
    UpperTheory.V.Cj.S.CtSat := by
  intro E _ _ _ n r φ ψ hφ hψ h0 w B hB
  let C : Submodule ℂ (Sm E n) :=
    { carrier := {f | Continuous f.1}
      add_mem' := fun h h' => Continuous.add h h'
      zero_mem' := continuous_const
      smul_mem' := fun c _ h => Continuous.const_smul h c }
  have hC : ∀ g, ∀ f ∈ C, fL n w g f ∈ C := fun g f hf =>
    show Continuous fun x => f.1 (x * finGL E n (locGL E n w g)) from
      Continuous.comp (show Continuous f.1 from hf) (continuous_id.mul continuous_const)
  have hc : φ ∈ C := ((UpperTheory.V.Cm.isAutForm_iff φ).1 hφ).continuous
  let F : C →ₗ[ℂ] (GA E n → ℂ) :=
    { toFun := fun f => constantTerm r f.1.1
      map_add' := fun f f' => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_add f.2 f'.2 g
      map_smul' := fun c f => funext fun g => GroundTheory.Automorphic.AutomorphicForm.constantTerm_smul c f.1.1 g }
  have h1 : IsSatVecGL w (GlobalTheory.PRep.sub (fL n w) C hC) ⟨φ, hc⟩ B :=
    IsSatVecGL.of_map C.subtype (fun _ _ => rfl) Subtype.val_injective hB
  have hF : F ⟨φ, hc⟩ = ψ.1 := hψ.symm
  have h2 := h1.map (ρ' := (GlobalTheory.PRep.rightReg ℂ (GA E n) ℂ).comp ((finGL E n).comp (locGL E n w))) F
    (fun g f => funext fun x =>
      GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate f.1.1 (finGL E n (locGL E n w g)) x)
    (by rw [hF]; exact fun h => h0 (Subtype.ext h))
  rw [hF] at h2
  exact IsSatVecGL.of_map (Sm E n).subtype (fun _ _ => rfl) Subtype.val_injective h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspProj
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem exists_minimal_compl {M O : Type*} [AddCommGroup M] [Module ℂ M] (act : O → Module.End ℂ M)
    (C : Submodule ℂ M) (hC : ∀ o, ∀ x ∈ C, act o x ∈ C)
    (hc : ∀ U ≤ C, (∀ o, ∀ x ∈ U, act o x ∈ U) →
      ∃ D ≤ C, (∀ o, ∀ x ∈ D, act o x ∈ D) ∧ U ⊓ D = ⊥ ∧ U ⊔ D = C) {φ : M} (hφ : φ ∈ C) (h0 : φ ≠ 0) :
    ∃ V D : Submodule ℂ M, V ≤ C ∧ D ≤ C ∧ (∀ o, ∀ x ∈ V, act o x ∈ V) ∧ V ≠ ⊥ ∧
      (∀ W ≤ V, (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V) ∧ (∀ o, ∀ x ∈ D, act o x ∈ D) ∧
      V ⊓ D = ⊥ ∧ V ⊔ D = C ∧ φ ∉ D := by
  let U : Submodule ℂ M := sInf {W | φ ∈ W ∧ ∀ o, ∀ x ∈ W, act o x ∈ W}
  have hUC : U ≤ C := sInf_le ⟨hφ, hC⟩
  have hφU : φ ∈ U := Submodule.mem_sInf.2 fun W hW => hW.1
  have hUs : ∀ o, ∀ x ∈ U, act o x ∈ U := fun o x hx =>
    Submodule.mem_sInf.2 fun W hW => hW.2 o x (Submodule.mem_sInf.1 hx W hW)
  have hle := UpperTheory.V.TR.SS.le_sSup_minimal act U hUs fun W hW hs => by
    obtain ⟨D, -, d2, d3, d4⟩ := hc W (hW.trans hUC) hs
    refine ⟨D ⊓ U, inf_le_right, fun o x hx => ⟨d2 o x hx.1, hUs o x hx.2⟩, ?_, ?_⟩
    · rw [← inf_assoc, d3, bot_inf_eq]
    · rw [← sup_inf_assoc_of_le _ hW, d4, inf_eq_right.2 hUC]
  by_contra hn
  refine h0 ((Submodule.mem_bot ℂ).1 ((hle.trans (sSup_le ?_)) hφU))
  rintro V ⟨v1, v2, v3, v4⟩
  obtain ⟨D, d1, d2, d3, d4⟩ := hc V (v1.trans hUC) v2
  by_cases hD : φ ∈ D
  · rw [← d3]
    exact le_inf le_rfl (v1.trans (sInf_le ⟨hD, d2⟩))
  · exact absurd ⟨V, D, v1.trans hUC, d1, v2, v3, v4, d2, d3, d4, hD⟩ hn

private theorem exists_proj {M : Type*} [AddCommGroup M] [Module ℂ M] {C V D : Submodule ℂ M} (hV : V ≤ C) (hD : D ≤ C)
    (h1 : V ⊓ D = ⊥) (h2 : V ⊔ D = C) :
    ∃ p : C →ₗ[ℂ] V, (∀ x : C, x.1 - (p x).1 ∈ D) ∧ ∀ (x : C) (v : V), x.1 - v.1 ∈ D → p x = v := by
  have hc : IsCompl (V.comap C.subtype) (D.comap C.subtype) := by
    constructor
    · rw [disjoint_iff, ← Submodule.comap_inf, h1, Submodule.comap_bot, Submodule.ker_subtype]
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.1 (h2.ge hx)
      exact Submodule.mem_sup.2 ⟨⟨v, hV hv⟩, hv, ⟨d, hD hd⟩, hd, rfl⟩
  let p : C →ₗ[ℂ] V := (Submodule.comapSubtypeEquivOfLe hV).toLinearMap ∘ₗ Submodule.projectionOnto _ _ hc
  have hp : ∀ x : C, x.1 - (p x).1 ∈ D := fun x => by
    obtain ⟨v, hv, d, hd, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top.ge (Submodule.mem_top (x := x)))
    have e1 : Submodule.projectionOnto _ _ hc v = ⟨v, hv⟩ := Submodule.projectionOnto_apply_left hc ⟨v, hv⟩
    have e2 : Submodule.projectionOnto _ _ hc d = 0 := Submodule.projectionOnto_apply_right hc ⟨d, hd⟩
    have : (p (v + d)).1 = v.1 := by
      simp only [p, LinearMap.comp_apply, map_add (f := _), e1, e2, map_zero, add_zero]
      rfl
    rw [this]
    simpa using hd
  refine ⟨p, hp, fun x v h => Subtype.ext (sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 (h1.le ⟨V.sub_mem (p x).2 v.2, ?_⟩)))⟩
  have := D.sub_mem h (hp x)
  rwa [sub_sub_sub_cancel_left] at this

theorem UpperTheory.V.Cj.S.cuspProj :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.CiBasic → UpperTheory.V.Cj.S.CiCompl → UpperTheory.V.Cj.S.CuspProj := by
  intro _ hb hc E _ _ _ a ha m hm φ h0
  obtain ⟨V, D, v1, d1, v2, v3, v4, d2, h1, h2, hφ⟩ :=
    exists_minimal_compl act (CI a m) (hb E a m).1 (hc E a ha m) φ.2 fun h => h0 (Subtype.ext h)
  obtain ⟨p, p1, p2⟩ := exists_proj v1 d1 h1 h2
  refine ⟨⟨V, fun ψ hψ => (mem_CI.1 (v1 hψ)).1, v2, v3, v4⟩, fun t => ⟨hm t, fun u ψ hψ => (mem_CI.1 (v1 hψ)).2 t u⟩,
    p, fun h => hφ ?_, fun g x y hy => p2 _ _ ?_⟩
  · simpa [h] using p1 φ
  · have := d2 (.fin g) _ (p1 x)
    rw [map_sub] at this
    rw [hy]
    exact this
end

