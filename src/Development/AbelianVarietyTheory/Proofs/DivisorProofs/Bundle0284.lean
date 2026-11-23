module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0109
public import Formalism.FormalDegreeBessel.StatementDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.BlockAnti

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterTwistedHarishChandraInduct
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section
namespace GlobalTheory.Shin.HatInd

theorem inPar_gal {F' : Type} [Field F'] (u : F' →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F') :
    InPar a (gal u n x) ↔ InPar a x := by
  unfold InPar gal
  simp only [Matrix.GeneralLinearGroup.map_apply, map_eq_zero]

theorem par_facts {F' : Type} [Field F'] (a b n : ℕ) (h : n = a + b) :
    (∀ x y : GL (Fin n) F', InPar a x → InPar a y → InPar a (x * y)) ∧ InPar a (1 : GL (Fin n) F') ∧
    (∀ x : GL (Fin n) F', InPar a x → InPar a x⁻¹) ∧
    (∀ x y : GL (Fin n) F', InPar a x → InPar a y → tlG a (x * y) = tlG a x * tlG a y) ∧
    (∀ x : GL (Fin n) F', InPar a x →
      ((tlG a x : GL (Fin a) F') : Matrix (Fin a) (Fin a) F') = tl a (x : Matrix (Fin n) (Fin n) F')) := by
  obtain ⟨H, π, hH, -, hπ, hmat, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n h
  refine ⟨fun x y hx hy => (hH _).1 (H.mul_mem ((hH x).2 hx) ((hH y).2 hy)), (hH 1).1 H.one_mem,
    fun x hx => (hH _).1 (H.inv_mem ((hH x).2 hx)), fun x y hx hy => ?_, fun x hx => ?_⟩
  · have := π.map_mul ⟨x, (hH x).2 hx⟩ ⟨y, (hH y).2 hy⟩
    rw [hπ, hπ, hπ] at this
    exact congrArg Prod.fst this
  · have := (hmat ⟨x, (hH x).2 hx⟩).1
    rw [hπ] at this
    exact this

theorem tlG_gal {F' : Type} [Field F'] (u : F' →+* F') (a b n : ℕ) (h : n = a + b) (x : GL (Fin n) F')
    (hx : InPar a x) : tlG a (gal u n x) = gal u a (tlG a x) := by
  have hm := (par_facts (F' := F') a b n h).2.2.2.2
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [hm _ ((inPar_gal u a x).2 hx)]
  unfold gal
  rw [Matrix.GeneralLinearGroup.map_apply, hm _ hx]
  unfold tl ent
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map_apply]

theorem finite_gal (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Finite (F' ≃ₐ[F] F') :=
  Finite.of_injective (fun e : F' ≃ₐ[F] F' => (e : F' → F')) (fun _ _ h => AlgEquiv.ext (congrFun h))

theorem galAct_symm {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (u : F' ≃ₐ[F] F')
    (x : GL (Fin n) F') : (galAct F F' n u).symm x = gal ((u⁻¹ : F' ≃ₐ[F] F') : F' →+* F') n x := rfl

theorem hat_ind : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (a b n : ℕ), n = a + b →
    ∀ X ∈ Virt ℂ ℂ (GHat F F' a), ∃ Z ∈ Virt ℂ ℂ (GHat F F' n), ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'),
      Z (inl δ * inr t) = hcTw (t : F' →+* F') a b (fun d => X (inl d * inr t)) (fun _ => 1) n δ := by
  intro F F' _ _ _ _ a b n hn X hX
  haveI : Finite (F' ≃ₐ[F] F') := finite_gal F F'
  haveI : Finite (GHat F F' n) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI : Finite (GHat F F' a) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  obtain ⟨hmul, hone, hinv, htl, -⟩ := par_facts (F' := F') a b n hn
  let P : Subgroup (GHat F F' n) :=
    { carrier := {x | InPar a x.left}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, mul_left, galAct_apply] at hx hy ⊢
        exact hmul _ _ hx ((inPar_gal _ a _).2 hy)
      one_mem' := by simpa using hone
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, inv_left, galAct_apply] at hx ⊢
        exact (inPar_gal _ a _).2 (hinv _ hx) }
  have hP : ∀ x : GHat F F' n, x ∈ P ↔ InPar a x.left := fun _ => Iff.rfl
  let πh : P →* GHat F F' a := MonoidHom.mk' (fun p => (⟨tlG a p.1.left, p.1.right⟩ : GHat F F' a))
    (fun p q => by
      have hp := (hP _).1 p.2
      have hq := (hP _).1 q.2
      apply SemidirectProduct.ext
      · simp only [Subgroup.coe_mul, mul_left, galAct_apply]
        rw [htl _ _ hp ((inPar_gal _ a _).2 hq), tlG_gal _ a b n hn _ hq]
      · simp)
  have hcl := (virt_mul_comap_conj_ind_linear (GHat F F' a)).2.2.1 X hX
  set ψ : P → ℂ := fun p => X (πh p) with hψ
  refine ⟨ind P ψ, (virt_mul_comap_conj_ind_linear (GHat F F' n)).2.2.2.1 P ψ
    ((virt_mul_comap_conj_ind_linear (GHat F F' a)).2.1 X hX P πh), fun t δ => ?_⟩

  have key : ∀ (w : GHat F F' n) (u : F' ≃ₐ[F] F'), ext0 P ψ ((inr u)⁻¹ * w * inr u) = ext0 P ψ w := by
    intro w u
    have hl : ((inr u)⁻¹ * w * inr u).left = gal ((u⁻¹ : F' ≃ₐ[F] F') : F' →+* F') n w.left := by
      simp [mul_left, galAct_apply, galAct_symm]
    have hr : ((inr u)⁻¹ * w * inr u).right = u⁻¹ * w.right * u := by simp
    unfold ext0
    by_cases hw : InPar a w.left
    · have hw' : (inr u)⁻¹ * w * inr u ∈ P := by rw [hP, hl]; exact (inPar_gal _ a _).2 hw
      rw [dite_eq_left hw', dite_eq_left ((hP w).2 hw)]
      simp only [hψ]
      have : πh ⟨(inr u)⁻¹ * w * inr u, hw'⟩ = (inr u)⁻¹ * πh ⟨w, (hP w).2 hw⟩ * inr u := by
        apply SemidirectProduct.ext
        · change tlG a ((inr u)⁻¹ * w * inr u).left = _
          rw [hl, tlG_gal _ a b n hn _ hw]
          simp [MonoidHom.mk'_apply, mul_left, galAct_apply, galAct_symm, πh]
        · change ((inr u)⁻¹ * w * inr u).right = _
          rw [hr]
          simp [MonoidHom.mk'_apply, πh]
      rw [this]
      have := hcl (πh ⟨w, (hP w).2 hw⟩) (inr u)
      simpa using this
    · have hw' : (inr u)⁻¹ * w * inr u ∉ P := by
        rw [hP, hl]; exact fun h => hw ((inPar_gal _ a _).1 h)
      rw [dite_eq_right hw', dite_eq_right (fun h => hw ((hP w).1 h))]
  haveI : Fintype (GHat F F' n) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin n) F') := Fintype.ofFinite _
  haveI : Fintype (F' ≃ₐ[F] F') := Fintype.ofFinite _
  set g : GHat F F' n := inl δ * inr t with hg
  have hval : ∀ y : GL (Fin n) F', ext0 P ψ ((inl y)⁻¹ * g * inl y) =
      if InPar a (y⁻¹ * δ * gal (t : F' →+* F') n y) then
        X (inl (tlG a (y⁻¹ * δ * gal (t : F' →+* F') n y)) * inr t) * 1 else 0 := by
    intro y
    have hl : ((inl y)⁻¹ * g * inl y).left = y⁻¹ * δ * gal (t : F' →+* F') n y := by
      simp [hg, mul_left, galAct_apply]
    have hr : ((inl y)⁻¹ * g * inl y).right = t := by simp [hg]
    unfold ext0
    by_cases hw : InPar a (y⁻¹ * δ * gal (t : F' →+* F') n y)
    · rw [dite_eq_left (by rw [hP, hl]; exact hw), if_pos hw, mul_one]
      simp only [hψ]
      congr 1
      apply SemidirectProduct.ext
      · change tlG a ((inl y)⁻¹ * g * inl y).left = _
        rw [hl]; simp
      · change ((inl y)⁻¹ * g * inl y).right = _
        rw [hr]; simp
    · rw [dite_eq_right (by rw [hP, hl]; exact hw), if_neg hw]
  have hz : ∀ (y : GL (Fin n) F') (u : F' ≃ₐ[F] F'),
      ((SemidirectProduct.equivProd (φ := galAct F F' n)).symm (y, u)) = inl y * inr u := by
    intro y u
    apply SemidirectProduct.ext <;> simp [SemidirectProduct.equivProd]
  have hsum : ∑ᶠ z : GHat F F' n, ext0 P ψ (z⁻¹ * g * z) =
      (Nat.card (F' ≃ₐ[F] F') : ℂ) * ∑ᶠ y : GL (Fin n) F', ext0 P ψ ((inl y)⁻¹ * g * inl y) := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← (SemidirectProduct.equivProd (φ := galAct F F' n)).symm.sum_comp, Fintype.sum_prod_type,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ∀ u : F' ≃ₐ[F] F', ext0 P ψ ((inl y * inr u)⁻¹ * g * (inl y * inr u)) =
        ext0 P ψ ((inl y)⁻¹ * g * inl y) := by
      intro u
      have e : (inl y * inr u)⁻¹ * g * (inl y * inr u) = (inr u)⁻¹ * ((inl y)⁻¹ * g * inl y) * inr u := by
        simp only [mul_inv_rev, mul_assoc]
      rw [e, key]
    simp only [hz, this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hcard : Nat.card P = Nat.card {p : GL (Fin n) F' // InPar a p} * Nat.card (F' ≃ₐ[F] F') := by
    rw [← Nat.card_prod]
    exact Nat.card_congr
      { toFun := fun p => (⟨p.1.left, p.2⟩, p.1.right)
        invFun := fun q => ⟨⟨q.1.1, q.2⟩, q.1.2⟩
        left_inv := fun p => rfl
        right_inv := fun q => rfl }
  have hB : (Nat.card (F' ≃ₐ[F] F') : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := F' ≃ₐ[F] F')).ne'
  unfold ind hcTw
  rw [hcard, hsum]
  simp only [hval]
  push_cast
  rw [mul_inv, mul_assoc, ← mul_assoc _ (Nat.card (F' ≃ₐ[F] F') : ℂ), inv_mul_cancel₀ hB, one_mul]

end GlobalTheory.Shin.HatInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpace
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_rfl' (a b : ℕ) : stdSum (rfl : a + b = a + b) = finSumFinEquiv := by
  ext x; simp [stdSum]

theorem X0_mul_invT_parab (a b : ℕ) (p : parab k (blocks a b)) :
    (X0 (k := k) (finSumFinEquiv (m := a) (n := b)) * (invT (p : GL (Fin (a + b)) k)).val :
      Matrix (Fin a) (Fin (a + b)) k) =
      ((invT (leviProj k (blocks a b) p false)).val : Matrix (Fin a) (Fin a) k) *
        X0 (k := k) (finSumFinEquiv (m := a) (n := b)) := by
  have hA : (invT (leviProj k (blocks a b) p false)).val
      = ((leviProj k (blocks a b) p⁻¹ false : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)ᵀ := by
    rw [invT_val, map_inv]; rfl
  refine Matrix.ext fun i j => ?_
  rw [frameMatrixFirstColumnBlock_mul_apply, invT_val, hA]
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with j | j
  · have := leviProj_apply k (blocks a b) p⁻¹ false j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this]
  · have hne : ∀ (i : Fin a), Fin.castAdd b i ≠ Fin.natAdd a j := fun i h => by
      have := congrArg Fin.val h; simp at this; omega
    have := (mem_parab_two k).1 (p⁻¹).2 j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this, hne]

variable [MeasurableSpace k] [BorelSpace k]

theorem fibre_mem_indSpace (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ) :
    fibre ν β a b Φ ∈ indSpace (parab k (blocks a b)) (ofChar (parChar ν β a b)) := by
  intro p x
  rw [ofChar_apply]
  set A : GL (Fin a) k := leviProj k (blocks a b) p false with hAdef
  set D := leviProj k (blocks a b) p true with hDdef
  set Ψ := omA ν β 1 x Φ with hΨ
  set z : ℂ := ((a + b : ℕ) : ℂ) / 2 with hz
  let X : Matrix (Fin a) (Fin (a + b)) k := X0 (k := k) finSumFinEquiv
  set F : GL (Fin a) k → ℂ := fun g => Ψ (g.val * X) * (ν (gdet g) : ℂ) *
    apow (gdet g) z with hF
  set c : ℂ := (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) *
    ν (gdet A) * apow (gdet A) z with hc
  have h1 : omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ = omA ν β 1 ↑p Ψ := by rw [hΨ, ← omA_mul, one_mul]
  have h2 : ∀ Y, omA ν β 1 (↑p : GL (Fin (a + b)) k) Ψ Y =
      (β (gdet (p : GL (Fin (a + b)) k)) : ℂ) * apow (gdet (p : GL (Fin (a + b)) k)) (-(a : ℂ) / 2) *
        Ψ (Y * (invT (p : GL (Fin (a + b)) k)).val) := by
    intro Y
    simp [omA]
  have hm : ∀ g : GL (Fin a) k,
      (g.val * X) * (invT (p : GL (Fin (a + b)) k)).val = (g * invT A).val * X := by
    intro g
    rw [Matrix.mul_assoc, X0_mul_invT_parab, ← Matrix.mul_assoc, ← Units.val_mul]
  have key : ∀ g : GL (Fin a) k, omA ν β 1 ((p : GL (Fin (a + b)) k) * x) Φ (g.val * X) * (ν (gdet g) : ℂ) *
      apow (gdet g) z = c * F (g * invT A) := by
    intro g
    rw [h1, h2, hm g]
    simp only [hF, hc, gdet_mul, gdet_invT, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, apow_mul,
      apow_inv, apow_neg]
    have n1 : (ν (gdet A) : ℂ) ≠ 0 := Units.ne_zero _
    have n2 : apow (gdet A) z ≠ 0 := apow_ne_zero _ _
    field_simp
  have hdet : gdet (p : GL (Fin (a + b)) k) = gdet A * gdet D := by
    have := det_parab k (blocks a b) p
    rw [Fintype.prod_bool] at this
    exact this.trans (mul_comm _ _)
  have hL : leviProj k (blocks a b) p = leviTwo k (Fin a) (Fin b) (A, D) := by
    funext t; cases t <;> rfl
  have hab : ∀ (s : ℂ) (y : kˣ), ((absPow k s y : ℂˣ) : ℂ) = apow y s := fun _ _ => rfl
  have hchar : ((parChar ν β a b p : ℂˣ) : ℂ) = c := by
    simp only [parChar, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul, hL,
      MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulEquiv.symm_apply_apply, deltaHalf_two,
      MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply, hab, Fintype.card_fin]
    have e : apow (gdet A) z * apow (gdet A) (-(a : ℂ) / 2) = apow (gdet A) ((b : ℂ) / 2) := by
      rw [← apow_add, hz]; congr 1; push_cast; ring
    rw [hc, hdet, map_mul, Units.val_mul, apow_mul]
    rw [← e]
    ring
  rw [hchar]
  have I1 : fibre ν β a b Φ ((p : GL (Fin (a + b)) k) * x) =
      ∫ g, c * F (g * invT A) ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    integral_congr_ae (Filter.Eventually.of_forall key)
  have I2 : fibre ν β a b Φ x = ∫ g, F g ∂(haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) := rfl
  rw [I1, I2, integral_const_mul, integral_mul_right_eq_self F (invT A)]

end GlobalTheory.RankFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCompactFixedVectorsPiTensorSmoo
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.PiTensorFixed

variable {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

theorem exists_fixed_tprod (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a))) (v : ∀ a, X a) :
    ∃ u : ∀ a, X a, (∀ a, u a ∈ fixed (ρ a) (K a)) ∧
      (twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1).mkQ (PiTensorProduct.tprod ℂ u) =
        (twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1).mkQ (PiTensorProduct.tprod ℂ v) := by
  classical
  haveI := Fintype.ofFinite α
  set N := twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1
  have key : ∀ S : Finset α, ∃ u : ∀ a, X a, (∀ a ∈ S, u a ∈ fixed (ρ a) (K a)) ∧
      N.mkQ (PiTensorProduct.tprod ℂ u) = N.mkQ (PiTensorProduct.tprod ℂ v) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨v, by simp, rfl⟩
    | insert a S ha ih =>
      obtain ⟨u, hu, e⟩ := ih
      let f : X a →ₗ[ℂ] _ := N.mkQ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap u a
      obtain ⟨y, hy, hfy⟩ := IwahoriOnto.exists_fixed_map_eq (hρ a) (hK a) f (u a) fun h hh => by
        simp only [f, LinearMap.comp_apply, MultilinearMap.toLinearMap_apply, Submodule.mkQ_apply,
          Function.update_eq_self]
        rw [Submodule.Quotient.eq]
        refine Submodule.subset_span ⟨⟨Pi.mulSingle a h, fun b _ => ?_⟩, PiTensorProduct.tprod ℂ u, ?_⟩
        · by_cases hb : b = a
          · subst hb; simpa using hh
          · simp [Pi.mulSingle_eq_of_ne hb]
        · have : (fun b => ρ b (Pi.mulSingle (M := Γ) a h b) (u b)) = Function.update u a (ρ a h (u a)) := by
            funext b
            by_cases hb : b = a
            · subst hb; simp
            · simp [Pi.mulSingle_eq_of_ne hb, Function.update_of_ne hb]
          simp [this]
      refine ⟨Function.update u a y, fun b hb => ?_, ?_⟩
      · by_cases hba : b = a
        · subst hba; simpa using hy
        · rw [Function.update_of_ne hba]
          exact hu b ((Finset.mem_insert.1 hb).resolve_left hba)
      · rw [← e]
        simpa [f] using hfy
  obtain ⟨u, hu, e⟩ := key Finset.univ
  exact ⟨u, fun a => hu a (Finset.mem_univ a), e⟩

theorem fixed_le_range (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (hρ : ∀ a, IsSmooth (ρ a))
    (K : ∀ a, Subgroup (Γ a)) (hK : ∀ a, IsCompact (K a : Set (Γ a))) :
    fixed (piTensor ρ) (Subgroup.pi Set.univ K) ≤
      LinearMap.range (PiTensorProduct.map fun a => (fixed (ρ a) (K a)).subtype) := by
  set N := twKer (piTensor ρ) (Subgroup.pi Set.univ K) 1
  set R := LinearMap.range (PiTensorProduct.map fun a => (fixed (ρ a) (K a)).subtype)
  have hR : R ≤ fixed (piTensor ρ) (Subgroup.pi Set.univ K) := by
    rintro _ ⟨x, rfl⟩
    induction x using PiTensorProduct.induction_on with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | smul_tprod c x =>
      rw [map_smul]
      refine Submodule.smul_mem _ c (ContraRefl.mem_fix.2 fun h hh => ?_)
      rw [PiTensorProduct.map_tprod, piTensor_tprod]
      congr 1
      funext a
      exact ContraRefl.mem_fix.1 (x a).2 _ (hh a trivial)
  have hall : ∀ w, ∃ r ∈ R, N.mkQ r = N.mkQ w := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | add x y hx hy =>
      obtain ⟨r, hr, e⟩ := hx
      obtain ⟨s, hs, e'⟩ := hy
      exact ⟨r + s, add_mem hr hs, by rw [map_add (f := _), map_add (f := _), e, e']⟩
    | smul_tprod c x =>
      obtain ⟨u, hu, e⟩ := exists_fixed_tprod ρ hρ K hK x
      refine ⟨c • PiTensorProduct.tprod ℂ u, Submodule.smul_mem _ c
        ⟨PiTensorProduct.tprod ℂ fun a => ⟨u a, hu a⟩, by simp⟩, ?_⟩
      rw [map_smul, map_smul, e]
  intro w hw
  obtain ⟨r, hr, e⟩ := hall w
  have h0 : r - w = 0 := ContraRefl.eq_zero_of_fixed_twKer (isSmooth_piTensor hρ)
    (isCompact_univ_pi hK) (sub_mem (hR hr) hw) ((Submodule.Quotient.eq N).1 e)
  rw [← sub_eq_zero.1 h0]
  exact hr

theorem finiteDimensional_fixed_piTensor : ∀ {α : Type} [Finite α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)] [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)), (∀ a, IsSmooth (ρ a)) → ∀ (K : ∀ a, Subgroup (Γ a)), (∀ a, IsCompact (K a : Set (Γ a))) → (∀ a, FiniteDimensional ℂ (fixed (ρ a) (K a))) → FiniteDimensional ℂ (fixed (piTensor ρ) (Subgroup.pi Set.univ K)) := by
  intro α _ Γ X _ _ _ _ _ ρ hρ K hK hfin
  exact Submodule.finiteDimensional_of_le (fixed_le_range ρ hρ K hK)

end GlobalTheory.PiTensorFixed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLengthCokerOfEtalePuncturedSpectrum
section
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] [Module.Finite R B], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B)) → ∀ ψ : A →ₐ[R] B, Function.Injective ψ → (∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ ψ.range := by
  intro R _ _ _ _ A B _ _ _ _ _ _ hA hB ψ hψ ⟨s, hs, hsb⟩
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.smul_mem_of_maximalIdeal_pow_of_locally_eq R B (ψ.range.toSubmodule.restrictScalars R) (fun p hp hpm => by
    haveI := hp
    haveI := hA p hpm
    haveI := hB p hpm
    let S := Localization.AtPrime p
    haveI : Module.Free S (S ⊗[R] A) := Module.free_of_flat_of_isLocalRing
    haveI : Module.Free S (S ⊗[R] B) := Module.free_of_flat_of_isLocalRing
    obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.localization_map_injective_coker_killed R A B p ψ hψ s hs hsb
    have htr := GlobalTheory.T.algebra_trace_map_of_cokernel_killed_by_scalar S _ _ _ h1 _ h2 h3
    exact GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map R A B p ψ (GlobalTheory.T.surjective_of_injective_of_trace_eq_of_smul_mem_range S _ _ _ h1 _ h2 h3 htr))
  exact ⟨k, fun x hx b => hk x hx b⟩

end GlobalTheory.EtaleCoker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapConditionsOfLargeGaps
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap

namespace GlobalTheory.PsCo.PcEG

def GapNum : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ),
    (∀ i j : Fin r, (j : ℕ) = i + 1 → 100 * (r : ℤ) ^ 4 ≤ lam i - lam j) →
    Formalism.QuantumDeterminants.IsHCParam (fun a => (lam a : ℝ)) ∧ StdGap ε (fun a => (lam a : ℝ)) ∧ Gap3 ε (fun a => (lam a : ℝ)) ∧
      ∃ h : ℝ, GapAtLeast ε (fun a => (lam a : ℝ)) h ∧ thrStar ε < h

end GlobalTheory.PsCo.PcEG

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG (GapNum)

namespace GapNumber

theorem chain {r : ℕ} {lam : Fin r → ℤ} {H : ℤ} (hH : 0 ≤ H)
    (hg : ∀ i j : Fin r, (j : ℕ) = i + 1 → H ≤ lam i - lam j) :
    ∀ i j : Fin r, i < j → H ≤ lam i - lam j := by
  suffices h : ∀ (k : ℕ) (i j : Fin r), (j : ℕ) = i + k + 1 → H ≤ lam i - lam j by
    intro i j hij
    have : (i : ℕ) < j := hij
    exact h ((j : ℕ) - i - 1) i j (by omega)
  intro k
  induction k with
  | zero => intro i j h; exact hg i j (by omega)
  | succ k ih =>
    intro i j h
    have hm : (i : ℕ) + k + 1 < r := by have := j.isLt; omega
    have h1 := ih i ⟨(i : ℕ) + k + 1, hm⟩ rfl
    have h2 := hg ⟨(i : ℕ) + k + 1, hm⟩ j (by show (j : ℕ) = (i : ℕ) + k + 1 + 1; omega)
    linarith

end GapNumber

theorem gapConditions_of_largeGaps : GapNum := by
  intro r hr ε lam hg
  obtain ⟨k, hk⟩ := hr
  have hr1 : 1 ≤ r := by omega
  have hH : (0 : ℤ) ≤ 100 * (r : ℤ) ^ 4 := by positivity
  have hc := GapNumber.chain hH hg
  have hcR : ∀ i j : Fin r, i < j → 100 * (r : ℝ) ^ 4 ≤ (lam i : ℝ) - lam j := fun i j h => by
    exact_mod_cast hc i j h
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hpos : (0 : ℝ) < 100 * (r : ℝ) ^ 4 := by positivity
  have hanti : StrictAnti (fun a => (lam a : ℝ)) := fun i j h => by
    have := hcR i j h
    show (lam j : ℝ) < lam i
    linarith
  have hgap : GapAtLeast ε (fun a => (lam a : ℝ)) (100 * (r : ℝ) ^ 4) := by
    intro a b hab
    have hne : a ≠ b := fun h => hab (h ▸ rfl)
    show 100 * (r : ℝ) ^ 4 ≤ |(lam a : ℝ) - lam b|
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hcR a b h).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hcR b a h).trans (le_abs_self _)
  have hp : pOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq : qOf ε ≤ r := (Finset.card_filter_le _ _).trans_eq (by simp)
  have hq0 : S7.q0 ε ≤ r := (min_le_left _ _).trans hp
  have hpR : (pOf ε : ℝ) ≤ r := by exact_mod_cast hp
  have hqR : (qOf ε : ℝ) ≤ r := by exact_mod_cast hq
  have hq0R : (S7.q0 ε : ℝ) ≤ r := by exact_mod_cast hq0
  have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hrR
  have h4 : (r : ℝ) ≤ (r : ℝ) ^ 4 := le_self_pow₀ hrR (by norm_num)
  have h2 : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have h3 : (r : ℝ) ^ 3 ≤ (r : ℝ) ^ 4 := pow_le_pow_right₀ hrR (by norm_num)
  have hbig : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < 100 * (r : ℝ) ^ 4 := by
    have : (r : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤ r * r * r := by gcongr
    nlinarith
  refine ⟨⟨hanti, fun a => ⟨lam a - k, ?_⟩⟩, ⟨hanti, _, hgap, hbig⟩, ⟨hanti, _, hgap, by linarith⟩, _, hgap, ?_⟩
  · have hkR : (r : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    show (lam a : ℝ) - ((r : ℝ) - 1) / 2 = ((lam a - k : ℤ) : ℝ)
    rw [hkR]; push_cast; ring
  · unfold thrStar
    refine max_lt hbig ?_
    have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * r := by
      rw [show (2 : ℝ) * r = Real.sqrt ((2 * r) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hm : (r : ℝ) * (S7.q0 ε : ℝ) ≤ r * r := mul_le_mul_of_nonneg_left hq0R (by positivity)
    nlinarith

end GlobalTheory.PsCo.PcEF

end
end

