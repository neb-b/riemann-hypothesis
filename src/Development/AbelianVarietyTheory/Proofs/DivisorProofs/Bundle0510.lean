module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0497

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftHarishChandraInductionEqTwisted
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.LiftHc

theorem galAct_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (n : ℕ) (t : F' ≃ₐ[F] F')
    (x : GL (Fin n) F) : galAct F F' n t (incl F F' n x) = incl F F' n x := by
  ext i j; simp [galAct_apply, gal, incl]

theorem inPar_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (x : GL (Fin n) F) :
    InPar a (incl F F' n x) ↔ InPar a x := by
  simp [InPar, incl, gal]

theorem inPar_gal {F : Type} [Field F] (t : F →+* F) (a n : ℕ) (x : GL (Fin n) F) (hx : InPar a x) :
    InPar a (gal t n x) := by
  intro i j hj hi; simp [gal, hx i j hj hi]

theorem gal_id {F : Type} [Field F] (n : ℕ) (x : GL (Fin n) F) : gal (RingHom.id F) n x = x := by
  ext i j; simp [gal]

theorem nrm_conj_incl {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (y₀ : GL (Fin n) F) :
    nrm s ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) = (incl F F' n y₀)⁻¹ * nrm s δ * incl F F' n y₀ := by
  unfold nrm nrmG
  set c := incl F F' n y₀
  set L := List.range (Module.finrank F F')
  have h : ∀ i : ℕ, galAct F F' n (s ^ i) (c⁻¹ * δ * c) =
      MulAut.conj c⁻¹ (galAct F F' n (s ^ i) δ) := by
    intro i
    rw [map_mul, map_mul, map_inv, galAct_incl, MulAut.conj_apply, inv_inv]
  simp only [h]
  have e := map_list_prod (MulAut.conj c⁻¹) (L.map fun i => galAct F F' n (s ^ i) δ)
  rw [List.map_map] at e
  rw [show (fun i => MulAut.conj c⁻¹ (galAct F F' n (s ^ i) δ)) =
    (⇑(MulAut.conj c⁻¹) ∘ fun i => galAct F F' n (s ^ i) δ) from rfl, ← e, MulAut.conj_apply, inv_inv]

theorem count {G₀ G : Type} [Group G₀] [Group G] [Finite G₀] [Finite G] (ι : G₀ →* G)
    (H : Subgroup G) (T : G → ℂ) (hT : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = ι k * p) :
    (Nat.card (H.comap ι) : ℂ) * ∑ᶠ y, T y = ∑ᶠ k : G₀, ∑ᶠ p : H, T (ι k * p) :=
  GlobalTheory.T.card_comap_mul_finsum_eq_finsum_fibres G₀ G ι H T hT

theorem blocks_twist {F : Type} [Field F] (t : F →+* F) (a b n : ℕ) (hn : n = a + b)
    (p x : GL (Fin n) F) (hp : InPar a p) (hx : InPar a x) :
    tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧
    brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) :=
  GlobalTheory.T.diagonalBlocks_twistedConj_blockUpperTriangular F t a b n hn p x hp hx

theorem inPar_conj_adjoin {F F' : Type} [Field F] [Field F'] [Algebra F F'] (a n : ℕ)
    (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hP : InPar a (y₀⁻¹ * γ * y₀)) : InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) :=
  GlobalTheory.T.inPar_conj_of_mem_adjoin_incl_of_inPar_conj F F' a n γ y₀ δ hA hP

theorem term (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (a b n : ℕ) (hn : n = a + b)
    (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β)
    (γ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hN : nrm s δ = incl F F' n γ) (y₀ : GL (Fin n) F) (p : GL (Fin n) F') (hp : InPar a p) :
    (if InPar a ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p)) then
      shLift s α (tlG a ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p))) *
      shLift s β (brG a b ((incl F F' n y₀ * p)⁻¹ * δ * gal (s : F' →+* F') n (incl F F' n y₀ * p)))
      else 0) =
    (if InPar a (y₀⁻¹ * γ * y₀) then α (tlG a (y₀⁻¹ * γ * y₀)) * β (brG a b (y₀⁻¹ * γ * y₀)) else 0) := by
  have hle : a ≤ n := by omega
  obtain ⟨H, π, hH, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n hn
  obtain ⟨H₀, π₀, hH₀, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  set c := incl F F' n y₀ with hc
  set δ₁ := c⁻¹ * δ * c with hδ₁def
  have hgc : gal (s : F' →+* F') n c = c := galAct_incl n s y₀
  have key : (c * p)⁻¹ * δ * gal (s : F' →+* F') n (c * p) = p⁻¹ * δ₁ * gal (s : F' →+* F') n p := by
    rw [map_mul, hgc, hδ₁def]; group
  by_cases h1 : InPar a (y₀⁻¹ * γ * y₀)
  · rw [key]
    have hδ₁ : InPar a δ₁ := inPar_conj_adjoin a n γ y₀ δ hA h1
    have hin : InPar a (p⁻¹ * δ₁ * gal (s : F' →+* F') n p) := by
      rw [← hH]
      exact H.mul_mem (H.mul_mem (H.inv_mem ((hH p).2 hp)) ((hH _).2 hδ₁))
        ((hH _).2 (inPar_gal _ a n p hp))
    rw [if_pos hin, if_pos h1]
    obtain ⟨et, eb⟩ := blocks_twist (s : F' →+* F') a b n hn p δ₁ hp hδ₁
    have hN₁ : nrm s δ₁ = incl F F' n (y₀⁻¹ * γ * y₀) := by
      rw [hδ₁def, nrm_conj_incl, hN, map_mul, map_mul, map_inv]
    obtain ⟨nt, nb⟩ := GlobalTheory.T.galoisTwistedNormGL_diagonal_blocks F F' s hs a b n hn _ δ₁ h1 hδ₁ hN₁
    have lα := GlobalTheory.T.base_change_lift_class_function F F' s hs a α hα
    have lβ := GlobalTheory.T.base_change_lift_class_function F F' s hs b β hβ
    rw [et, eb]
    have eα := lα.2 (tlG a δ₁) (tlG a p)
    have eβ := lβ.2 (brG a b δ₁) (brG a b p)
    rw [galAct_apply] at eα eβ
    rw [eα, eβ, lα.1 _ _ (by unfold IsNorm; rw [nt]), lβ.1 _ _ (by unfold IsNorm; rw [nb])]
  · rw [if_neg h1, if_neg]
    intro hin
    obtain ⟨y₁, p₁, hp₁, e, hγ₁⟩ := (GlobalTheory.T.blockUpper_twistedConj_iff_defined_over_base F F' s hs a n hle γ δ (c * p) hA hN).1 hin
    have hh : incl F F' n (y₁⁻¹ * y₀) = p₁ * p⁻¹ := by
      rw [map_mul, map_inv, ← hc, show c = incl F F' n y₁ * p₁ * p⁻¹ by rw [← e]; group]
      group
    have hP : InPar a (y₁⁻¹ * y₀) := by
      rw [← inPar_incl (F' := F'), hh, ← hH]
      exact H.mul_mem ((hH _).2 hp₁) (H.inv_mem ((hH _).2 hp))
    apply h1
    have : y₀⁻¹ * γ * y₀ = (y₁⁻¹ * y₀)⁻¹ * (y₁⁻¹ * γ * y₁) * (y₁⁻¹ * y₀) := by group
    rw [this, ← hH₀]
    exact H₀.mul_mem (H₀.mul_mem (H₀.inv_mem ((hH₀ _).2 hP)) ((hH₀ _).2 hγ₁)) ((hH₀ _).2 hP)

theorem pointwise (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (a b n : ℕ) (hn : n = a + b)
    (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β)
    (γ : GL (Fin n) F) (δ : GL (Fin n) F')
    (hA : (δ : Matrix (Fin n) (Fin n) F') ∈
      Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')})
    (hN : nrm s δ = incl F F' n γ) :
    hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n δ = hc a b α β n γ := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  obtain ⟨H, -, hH, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F' a b n hn
  set T : GL (Fin n) F' → ℂ := fun y => if InPar a (y⁻¹ * δ * gal (s : F' →+* F') n y) then
      shLift s α (tlG a (y⁻¹ * δ * gal (s : F' →+* F') n y)) *
      shLift s β (brG a b (y⁻¹ * δ * gal (s : F' →+* F') n y)) else 0 with hTdef
  set c₀ : GL (Fin n) F → ℂ := fun y₀ => if InPar a (y₀⁻¹ * γ * y₀) then
      α (tlG a (y₀⁻¹ * γ * y₀)) * β (brG a b (y₀⁻¹ * γ * y₀)) else 0 with hc₀
  have hsupp : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = incl F F' n k * p := by
    intro y hy
    have hin : InPar a (y⁻¹ * δ * gal (s : F' →+* F') n y) := by
      by_contra h; exact hy (if_neg h)
    obtain ⟨k, p, hp, e, -⟩ := (GlobalTheory.T.blockUpper_twistedConj_iff_defined_over_base F F' s hs a n (by omega) γ δ y hA hN).1 hin
    exact ⟨k, p, (hH p).2 hp, e⟩
  have hcnt := count (incl F F' n) H T hsupp
  have hterm : ∀ k (p : H), T (incl F F' n k * p) = c₀ k := fun k p =>
    term F F' s hs a b n hn α β hα hβ γ δ hA hN k p ((hH p).1 p.2)
  simp only [hterm] at hcnt
  have e1 : Nat.card (H.comap (incl F F' n)) = Nat.card {p : GL (Fin n) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [Subgroup.mem_comap, hH, inPar_incl])
  have e2 : Nat.card H = Nat.card {p : GL (Fin n) F' // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => hH x)
  have hpos1 : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0 := by
    rw [← e1]; exact_mod_cast (Nat.card_pos (α := H.comap (incl F F' n))).ne'
  have hpos2 : (Nat.card {p : GL (Fin n) F' // InPar a p} : ℂ) ≠ 0 := by
    rw [← e2]; exact_mod_cast (Nat.card_pos (α := H)).ne'
  haveI := Fintype.ofFinite H
  have hconst : ∀ k, ∑ᶠ _p : H, c₀ k = (Nat.card H : ℂ) * c₀ k := by
    intro k; rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul]
  simp only [hconst] at hcnt
  rw [← mul_finsum] at hcnt
  have hhc : hc a b α β n γ = (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹ * ∑ᶠ y₀, c₀ y₀ := by
    simp only [hc, hcTw, gal_id, hc₀]
  rw [hhc, e1, e2] at *
  unfold hcTw
  rw [← hTdef]
  field_simp
  linear_combination hcnt

end GlobalTheory.Shin.LiftHc

theorem GlobalTheory.Shin.shLift_hc_eq_hcTw : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → shLift s (hc a b α β n) = hcTw (s : F' →+* F') a b (shLift s α) (shLift s β) n := by
  intro F F' _ _ _ _ s hs a b n hn α β hα hβ
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  funext δ
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.every_element_is_norm F F' s hs n δ
  obtain ⟨y, hyA, hyN⟩ := GlobalTheory.T.conjugate_into_adjoined_algebra F F' s hs n δ γ hγ
  have hcl := (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) a b n α β).2.1
  have hL := (GlobalTheory.T.base_change_lift_class_function F F' s hs n _ hcl).2 δ y
  have hR := (GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F' (s : F' →+* F') a b n (shLift s α) (shLift s β)).1 δ y
  rw [← hL, ← hR, (GlobalTheory.T.base_change_lift_class_function F F' s hs n _ hcl).1 _ γ (by unfold IsNorm; rw [hyN])]
  exact (GlobalTheory.Shin.LiftHc.pointwise F F' s hs a b n hn α β hα hβ γ _ hyA hyN).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationPrimeEq
section
open IsLocalRing Polynomial

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.KeyOriginCut

theorem torsor_baseChange : ∀ (B₁ B₂ D₁ : Type) [CommRing B₁] [CommRing B₂] [CommRing D₁] [Algebra B₁ B₂] [Algebra B₁ D₁]
    (q : ℕ), 0 < q → ∀ (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[B₁] D₁)),
    GlobalTheory.KeyOriginCut.IsZTorsor B₁ D₁ q act₁ →
    ∃ act₂ : Multiplicative (ZMod q) →* (TensorProduct B₁ B₂ D₁ ≃ₐ[B₂] TensorProduct B₁ B₂ D₁),
      GlobalTheory.KeyOriginCut.IsZTorsor B₂ (TensorProduct B₁ B₂ D₁) q act₂ := by
  intro B₁ B₂ D₁ _ _ _ _ _ q hq act₁ h
  haveI : NeZero q := ⟨hq.ne'⟩
  classical
  obtain ⟨hfin, hproj, hff, hbij⟩ := h
  let act₂ : Multiplicative (ZMod q) →* (B₂ ⊗[B₁] D₁ ≃ₐ[B₂] B₂ ⊗[B₁] D₁) :=
    { toFun := fun g => Algebra.TensorProduct.congr AlgEquiv.refl (act₁ g)
      map_one' := by
        refine AlgEquiv.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b d => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      map_mul' := by
        intro g h
        refine AlgEquiv.ext fun x => ?_
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b d => simp [Algebra.TensorProduct.congr_apply]
        | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy] }
  refine ⟨act₂, inferInstance, inferInstance, inferInstance, ?_⟩
  let e₀ := LinearEquiv.ofBijective (Algebra.TensorProduct.productMap
      (Pi.algHom B₁ (fun _ : Multiplicative (ZMod q) => D₁) (fun _ => AlgHom.id B₁ D₁))
      (Pi.algHom B₁ (fun _ : Multiplicative (ZMod q) => D₁) (fun g => (act₁ g).toAlgHom))).toLinearMap hbij
  have key : ∀ z : B₂ ⊗[B₁] (D₁ ⊗[B₁] D₁),
      Algebra.TensorProduct.productMap
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun _ => AlgHom.id B₂ _))
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun g => (act₂ g).toAlgHom))
        (TensorProduct.AlgebraTensorModule.distribBaseChange B₁ B₂ D₁ D₁ z) =
      TensorProduct.piRight B₁ B₂ B₂ (fun _ : Multiplicative (ZMod q) => D₁)
        (LinearEquiv.baseChange B₁ B₂ _ _ e₀ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy]
    | tmul b w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      | tmul x y =>
        funext g
        simp [act₂, e₀, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          Algebra.TensorProduct.productMap_apply_tmul, TensorProduct.piRight_apply,
          Algebra.TensorProduct.congr_apply]
        congr 1
  have hfun : ⇑(Algebra.TensorProduct.productMap
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun _ => AlgHom.id B₂ _))
        (Pi.algHom B₂ (fun _ : Multiplicative (ZMod q) => B₂ ⊗[B₁] D₁) (fun g => (act₂ g).toAlgHom))) =
      ⇑(TensorProduct.piRight B₁ B₂ B₂ (fun _ : Multiplicative (ZMod q) => D₁)) ∘
        ⇑(LinearEquiv.baseChange B₁ B₂ _ _ e₀) ∘
        ⇑(TensorProduct.AlgebraTensorModule.distribBaseChange B₁ B₂ D₁ D₁).symm := by
    funext z
    simp only [Function.comp_apply]
    rw [← key, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (TensorProduct.piRight B₁ B₂ B₂ _).bijective.comp
    ((LinearEquiv.baseChange B₁ B₂ _ _ e₀).bijective.comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange B₁ B₂ D₁ D₁).symm.bijective)

theorem exists_stage_torsor : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (Q : Ideal E) (_ : Q.IsPrime),
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T ∧
      ∃ (j : Localization.AtPrime Q →+* O),
        j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O ∧
      ∃ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j ∧
      ∃ (D₁ : Type) (_ : CommRing D₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁)
        (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ ∧
        ∀ σ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ →
          Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hPeq q hq hqu D _ _ act hD
  obtain ⟨E, _, _, _, _, _, ψ, DE, _, _, actE, hDE, hred⟩ :=
    GlobalTheory.T.spread_torsor_to_etale_algebra T O P φ hφ hSH.2.2.2 q hq D act hD
  set Q : Ideal E := (maximalIdeal O).comap ψ.toRingHom with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hloc : (maximalIdeal O).comap φ = maximalIdeal (Localization.AtPrime P) := by
    haveI := hSH.2.2.1
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
    · intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit φ x hu)
  have hQP : Q.comap (algebraMap (Polynomial T) E) = P := by
    rw [hQdef, Ideal.comap_comap]
    have h1 : ψ.toRingHom.comp (algebraMap (Polynomial T) E) = φ.comp (algebraMap (Polynomial T) _) := by
      rw [hφ]; exact ψ.comp_algebraMap
    rw [h1, ← Ideal.comap_comap, hloc]
    exact Localization.AtPrime.under_maximalIdeal (R := Polynomial T) (I := P)

  have hunit : ∀ y : Q.primeCompl, IsUnit (ψ.toRingHom (y : E)) := by
    intro y
    by_contra hy
    exact y.2 (show (y : E) ∈ Q from (IsLocalRing.mem_maximalIdeal _).2 hy)
  let j : Localization.AtPrime Q →+* O := IsLocalization.lift (M := Q.primeCompl) hunit
  have hjE : j.comp (algebraMap E (Localization.AtPrime Q)) = ψ.toRingHom :=
    IsLocalization.lift_comp hunit
  have hjR : j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O := by
    rw [IsScalarTower.algebraMap_eq (Polynomial T) E (Localization.AtPrime Q), ← RingHom.comp_assoc, hjE]
    exact ψ.comp_algebraMap
  have hjT : ∀ t : T, j (algebraMap T (Localization.AtPrime Q) t) = algebraMap T O t := by
    intro t
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply T (Polynomial T) O, ← RingHom.comp_apply, hjR]
  have hM : Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)).comap j := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (hjT t).symm⟩
  let ψ' : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.map (GlobalTheory.LocAcyc.GenFib T O) j hM
  have hψ' : ψ'.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j := IsLocalization.map_comp hM

  have hM' : Algebra.algebraMapSubmonoid E (nonZeroDivisors T) ≤
      (Algebra.algebraMapSubmonoid (Localization.AtPrime Q) (nonZeroDivisors T)).comap
        (algebraMap E (Localization.AtPrime Q)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (IsScalarTower.algebraMap_apply T E (Localization.AtPrime Q) t).symm⟩
  let m : GlobalTheory.LocAcyc.GenFib T E →+* GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) :=
    IsLocalization.map _ (algebraMap E (Localization.AtPrime Q)) hM'
  letI : Algebra (GlobalTheory.LocAcyc.GenFib T E) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) := m.toAlgebra
  obtain ⟨act₂, h₂⟩ := torsor_baseChange (GlobalTheory.LocAcyc.GenFib T E)
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) DE q hq actE hDE
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q, inferInstance,
    hQP.trans hPeq, j, hjR, ψ', hψ', _, inferInstance, inferInstance, act₂, h₂, ?_⟩
  intro σ hσ
  refine hred (σ.comp (Algebra.TensorProduct.includeRight (R := GlobalTheory.LocAcyc.GenFib T E)
    (A := GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) (B := DE)).toRingHom) fun e => ?_
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (GlobalTheory.LocAcyc.GenFib T E)
    (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)), ← RingHom.comp_apply σ, hσ]
  change ψ' (m (algebraMap E _ e)) = _
  simp only [m, IsLocalization.map_eq]
  rw [← RingHom.comp_apply ψ', hψ', RingHom.comp_apply, ← RingHom.comp_apply j, hjE]
  rfl

end GlobalTheory.KeyOriginCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroLaurentSurjective
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.MultiplicativeGroupGlobalSections


open LaurentPolynomial in
theorem laurent_ringHom_ext {R S : Type} [CommRing R] [CommRing S] {f g : LaurentPolynomial R →+* S}
    (hC : f.comp C = g.comp C) (hT : f (T 1) = g (T 1)) : f = g := by
  have h1 : f (T 1) * f (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
  have h2 : g (T 1) * g (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
  have hTm : f (T (-1)) = g (T (-1)) :=
    calc f (T (-1)) = f (T (-1)) * (g (T 1) * g (T (-1))) := by rw [h2, mul_one]
      _ = (f (T 1) * f (T (-1))) * g (T (-1)) := by rw [← hT]; ring
      _ = g (T (-1)) := by rw [h1, one_mul]
  have hTn : ∀ n : ℤ, f (T n) = g (T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [T_zero]
    | succ n ih => rw [T_add, map_mul, map_mul, ih, hT]
    | pred n ih => rw [sub_eq_add_neg, T_add, map_mul, map_mul, ih, hTm]
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    rw [single_eq_C]
    exact congrArg (fun φ : R →+* S => φ b) hC
  · intro n
    exact hTn n

theorem pull_spMap_id (q : ℕ) (A : Type) [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ n x = x := by
  have h : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap]
    rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]
  rw [h, pull_id]


open LaurentPolynomial GmPhiNat in
theorem exists_ht_zero_pull_laurent_eq (q : ℕ) [NeZero q] (R : Type) [CommRing R] (hq : IsUnit (q : R)) (i : ℤ)
    (y : Ht q (sp (LaurentPolynomial R)) 0 i) :
    ∃ z : Ht q (sp R) 0 i, pull _ (spMap (LaurentPolynomial.C : R →+* LaurentPolynomial R)) _ 0 z = y := by
  let ev₁ : LaurentPolynomial R →+* R := eval₂ (RingHom.id R) 1
  have hev : ev₁.comp C = RingHom.id R := RingHom.ext fun a => eval₂_C _ _ a
  refine ⟨pull _ (spMap ev₁) _ 0 y, ?_⟩
  symm
  rw [← sub_eq_zero]
  have hqL : IsUnit (q : LaurentPolynomial R) := by simpa using hq.map (C : R →+* LaurentPolynomial R)
  apply GlobalTheory.EtC.GeomZero.eq_zero_of_geom q (LaurentPolynomial R) hqL i
  intro K _ _ f
  set y' := y - pull _ (spMap (C : R →+* LaurentPolynomial R)) _ 0 (pull _ (spMap ev₁) _ 0 y) with hy'

  have h0 : pull _ (spMap ev₁) _ 0 y' = 0 := by
    rw [hy', map_sub, ← pull_spMap_comp, hev, pull_spMap_id, sub_self]
  let f₀ : R →+* K := f.comp C
  have hT1 : IsUnit (f (T 1)) := by
    refine isUnit_iff_exists_inv.2 ⟨f (T (-1)), ?_⟩
    rw [← map_mul, ← T_add]; simp
  let u : Kˣ := hT1.unit
  let evu : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) u
  have hf : f = evu.comp (laurentMap f₀) := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc]
      ext a
      simp [evu, f₀, eval₂_C]
    · simp [evu, laurentMap_T, eval₂_T, u]
  let ev₁K : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) 1
  have hevK : ev₁K.comp C = RingHom.id K := RingHom.ext fun a => eval₂_C _ _ a
  have hcomm : ev₁K.comp (laurentMap f₀) = f₀.comp ev₁ := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc, hevK, RingHom.comp_assoc, hev]
      rfl
    · simp [ev₁K, ev₁, laurentMap_T, eval₂_T]
  have hqK : IsUnit (q : K) := by simpa using hq.map f₀
  have hζ : ∃ ζ : K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    have hdeg : (Polynomial.cyclotomic q K).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨ζ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ
  have hbij := GlobalTheory.EtC.h_zero_pull_bijective q K (LaurentPolynomial K) (C : K →+* LaurentPolynomial K) hqK hζ
    inferInstance (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) i
  have hw : pull _ (spMap (laurentMap f₀)) _ 0 y' = 0 := by
    obtain ⟨v, hv⟩ := hbij.2 (pull _ (spMap (laurentMap f₀)) _ 0 y')
    have hv0 : v = 0 := by
      have e1 : pull _ (spMap ev₁K) _ 0 (pull _ (spMap (C : K →+* LaurentPolynomial K)) _ 0 v) = v := by
        rw [← pull_spMap_comp, hevK, pull_spMap_id]
      rw [← e1, hv, ← pull_spMap_comp, hcomm, pull_spMap_comp, h0, map_zero]
    rw [← hv, hv0, map_zero]
  rw [hf, pull_spMap_comp, hw, map_zero]

end GlobalTheory.EtC.MultiplicativeGroupGlobalSections

end
end

