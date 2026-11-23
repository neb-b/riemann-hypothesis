module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DformRelEquivalence
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ClsMove
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix NumberField Polynomial GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef
open UpperTheory.Gal.LocalSmoothExtension
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Spc

section Ring

variable {S A : Type*} [Ring S] [CommRing A] [Algebra A S]

private theorem sim_triv (σ : S →+* Sᵐᵒᵖ) (b b' : S) (x x' Y : Sˣ) (t t' T : Aˣ)
    (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b' * (σ x').unop = algebraMap A S t')
    (hb : b' = algebraMap A S T * ((Y : S) * b * (σ Y).unop)) :
    ((x' * Y * x⁻¹ : Sˣ) : S) * (σ ((x' * Y * x⁻¹ : Sˣ) : S)).unop =
      algebraMap A S ((t' * T⁻¹ * t⁻¹ : Aˣ) : A) := by
  have h1 : (σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have h0 : b = (t : A) • (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
    calc b = (((x⁻¹ : Sˣ) : S) * x) * b * ((σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, h1, one_mul, mul_one]
      _ = ((x⁻¹ : Sˣ) : S) * ((x : S) * b * (σ x).unop) * (σ ((x⁻¹ : Sˣ) : S)).unop := by
          simp only [mul_assoc]
      _ = _ := by
          rw [hx, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]
  have h2 : ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop = ((t⁻¹ : Aˣ) : A) • b := by
    conv_rhs => rw [h0]
    rw [smul_smul, Units.inv_mul, one_smul]
  have h3 : (Y : S) * b * (σ Y).unop = ((T⁻¹ : Aˣ) : A) • b' := by
    rw [hb, ← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
  calc ((x' * Y * x⁻¹ : Sˣ) : S) * (σ ((x' * Y * x⁻¹ : Sˣ) : S)).unop
      = x' * (Y * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) * (σ Y).unop) * (σ x').unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = ((t⁻¹ : Aˣ) : A) • (x' * ((Y : S) * b * (σ Y).unop) * (σ x').unop) := by
        rw [h2]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = ((t⁻¹ : Aˣ) : A) • ((T⁻¹ : Aˣ) : A) • ((x' : S) * b' * (σ x').unop) := by
        rw [h3]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = _ := by
        rw [hx', Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul]
        congr 1
        simp only [Units.val_mul]
        ring

private theorem sim_conj (σ : S →+* Sᵐᵒᵖ) (b b' : S) (z y : Sˣ) (T : Aˣ) (r : A)
    (hb : b' = algebraMap A S T * ((y : S) * b * (σ y).unop))
    (hz : (z : S) * b' * (σ z).unop = algebraMap A S r * b') :
    ((y⁻¹ * z * y : Sˣ) : S) * b * (σ ((y⁻¹ * z * y : Sˣ) : S)).unop = algebraMap A S r * b := by
  have h1 : (σ y).unop * (σ ((y⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have h3 : (y : S) * b * (σ y).unop = ((T⁻¹ : Aˣ) : A) • b' := by
    rw [hb, ← Algebra.smul_def, smul_smul, Units.inv_mul, one_smul]
  rw [← Algebra.smul_def] at hz ⊢
  calc ((y⁻¹ * z * y : Sˣ) : S) * b * (σ ((y⁻¹ * z * y : Sˣ) : S)).unop
      = ((y⁻¹ : Sˣ) : S) * ((z : S) * ((y : S) * b * (σ y).unop) * (σ z).unop) *
          (σ ((y⁻¹ : Sˣ) : S)).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = ((T⁻¹ : Aˣ) : A) • (((y⁻¹ : Sˣ) : S) * ((z : S) * b' * (σ z).unop) *
          (σ ((y⁻¹ : Sˣ) : S)).unop) := by
        rw [h3]; simp only [mul_smul_comm, smul_mul_assoc]
    _ = r • (((y⁻¹ : Sˣ) : S) * (((T⁻¹ : Aˣ) : A) • b') * (σ ((y⁻¹ : Sˣ) : S)).unop) := by
        rw [hz]; simp only [mul_smul_comm, smul_mul_assoc]; rw [smul_comm]
    _ = r • ((((y⁻¹ : Sˣ) : S) * y) * b * ((σ y).unop * (σ ((y⁻¹ : Sˣ) : S)).unop)) := by
        rw [← h3]; simp only [mul_assoc]
    _ = r • b := by rw [Units.inv_mul, h1, one_mul, mul_one]

end Ring

private theorem mem_forms_move {A H V : Type} [Group A] [Group H] [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ A V) (Γ Γ' : Subgroup A) (ι : Γ →* H) (ι' : Γ' →* H) (K : Subgroup H) (y : A) (d : H)
    (hc : ∀ γ' : Γ', ∃ γ : Γ, (γ' : A) = y * (γ : A) * y⁻¹ ∧ ι' γ' = d * ι γ * d⁻¹)
    {Φ : H → V} (hΦ : Φ ∈ HeckeTraceForms.forms ι K (ξ.comp Γ.subtype)) :
    (fun g => ξ y (Φ (d⁻¹ * g))) ∈ HeckeTraceForms.forms ι' K (ξ.comp Γ'.subtype) := by
  refine ⟨fun γ' g => ?_, fun k hk g => ?_⟩
  · obtain ⟨γ, e1, e2⟩ := hc γ'
    have e3 : d⁻¹ * (ι' γ' * g) = ι γ * (d⁻¹ * g) := by rw [e2]; group
    have e4 : Φ (ι γ * (d⁻¹ * g)) = ξ (γ : A) (Φ (d⁻¹ * g)) := hΦ.1 γ (d⁻¹ * g)
    show ξ y (Φ (d⁻¹ * (ι' γ' * g))) = ξ (γ' : A) (ξ y (Φ (d⁻¹ * g)))
    rw [e3, e4, e1, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  · show ξ y (Φ (d⁻¹ * (g * k))) = ξ y (Φ (d⁻¹ * g))
    rw [← mul_assoc]
    exact congrArg _ (hΦ.2 k hk _)

variable {p : ℕ} [Fact p.Prime]

private theorem op_move {G : HTGroup p} {A V : Type} [Group A] [AddCommGroup V] [Module ℂ V]
    (ξ : Representation ℂ A V) (K : Subgroup G.GAf) (f : G.GAf → ℂ) (Φ : G.GAf × Gr G 1 → V) (y : A)
    (d : G.GAf × Gr G 1) :
    op K f (fun g => ξ y (Φ (d⁻¹ * g))) = fun g => ξ y (op K f Φ (d⁻¹ * g)) := by
  funext g
  let L : V ≃+ V :=
    { toFun := ξ y
      invFun := ξ y⁻¹
      left_inv := fun v => by rw [← Module.End.mul_apply, ← map_mul]; simp
      right_inv := fun v => by rw [← Module.End.mul_apply, ← map_mul]; simp
      map_add' := map_add _ }
  show ∑ᶠ h : G.GAf ⧸ K, f h.out • ξ y (Φ (d⁻¹ * (g * (h.out, 1)))) =
    L (∑ᶠ h : G.GAf ⧸ K, f h.out • Φ (d⁻¹ * g * (h.out, 1)))
  rw [AddEquiv.map_finsum]
  refine finsum_congr fun h => ?_
  show _ = ξ y (_ • _)
  rw [map_smul, mul_assoc]

private theorem conj_emb (G : HTGroup p) (B B' : DForm G) (y : G.Cˣ) (s : ℚ) (hs : 0 < s)
    (hβ : (B'.β : G.C) = algebraMap ℚ G.C s * (y * B.β * sh G y))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) B.β x t)
    (x' : (AfP p ⊗[ℚ] G.C)ˣ) (t' : (AfP p)ˣ) (hx' : Triv G (AfP p) B'.β x' t') :
    ∃ d : G.GAf × Gr G 1, ∀ γ' : grp G B'.β, ∃ γ : grp G B.β,
      (γ' : G.Cˣ × ℚˣ) = ((y, 1) : G.Cˣ × ℚˣ) * (γ : G.Cˣ × ℚˣ) * ((y, 1) : G.Cˣ × ℚˣ)⁻¹ ∧
      B'.embAt x' t' hx' γ' = d * B.embAt x t hx γ * d⁻¹ := by
  let Y : (AfP p ⊗[ℚ] G.C)ˣ := Units.map (inC G (AfP p)).toMonoidHom y
  let T : (AfP p)ˣ := Units.map (algebraMap ℚ (AfP p)).toMonoidHom (Units.mk0 s hs.ne')
  have e1 : inC G (AfP p) (sh G y) = (starT G.star (AfP p) (Y : AfP p ⊗[ℚ] G.C)).unop :=
    (starT_tmul G.star (AfP p) 1 _).symm
  have e2 : inC G (AfP p) (algebraMap ℚ G.C s) =
      algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (T : AfP p) := by
    show _ = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) s)
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
  have hb : inC G (AfP p) B'.β = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (T : AfP p) *
      ((Y : AfP p ⊗[ℚ] G.C) * inC G (AfP p) B.β * (starT G.star (AfP p) (Y : AfP p ⊗[ℚ] G.C)).unop) := by
    rw [hβ, map_mul, map_mul, map_mul, e1, e2]
    rfl
  have hc := sim_triv (starT G.star (AfP p)) _ _ x x' Y t t' T hx hx' hb
  let c : G.GAf := ⟨(x' * Y * x⁻¹, t' * T⁻¹ * t⁻¹), hc⟩
  refine ⟨(c, inclG G 1 (locC G (y, 1))), fun γ' => ?_⟩
  have hz : ((γ'.1.1 : G.Cˣ) : G.C) * B'.β * (G.star ((γ'.1.1 : G.Cˣ) : G.C)).unop =
      algebraMap ℚ G.C (γ'.1.2 : ℚ) * B'.β := γ'.2.1
  have hmem : ((y⁻¹ * γ'.1.1 * y, γ'.1.2) : G.Cˣ × ℚˣ) ∈ grp G B.β :=
    ⟨sim_conj G.star (B.β : G.C) (B'.β : G.C) γ'.1.1 y (Units.mk0 s hs.ne') (γ'.1.2 : ℚ) hβ hz, γ'.2.2⟩
  have hconj : (γ' : G.Cˣ × ℚˣ) = ((y, 1) : G.Cˣ × ℚˣ) * (y⁻¹ * γ'.1.1 * y, γ'.1.2) *
      ((y, 1) : G.Cˣ × ℚˣ)⁻¹ := by
    refine Prod.ext ?_ ?_
    · simp [mul_assoc]
    · simp
  refine ⟨⟨_, hmem⟩, hconj, ?_⟩
  refine Prod.ext (Subtype.ext (Prod.ext ?_ ?_)) ?_
  · show x' * Units.map (inC G (AfP p)).toMonoidHom γ'.1.1 * x'⁻¹ =
      (x' * Y * x⁻¹) * (x * Units.map (inC G (AfP p)).toMonoidHom (y⁻¹ * γ'.1.1 * y) * x⁻¹) *
        (x' * Y * x⁻¹)⁻¹
    have e3 : Units.map (inC G (AfP p)).toMonoidHom (y⁻¹ * γ'.1.1 * y) =
        Y⁻¹ * Units.map (inC G (AfP p)).toMonoidHom γ'.1.1 * Y := by
      rw [map_mul, map_mul, map_inv]
    rw [e3]
    group
  · have e3 : ∀ a b : (AfP p)ˣ, b = a * b * a⁻¹ := fun a b => by
      rw [mul_comm a b, mul_inv_cancel_right]
    exact e3 (t' * T⁻¹ * t⁻¹) (Units.map (algebraMap ℚ (AfP p)).toMonoidHom γ'.1.2)
  · have e3 := congrArg ((inclG G 1).comp (locC G)) hconj
    rw [map_mul, map_mul, map_inv] at e3
    exact e3

theorem clsMove : ClsMove := by
  intro p _ G V _ _ ξ K J ψ θ e ⟨B, x, t, hx, Φ, hΦ, h0, he, hψ⟩
  have hrel : DForm.Rel B (Quot.out (Quot.mk _ B : DFCls G)) :=
    (GlobalTheory.LKDef.Regroup.dform_rel_equivalence.eqvGen_iff).1
      (Quot.eqvGen_exact (Quot.out_eq (Quot.mk DForm.Rel B)).symm)
  obtain ⟨y, s, hs, hβ⟩ := hrel
  obtain ⟨d, hd⟩ := conj_emb G B _ y s hs hβ x t hx _ _
    (Quot.out (Quot.mk _ B : DFCls G)).trivAf.choose_spec.choose_spec
  refine ⟨Quot.mk _ B, fun g => ξ (y, 1) (Φ (d⁻¹ * g)),
    mem_forms_move ξ _ _ _ _ _ _ d hd hΦ, fun h => h0 ?_, ?_, fun j => ?_⟩
  · funext g
    have := congrFun h (d * g)
    simp only [inv_mul_cancel_left, Pi.zero_apply] at this
    have h2 := congrArg (ξ ((y, 1) : G.Cˣ × ℚˣ)⁻¹) this
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at h2
    exact h2
  · rw [op_move, he]
  · rw [op_move, hψ j]
    funext g
    simp

end UpperTheory.Gal.Spc
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.CommOfOpen
section
set_option autoImplicit false

noncomputable section

open Formalism.UG GlobalTheory.LKDef

namespace UpperTheory.Gal.Spc

section Abstract

variable {H₁ H₂ Γ V : Type} [Group H₁] [Group H₂] [Group Γ] [AddCommGroup V] [Module ℂ V]
  (ι : Γ →* H₁ × H₂) (K₁ : Subgroup H₁) (K₂ : Subgroup H₂) (ξ : Representation ℂ Γ V)

variable {K₁} in
private theorem hecke_right {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) (h : H₁) (c : K₁) : f (h * c) = f h := by
  have := hf.1 1 c h
  simpa using this

variable {K₁} in
private theorem hecke_left {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) (h : H₁) (c : K₁) : f (c * h) = f h := by
  have := hf.1 c 1 h
  simpa using this

variable {K₁} in
private theorem fin_act (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) (Φ : H₁ × H₂ → V) (g : H₁ × H₂) :
    (Function.support fun x : H₁ ⧸ K₁ => f x.out • Φ (g * (x.out, 1))).Finite :=
  (P.finite_supp K₁ hK f hf).subset fun x hx h0 => hx (by simp [h0])

variable {ι K₁ K₂ ξ} in
private theorem form_right {Φ : H₁ × H₂ → V} (hΦ : Φ ∈ HeckeTraceForms.forms ι (K₁.prod K₂) ξ) (g : H₁ × H₂) {k₁ : H₁} {k₂ : H₂}
    (h₁ : k₁ ∈ K₁) (h₂ : k₂ ∈ K₂) : Φ (g * (k₁, k₂)) = Φ g :=
  hΦ.2 _ (Subgroup.mem_prod.2 ⟨h₁, h₂⟩) g

variable {ι K₁ K₂ ξ} in
private theorem act_mem (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) {Φ : H₁ × H₂ → V}
    (hΦ : Φ ∈ HeckeTraceForms.forms ι (K₁.prod K₂) ξ) : hActK K₁ f Φ ∈ HeckeTraceForms.forms ι (K₁.prod K₂) ξ := by
  refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
  · unfold hActK
    rw [map_finsum (ξ γ) (fin_act hK hf Φ g)]
    refine finsum_congr fun x => ?_
    rw [map_smul, mul_assoc, hΦ.1]
  · obtain ⟨h₁, h₂⟩ := Subgroup.mem_prod.1 hk
    unfold hActK
    have key := P.finsum_out_mul K₁ k.1 (fun h => f h • Φ (g * (h, 1))) (fun h c => by
      have e : g * (h * (c : H₁), (1 : H₂)) = g * (h, 1) * ((c : H₁), (1 : H₂)) := by
        simp [mul_assoc]
      show f (h * c) • Φ (g * (h * (c : H₁), (1 : H₂))) = f h • Φ (g * (h, 1))
      rw [hecke_right hf, e, form_right hΦ _ c.2 (one_mem _)])
    refine Eq.trans ?_ key
    refine finsum_congr fun x => ?_
    have e : g * k * (x.out, (1 : H₂)) = g * (k.1 * x.out, 1) * ((1 : H₁), k.2) := by
      ext <;> simp [mul_assoc]
    show _ = f (k.1 * x.out) • Φ (g * (k.1 * x.out, 1))
    rw [e, form_right hΦ _ (one_mem _) h₂, hecke_left hf x.out ⟨k.1, h₁⟩]

private def act (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) :
    Module.End ℂ (HeckeTraceForms.forms ι (K₁.prod K₂) ξ) where
  toFun Φ := ⟨hActK K₁ f Φ, act_mem hK hf Φ.2⟩
  map_add' a b := by
    apply Subtype.ext
    funext g
    show (∑ᶠ x : H₁ ⧸ K₁, f x.out • ((a : H₁ × H₂ → V) (g * (x.out, 1)) + (b : H₁ × H₂ → V) (g * (x.out, 1)))) =
      (∑ᶠ x : H₁ ⧸ K₁, f x.out • (a : H₁ × H₂ → V) (g * (x.out, 1))) +
        ∑ᶠ x : H₁ ⧸ K₁, f x.out • (b : H₁ × H₂ → V) (g * (x.out, 1))
    simp only [smul_add]
    exact finsum_add_distrib (fin_act hK hf _ g) (fin_act hK hf _ g)
  map_smul' c a := by
    apply Subtype.ext
    funext g
    show (∑ᶠ x : H₁ ⧸ K₁, f x.out • (c • (a : H₁ × H₂ → V) (g * (x.out, 1)))) =
      c • ∑ᶠ x : H₁ ⧸ K₁, f x.out • (a : H₁ × H₂ → V) (g * (x.out, 1))
    rw [smul_finsum' c (show Function.HasFiniteSupport
      (fun x : H₁ ⧸ K₁ => f x.out • (a : H₁ × H₂ → V) (g * (x.out, 1))) from fin_act hK hf _ g)]
    exact finsum_congr fun x => smul_comm _ _ _

variable {K₁} in
private theorem act_mul (hK : IsCommensurated K₁) {f₁ f₂ : H₁ → ℂ} (h₁ : f₁ ∈ Hecke ℂ K₁) (h₂ : f₂ ∈ Hecke ℂ K₁)
    {Φ : H₁ × H₂ → V} (hΦ : ∀ (k : H₁), k ∈ K₁ → ∀ g, Φ (g * (k, 1)) = Φ g) :
    hActK K₁ (conv K₁ f₁ f₂) Φ = hActK K₁ f₁ (hActK K₁ f₂ Φ) := by
  funext g
  let φ : H₁ → V := fun x => Φ (g * (x, 1))
  have hφ : φ ∈ AMF ℂ (⊥ : Subgroup H₁) K₁ (1 : Representation ℂ (⊥ : Subgroup H₁) V) := by
    rintro ⟨γ, hγ⟩ x ⟨κ, hκ⟩
    obtain rfl : γ = 1 := Subgroup.mem_bot.1 hγ
    have e : g * ((1 : H₁) * x * κ, (1 : H₂)) = g * (x, 1) * (κ, 1) := by simp [mul_assoc]
    show Φ (g * ((1 : H₁) * x * κ, (1 : H₂))) = Φ (g * (x, 1))
    rw [e, hΦ κ hκ]
  have key := congrFun (P.hecke_act_mul H₁ ⊥ K₁ ℂ V 1 hK f₁ h₁ f₂ h₂ φ hφ) 1
  have e1 : ∀ (f : H₁ → ℂ) (a : H₁), hAct K₁ f φ a = hActK K₁ f Φ (g * (a, 1)) := by
    intro f a
    unfold hAct hActK
    refine finsum_congr fun x => ?_
    have e : g * (a * x.out, (1 : H₂)) = g * (a, 1) * (x.out, 1) := by simp [mul_assoc]
    show f x.out • Φ (g * (a * x.out, (1 : H₂))) = _
    rw [e]
  have l : hActK K₁ (conv K₁ f₁ f₂) Φ g = hAct K₁ (conv K₁ f₁ f₂) φ 1 := by
    rw [e1]
    exact congrArg _ (mul_one g).symm
  have r : hActK K₁ f₁ (hActK K₁ f₂ Φ) g = hAct K₁ f₁ (hAct K₁ f₂ φ) 1 := by
    show (∑ᶠ x : H₁ ⧸ K₁, f₁ x.out • hActK K₁ f₂ Φ (g * (x.out, 1))) =
      ∑ᶠ x : H₁ ⧸ K₁, f₁ x.out • hAct K₁ f₂ φ (1 * x.out)
    refine finsum_congr fun x => ?_
    rw [e1, one_mul]
  rw [l, r, key]

variable {ι K₁ K₂ ξ} in
private theorem act_isHecke (hK : IsCommensurated K₁) {f : H₁ → ℂ} (hf : f ∈ Hecke ℂ K₁) :
    HeckeTraceForms.IsHecke ι (K₁.prod K₂) ξ (fun h => f h.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.2)
      (act ι K₁ K₂ ξ hK hf) := by
  intro φ g
  let e : H₁ ⧸ K₁ → (H₁ × H₂) ⧸ (K₁.prod K₂) := fun q => QuotientGroup.mk (q.out, 1)
  have he : Function.Injective e := by
    intro a b hab
    have h := QuotientGroup.eq.1 hab
    have h1 := (Subgroup.mem_prod.1 h).1
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
    exact QuotientGroup.eq.2 (by simpa using h1)
  set A : (H₁ × H₂) ⧸ (K₁.prod K₂) → V := fun h =>
    (f h.out.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.out.2) • (φ : H₁ × H₂ → V) (g * h.out) with hA
  have hsupp : ∀ h, A h ≠ 0 → h ∈ Set.range e := by
    intro h hh
    have h2 : h.out.2 ∈ K₂ := by
      by_contra hn
      exact hh (by simp [hA, Set.indicator_of_notMem (show h.out.2 ∉ (K₂ : Set H₂) from hn)])
    refine ⟨QuotientGroup.mk h.out.1, ?_⟩
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K₁ h.out.1
    show QuotientGroup.mk ((QuotientGroup.mk h.out.1 : H₁ ⧸ K₁).out, (1 : H₂)) = h
    rw [hc, ← QuotientGroup.out_eq' h]
    refine QuotientGroup.eq.2 (Subgroup.mem_prod.2 ?_)
    simp only [QuotientGroup.out_eq']
    refine ⟨?_, ?_⟩
    · simpa using K₁.inv_mem c.2
    · simpa using h2
  have hval : ∀ q, A (e q) = f q.out • (φ : H₁ × H₂ → V) (g * (q.out, 1)) := by
    intro q
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (K₁.prod K₂) ((q.out, 1) : H₁ × H₂)
    obtain ⟨c₁, c₂⟩ := Subgroup.mem_prod.1 c.2
    have ho : (e q).out = (q.out, 1) * (c : H₁ × H₂) := hc
    simp only [hA]
    rw [ho]
    have e2 : g * (((q.out, 1) : H₁ × H₂) * (c : H₁ × H₂)) = g * (q.out, 1) * ((c : H₁ × H₂).1, (c : H₁ × H₂).2) := by
      rw [mul_assoc]
    rw [e2, form_right φ.2 _ c₁ c₂]
    congr 1
    have i2 : ((((q.out, 1) : H₁ × H₂) * (c : H₁ × H₂)).2) ∈ (K₂ : Set H₂) := by simpa using c₂
    rw [Set.indicator_of_mem i2]
    have := hecke_right hf q.out ⟨_, c₁⟩
    simpa using this
  have hsum : (∑ᶠ h, A h) = ∑ᶠ q, A (e q) := by
    rw [← finsum_mem_range he, finsum_mem_def]
    refine finsum_congr fun h => ?_
    by_cases hr : h ∈ Set.range e
    · rw [Set.indicator_of_mem hr]
    · rw [Set.indicator_of_notMem hr]
      by_contra hne
      exact hr (hsupp h hne)
  show hActK K₁ f φ g = ∑ᶠ h, A h
  rw [hsum]
  exact finsum_congr fun q => (hval q).symm

private theorem abs_main (hK : IsCommensurated K₁) :
    ∃ T : (H₁ → ℂ) → Module.End ℂ (HeckeTraceForms.forms ι (K₁.prod K₂) ξ), T 0 = 0 ∧
      ∀ f ∈ Hecke ℂ K₁, (∀ Φ, (T f Φ : H₁ × H₂ → V) = hActK K₁ f Φ) ∧
        HeckeTraceForms.heckeTrace ι (K₁.prod K₂) ξ (fun h => f h.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.2) =
          LinearMap.trace ℂ _ (T f) ∧
        ∀ f' ∈ Hecke ℂ K₁, T (conv K₁ f f') = T f * T f' ∧ ∀ c : ℂ, T (c • f + f') = c • T f + T f' := by
  classical
  let T : (H₁ → ℂ) → Module.End ℂ (HeckeTraceForms.forms ι (K₁.prod K₂) ξ) := fun f =>
    if h : f ∈ Hecke ℂ K₁ then act ι K₁ K₂ ξ hK h else 0
  have hT : ∀ f (h : f ∈ Hecke ℂ K₁), T f = act ι K₁ K₂ ξ hK h := fun f h => dif_pos h
  have hTa : ∀ f (h : f ∈ Hecke ℂ K₁) Φ, (T f Φ : H₁ × H₂ → V) = hActK K₁ f Φ := fun f h Φ => by rw [hT f h]; rfl
  refine ⟨T, ?_, fun f hf => ⟨hTa f hf, ?_, fun f' hf' => ⟨?_, fun c => ?_⟩⟩⟩
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    rw [hTa 0 (Submodule.zero_mem _)]
    funext g
    simp [hActK]
  · have hI := act_isHecke (ι := ι) (K₂ := K₂) (ξ := ξ) hK hf
    have hex : ∃ T', HeckeTraceForms.IsHecke ι (K₁.prod K₂) ξ
        (fun h => f h.1 * Set.indicator (K₂ : Set H₂) (1 : H₂ → ℂ) h.2) T' := ⟨_, hI⟩
    rw [HeckeTraceForms.heckeTrace, dif_pos hex, hT f hf]
    congr 1
    apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    funext g
    rw [hex.choose_spec Φ g, hI Φ g]
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    have hc := P.hecke_convolution_mem_holds H₁ K₁ ℂ hK f hf f' hf'
    rw [hTa _ hc, Module.End.mul_apply, hTa f hf, hTa f' hf']
    exact act_mul hK hf hf' fun k hk g => form_right Φ.2 g hk (one_mem _)
  · apply LinearMap.ext
    intro Φ
    apply Subtype.ext
    have hc : c • f + f' ∈ Hecke ℂ K₁ := Submodule.add_mem _ (Submodule.smul_mem _ c hf) hf'
    rw [hTa _ hc]
    show _ = c • (T f Φ : H₁ × H₂ → V) + (T f' Φ : H₁ × H₂ → V)
    rw [hTa f hf, hTa f' hf']
    funext g
    show (∑ᶠ x : H₁ ⧸ K₁, (c • f + f') x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) =
      c • (∑ᶠ x : H₁ ⧸ K₁, f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) +
        ∑ᶠ x : H₁ ⧸ K₁, f' x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))
    have hA : Function.HasFiniteSupport
        (fun x : H₁ ⧸ K₁ => f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) := fin_act hK hf _ g
    have hB : Function.HasFiniteSupport
        (fun x : H₁ ⧸ K₁ => f' x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) := fin_act hK hf' _ g
    have hC : Function.HasFiniteSupport
        (fun x : H₁ ⧸ K₁ => c • f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1))) :=
      Set.Finite.subset hA fun x hx h0 => hx (by
        show c • f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1)) = 0
        rw [show f x.out • (Φ : H₁ × H₂ → V) (g * (x.out, 1)) = 0 from h0, smul_zero])
    rw [smul_finsum' c hA, ← finsum_add_distrib hC hB]
    refine finsum_congr fun x => ?_
    simp [add_smul, mul_smul]

end Abstract

private theorem comm_of_open {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H)
    (ho : IsOpen (K : Set H)) (hc : IsCompact (K : Set H)) : IsCommensurated K := by
  intro g
  have : CompactSpace K := isCompact_iff_compactSpace.1 hc
  have h1 : IsOpen ((K.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) := by
    rw [Subgroup.coe_map]
    exact ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ ho
  have h2 : IsOpen (((K.map (MulAut.conj g).toMonoidHom).subgroupOf K : Subgroup K) : Set K) :=
    h1.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ h2
  exact Subgroup.index_ne_zero_iff_finite.2 this

end UpperTheory.Gal.Spc

theorem UpperTheory.Gal.Spc.opAlg :
    UpperTheory.Gal.Spc.OpAlg := by
  intro p _ G Lv V _ _ ξ B
  exact UpperTheory.Gal.Spc.abs_main B.emb Lv.K.toSubgroup (UpperTheory.Gal.LocalSmoothExtension.Kp G) (ξ.comp (GlobalTheory.LKCx.grp G B.β).subtype)
    (UpperTheory.Gal.Spc.comm_of_open _ Lv.K.isOpen Lv.compact)
end
end

