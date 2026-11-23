module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2018
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZero
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.BaryFin

variable {X : Type} [AddCommGroup X]

theorem toReal_zero' : toReal (0 : LinearMap.BilinForm ℤ X) = 0 := LinearMap.ext₂ fun a b => by simp

theorem eq_zero_of_genRank_eq_zero {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (h : genRank γ = 0) (i : Fin m) :
    γ i = 0 := by
  unfold genRank at h
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  obtain ⟨a, ha, e⟩ := Module.finrank_eq_zero_iff.1 h ⟨γ i, Submodule.subset_span ⟨i, rfl⟩⟩
  have e' : a • γ i = 0 := congrArg Subtype.val e
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ e' y z
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this ⊢
  exact (mul_eq_zero.1 this).resolve_left ha

theorem inRCone_smul_iff {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) {k : ℕ}
    (hk : 0 < k) : InRCone γ ((k : ℤ) • β) ↔ InRCone γ β := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => c i / k, fun i => div_nonneg (hc i) hk'.le, LinearMap.ext₂ fun a b => ?_⟩
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢
    push_cast at this
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← this]
    field_simp
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => k * c i, fun i => mul_nonneg hk'.le (hc i), LinearMap.ext₂ fun a b => ?_⟩
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢
    push_cast
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

variable {O : Type} [CommRing O] {bar : O → O} {q : ℕ}

theorem eq_zero_of_label_nonpos {ψ lab : InvFun O} (hlab : IsCarrierDim bar q ψ lab) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {b : ℕ}
    {v : Fin b → LinearMap.BilinForm ℤ X} (hv : IsCell bar ψ v) (k : Fin b) (hk : lab.evalZ (v k) ≤ 0) : v k = 0 := by
  have key := hlab X hX (v k) (hv.mem k) (hv.nonneg k)
  rw [key] at hk
  have h0 := Nat.cast_nonpos.1 hk
  have hS : ({n : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ (v k) ∧
      genRank γ = n}).Nonempty := ⟨_, b, v, hv, inRCone_self v k, rfl⟩
  obtain ⟨m, γ, -, ⟨c, -, hc⟩, hr⟩ := Nat.sInf_mem hS
  rw [h0] at hr
  have hz := eq_zero_of_genRank_eq_zero γ hr
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hc y z
  simp [hz, LinearMap.sum_apply] at this
  simpa using this


variable (O bar q) in
theorem simpLab_of_isBaryStage_zero (ψ lab φ : InvFun O) (hlab : IsCarrierDim bar q ψ lab)
    (hφ : IsBaryStage bar q ψ lab φ 0) : SimpLab bar q φ lab := by
  refine ⟨fun X _ _ _ _ hX β hβ hp k hk => ?_, fun X _ _ _ _ hX m γ hγ => ?_⟩
  · have hp' : ∀ y, 0 ≤ ((k : ℤ) • β) y y := fun y => by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (hp y)
    rw [hlab X hX _ (Submodule.smul_mem _ _ hβ) hp', hlab X hX β hβ hp]
    simp only [inRCone_smul_iff _ _ hk]
  · obtain ⟨b, a, v, u, hc, hv, hin, hinj, -, hle, -, hli⟩ := hφ.2.2 X hX m γ hγ
    have hv0 : ∀ k, v k = 0 := fun k => eq_zero_of_label_nonpos hlab hX hv k
      (by simpa using hle (v k) (hv.mem k) (hv.nonneg k) (inRCone_self v k))
    have hu : IsCell bar φ u := by
      refine ⟨fun j => by simpa using hc.mem (Fin.natAdd b j), fun j => by simpa using hc.nonneg (Fin.natAdd b j),
        ?_, ?_⟩
      · have := linearOn_comp hc.linear (⟨Fin.natAdd b, fun x y h => by simpa using h⟩ : Fin a ↪ Fin (b + a))
        convert this using 1
        funext i
        exact (Fin.append_right v u i).symm
      · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hc.strict
        refine ⟨N, ℓ, hN, fun i => by simpa using h1 (Fin.natAdd b i), h2, fun β hβ hp he => ?_⟩
        obtain ⟨k, c, hk, hc'⟩ := h3 β hβ hp he
        refine ⟨k, fun i => c (Fin.natAdd b i), hk, ?_⟩
        rw [hc', Fin.sum_univ_add]
        simp [hv0]
    refine ⟨a, u, hu, Fintype.linearIndependent_iff.2 fun c hc0 i => congrFun (hli 0 c (by rw [hc0]; simp)) i,
      hinj, fun j => ?_⟩
    obtain ⟨c, hc0, h⟩ := hin j
    refine ⟨fun i => c (Fin.natAdd b i), fun i => hc0 _, ?_⟩
    rw [h, Fin.sum_univ_add]
    simp [hv0, toReal_zero']

end GlobalTheory.PolFan.BaryFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecOfAnypoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CarrySpec

theorem upper_mul {n : ℕ} {R : Type} [CommRing R] {M N : Matrix (Fin n) (Fin n) R}
    (hM : ∀ a i, i < a → M a i = 0) (hN : ∀ a i, i < a → N a i = 0) :
    (∀ a i, i < a → (M * N) a i = 0) ∧ ∀ i, (M * N) i i = M i i * N i i := by
  first
  | exact @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul
  | (apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperTriangularMul.upperTriangular_mul ..)

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (ρ : R →+* R') (ψ : R' →+* R'') :
    spMap (ψ.comp ρ) = spMap ψ ≫ spMap ρ := by
  simp [spMap, Spec.map_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem isMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {φ : c.F →+* R} {φ' : c.F →+* R'}
    {φ'' : c.F →+* R''} {x : Sp R ⟶ Z.X} {x' : Sp R' ⟶ Z.X} {x'' : Sp R'' ⟶ Z.X} {f : EigFrame Z φ x}
    {f' : EigFrame Z φ' x'} {f'' : EigFrame Z φ'' x''} {ρ : R →+* R'} {ψ : R' →+* R''}
    (h1 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ρ f') (h2 : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f' embτ basisIdx) ψ f'') : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) (ψ.comp ρ) f'' := fun τ i => by
  rw [h2 τ i, h1 τ i, GlobalTheory.ShFam.CarriesAt.spMap_dualMap_comp, Category.assoc]

theorem tri_of_co {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' : c.F →+* R'} {x : Sp R ⟶ Z.X}
    {x' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {f' g : EigFrame Z φ' x'} (hf : (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v f embτ basisIdx) ψ f')
    (hx : x' = spMap ψ ≫ x) (hφ : φ' = ψ.comp φ) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ)
    (hu : ∀ τ a i, i < a → f'.co g τ a i = 0) (hd : ∀ τ i, f'.co g τ i i = t τ i) : f.Tri ψ g t :=
  ⟨hx, hφ, fun τ i => ⟨fun a => f'.co g τ a i, hd τ i, fun k hk => hu τ k i hk, by
    have := f'.co_spec g τ i
    rwa [funext (hf τ)] at this⟩⟩

theorem tri_spec {R V L k : Type} [CommRing R] [CommRing V] [CommRing L] [CommRing k]
    {φ₁ : c.F →+* R} {x₁ : Sp R ⟶ Z.X} (f : EigFrame Z φ₁ x₁) (ρ : R →+* V) (ν : V →+* L)
    (hν : Function.Injective ν) (r : V →+* k) {φV : c.F →+* V} {xV : Sp V ⟶ Z.X} (hxV : xV = spMap ρ ≫ x₁)
    (gV : EigFrame Z φV xV) {φL : c.F →+* L} {xL : Sp L ⟶ Z.X} (gL : EigFrame Z φL xL)
    (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hL : gV.Tri ν gL tL)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (hfL : f.Tri (ν.comp ρ) gL t')
    {φk : c.F →+* k} {xk : Sp k ⟶ Z.X} (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ)
    (hk : gV.Tri r gk tk) : ∃ t'' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri (r.comp ρ) gk t'' := by
  have hφV : φV = ρ.comp φ₁ := RingHom.ext fun a => hν (by
    have := RingHom.congr_fun (hL.2.1.symm.trans hfL.2.1) a
    simpa using this)
  obtain ⟨h, hh⟩ := EigFrame.exists_isMap f ρ hφV hxV
  obtain ⟨gVL, hgVL⟩ := EigFrame.exists_isMap gV ν hL.2.1 hL.1
  obtain ⟨hLf, hhL⟩ := EigFrame.exists_isMap h ν hL.2.1 hL.1
  have hfhL : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (ν.comp ρ) hLf := isMap_comp hh hhL

  have hA : ∀ τ, (∀ a i, i < a → h.co gV τ a i = 0) := fun τ a i hia => by
    obtain ⟨hU, -⟩ := EigFrame.Tri.co τ hfL hfhL
    obtain ⟨hW, -⟩ := EigFrame.Tri.co τ hL hgVL
    have hmap := EigFrame.IsMap.co τ hhL hgVL hL.1
    have hmul := EigFrame.co_mul hLf gVL gL τ
    have hWu := EigFrame.isUnit_det_co gVL gL τ
    set W := gVL.co gL τ
    have hWt : W.BlockTriangular id := fun a b h => hW a b h
    letI := Matrix.invertibleOfIsUnitDet W hWu
    have hWi : W⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hWt
    have hM : hLf.co gVL τ = hLf.co gL τ * W⁻¹ := by
      rw [← hmul, Matrix.mul_nonsing_inv_cancel_right _ _ hWu]
    have hP : (hLf.co gL τ * W⁻¹).BlockTriangular id :=
      Matrix.BlockTriangular.mul (fun a b h => hU a b h) hWi
    apply hν
    have := hP hia
    rw [← hM, hmap, Matrix.map_apply] at this
    rw [this, map_zero]
  have hAd : ∀ τ i, IsUnit (h.co gV τ i i) := fun τ i => by
    have hdet := EigFrame.isUnit_det_co h gV τ
    rw [Matrix.det_of_upperTriangular (fun a b hab => hA τ a b hab)] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => h.co gV τ j j) (Finset.mem_univ i)) hdet

  obtain ⟨hkf, hhk⟩ := EigFrame.exists_isMap h r hk.2.1 hk.1
  obtain ⟨gVk, hgVk⟩ := EigFrame.exists_isMap gV r hk.2.1 hk.1
  have hfhk : (_root_.GlobalTheory.ShFam.EigFrame.IsMap f) (r.comp ρ) hkf := isMap_comp hh hhk
  have hco : ∀ τ, hkf.co gk τ = (h.co gV τ).map r * gVk.co gk τ := fun τ => by
    rw [← EigFrame.IsMap.co τ hhk hgVk hk.1, EigFrame.co_mul]
  have key : ∀ τ, (∀ a i, i < a → hkf.co gk τ a i = 0) ∧ ∀ i, hkf.co gk τ i i = r (h.co gV τ i i) * tk τ i := by
    intro τ
    obtain ⟨hN, hNd⟩ := EigFrame.Tri.co τ hk hgVk
    have hm := upper_mul (M := (h.co gV τ).map r) (fun a i hia => by rw [Matrix.map_apply, hA τ a i hia, map_zero]) hN
    rw [hco]
    exact ⟨hm.1, fun i => by rw [hm.2, Matrix.map_apply, hNd]⟩
  refine ⟨fun τ i => ((hAd τ i).map r).unit * tk τ i, tri_of_co hfhk ?_ ?_ _ (fun τ => (key τ).1) fun τ i => ?_⟩
  · rw [hk.1, hxV, spMap_comp, Category.assoc]
  · rw [hk.2.1, hφV, RingHom.comp_assoc]
  · rw [(key τ).2, Units.val_mul, IsUnit.unit_spec]

end GlobalTheory.CarrySpec

namespace GlobalTheory.CarrySpec

open MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem spec_of_anypoint (hany : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (k : Type) [Field k] (φ : c.F →+* k) (x : Sp k ⟶ Z.X) (g : EigFrame Z φ x) (p : Sp k ⟶ C.Y.X), C.Carries p g → ∀ (y : C.Y.X) (ψ : C.Y.X.presheaf.stalk y →+* k) (φ₁ : c.F →+* C.Y.X.presheaf.stalk y) (f : EigFrame Z φ₁ (stalkPt C.Y y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), p = spMap ψ ≫ stalkPt C.Y y → f.Tri (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) C.f0 t → ∃ t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ, f.Tri ψ g t') : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (V : Type) [CommRing V] [IsLocalRing V] (L : Type) [Field L] (ν : V →+* L), Function.Injective ν → ∀ (k : Type) [Field k] (r : V →+* k), RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ (q : Sp V ⟶ C.Y.X) (φV : c.F →+* V) (xV : Sp V ⟶ Z.X), xV = q ≫ C.π ≫ genι Z → ∀ (gV : EigFrame Z φV xV) (φL : c.F →+* L) (xL : Sp L ⟶ Z.X) (gL : EigFrame Z φL xL) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ), gV.Tri ν gL tL → C.Carries (spMap ν ≫ q) gL → ∀ (φk : c.F →+* k) (xk : Sp k ⟶ Z.X) (gk : EigFrame Z φk xk) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), gV.Tri r gk tk → C.Carries (spMap r ≫ q) gk := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V _ _ L _ ν hν k _ r _ q φV xV hxV gV φL xL gL tL hL hcar φk xk gk tk hk
  set y₀ := q (IsLocalRing.closedPoint V)
  set ρ := (Scheme.stalkClosedPointTo (R := CommRingCat.of V) q).hom
  have hq : spMap ρ ≫ stalkPt C.Y y₀ = q := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of V) q
  obtain ⟨φ₁, f, t, hf, -⟩ := C.gr_spec y₀
  have hpL : spMap ν ≫ q = spMap (ν.comp ρ) ≫ stalkPt C.Y y₀ :=
    (congrArg (spMap ν ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc])
  obtain ⟨t', hfL⟩ := hany E H Dw l Xo c O β Z F e C L φL xL gL (spMap ν ≫ q) hcar y₀ (ν.comp ρ) φ₁ f t hpL hf
  have hxV' : xV = spMap ρ ≫ (stalkPt C.Y y₀ ≫ C.π ≫ genι Z) :=
    hxV.trans ((congrArg (· ≫ C.π ≫ genι Z) hq).symm.trans (Category.assoc _ _ _))
  obtain ⟨t'', htri⟩ := tri_spec f ρ ν hν r hxV' gV gL tL hL t' hfL gk tk hk
  exact ⟨y₀, r.comp ρ, φ₁, f, t, t'',
    (congrArg (spMap r ≫ ·) hq).symm.trans (by rw [spMap_comp, Category.assoc]), hf, htri⟩

end GlobalTheory.CarrySpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Depth

variable {O : Type} [CommRing O] (bar : O → O) (ψ w : InvFun O)

def IsStarDepth {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
    v ∈ balForms bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v ∧ B ∈ rcone γ ∧ B - t • toReal v ∈ rcone γ

def depthSet (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Set ℝ :=
  {t | ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module O X₁) (_ : Module.Finite O X₁) (r : (Fin n → O) →ₗ[O] X₁)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧ (∀ x, (∀ y, B₁ x y = 0) → x = 0) ∧
    (∀ a b, B a b = B₁ (r a) (r b)) ∧ IsStarDepth bar ψ w B₁ t}

variable {bar ψ w}

theorem depthSet_comp {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r)
    (B : (Fin m → O) → (Fin m → O) → ℝ) : depthSet bar ψ w n (fun a b => B (r a) (r b)) = depthSet bar ψ w m B := by
  ext t
  constructor
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    have hker : LinearMap.ker r ≤ LinearMap.ker ρ := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      refine hrad _ fun y => ?_
      obtain ⟨y', rfl⟩ := hρ y
      have h1 := hB x y'
      have h2 := hB 0 y'
      simp only [hx, map_zero, LinearMap.zero_apply] at h1 h2
      rw [← h1, h2]
    let ρ' : (Fin m → O) →ₗ[O] X₁ :=
      (LinearMap.ker r).liftQ ρ hker ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
    have hρ' : ∀ a, ρ' (r a) = ρ a := fun a => by
      have : (r.quotKerEquivOfSurjective hr).symm (r a) = Submodule.Quotient.mk a := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
    refine ⟨X₁, i1, i2, i3, ρ', B₁, fun x => ?_, hrad, fun a b => ?_, hd⟩
    · obtain ⟨a, rfl⟩ := hρ x
      exact ⟨r a, hρ' a⟩
    · obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      rw [hρ', hρ']
      exact hB a b
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    exact ⟨X₁, i1, i2, i3, ρ ∘ₗ r, B₁, hρ.comp hr, hrad, fun a b => hB (r a) (r b), hd⟩

theorem depthSet_zero (B : (Fin 0 → O) → (Fin 0 → O) → ℝ) : depthSet bar ψ w 0 B = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, hρ, _, _, _, _, _, v, _, _, _, hv, _⟩ => ?_
  haveI : Subsingleton X₁ := ⟨fun x y => by
    obtain ⟨a, rfl⟩ := hρ x
    obtain ⟨b, rfl⟩ := hρ y
    rw [Subsingleton.elim a b]⟩
  rw [InvFun.evalZ, w.eval_of_subsingleton] at hv
  exact zero_ne_one hv

variable (bar ψ w)

def starDepth : InvFun O where
  toFun n B := sSup (depthSet bar ψ w n B)
  inv n m r hr B := by rw [depthSet_comp hr]
  zero B := by rw [depthSet_zero, Real.sSup_empty]

def starFun (K D : ℕ) : InvFun O where
  toFun n B := D * (K * ψ.toFun n B + (starDepth bar ψ w).toFun n B)
  inv n m r hr B := by simp only [InvFun.inv _ _ _ r hr]
  zero B := by simp only [InvFun.zero, mul_zero, add_zero]

variable {bar ψ w}

theorem starDepth_toFun_nonneg (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : 0 ≤ (starDepth bar ψ w).toFun n B :=
  Real.sSup_nonneg fun _ h => h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1

theorem starDepth_eval_nonneg {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) :
    0 ≤ (starDepth bar ψ w).eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  exact starDepth_toFun_nonneg n _

theorem starFun_eval {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ) (B : X → X → ℝ) :
    (starFun bar ψ w K D).eval X B = D * (K * ψ.eval X B + (starDepth bar ψ w).eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr, InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]
  rfl

theorem starFun_evalZ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (β : LinearMap.BilinForm ℤ X) :
    (starFun bar ψ w K D).evalZ β = D * (K * ψ.evalZ β + (starDepth bar ψ w).evalZ β) :=
  starFun_eval K D _

theorem starFun_evalR {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalR (starFun bar ψ w K D) B = D * (K * evalR ψ B + evalR (starDepth bar ψ w) B) :=
  starFun_eval K D _

theorem starDepth_zeroFun (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : (starDepth bar ψ (zeroFun O)).toFun n B = 0 := by
  have : depthSet bar ψ (zeroFun O) n B = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, _, _, _, _, _, _, v, _, _, _, hv, _⟩ => by
      rw [zeroFun_evalZ] at hv
      exact zero_ne_one hv
  show sSup _ = 0
  rw [this, Real.sSup_empty]

end Depth

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem isTwInv_starFun {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hd : IsTwInv H (starDepth H.bar ψ w)) (K D : ℕ) :
    IsTwInv H (starFun H.bar ψ w K D) := fun σ hσ n B => by
  show _ * (_ * _ + _) = _ * (_ * _ + _)
  rw [hψ σ hσ n B, hd σ hσ n B]

end Twist

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKAtWitnesses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Top.Bl.WitSK

def of_sigma_eq {α : Type*} {β : α → Type*} {a b : Σ x, β x} (h : a = b) (P : ∀ x, β x → Sort*) (hb : P b.1 b.2) :
    P a.1 a.2 := by
  subst h; exact hb

end GlobalTheory.Mem.Top.Bl.WitSK

end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsPolarizedModel
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.FanTheta

theorem isLB_detOm_of_smooth {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (hpq : 1 ≤ D.p + D.q)
    (hsm : SmoothOfRelativeDimension D.dim (genStr Y)) : (GlobalTheory.FlagMod.detOm Y).IsLB := by
  have e : spMap (RingHom.id c.F) = 𝟙 _ := by
    simp [spMap]
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [e]; infer_instance
  haveI : IsIso (genι Y) := inferInstance
  have hs : SmoothOfRelativeDimension D.dim Y.s := by
    have hw : Y.s = inv (genι Y) ≫ genStr Y ≫ spMap (RingHom.id c.F) := by
      rw [← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [hw]
    have := (inferInstance :
      SmoothOfRelativeDimension (0 + (D.dim + 0)) (inv (genι Y) ≫ genStr Y ≫ spMap (RingHom.id c.F)))
    simpa using this
  have hθ : GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := _root_.GlobalTheory.ThetaNormal.hasTheta_of_smooth E H D hpq l Xo c Y hs
  exact GlobalTheory.FlagMod.isLB_detOm (GlobalTheory.CompHS.TorFlagEx.pushInvertible_of_hasTheta Y hθ)

end GlobalTheory.FanTheta
end

