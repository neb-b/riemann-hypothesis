module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousOfDense

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHom
section
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace TensorProduct GlobalTheory.AnPer

namespace GlobalTheory.TaylorHom

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)}

theorem eventually_mem {w : Fin g → ℂ} (h : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, w) : Tot I g) ∈ W := by
  have hc : Continuous fun z : I → ℂ ↦ ((z, w) : Tot I g) := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds h)

theorem analyticAt_slice (h : Hol W) {w : Fin g → ℂ} (hw : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    AnalyticAt ℂ (fun z : I → ℂ ↦ h.fn (z, w)) 0 := by
  have hp : AnalyticAt ℂ (fun z : I → ℂ ↦ ((z, w) : Tot I g)) 0 :=
    analyticAt_id.prod analyticAt_const
  exact AnalyticAt.comp (g := h.fn) (f := fun z : I → ℂ ↦ ((z, w) : Tot I g)) (h.analytic _ hw) hp

def coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W) : Hol W₀ :=
  Hol.mk (fun p ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v) fun p hp ↦
    AnalyticAt.comp (g := fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) (f := Prod.snd)
      (GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v (h.analytic _ (hW p hp))).1 analyticAt_snd

theorem fn_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    {p : Tot I₀ g} (hp : p ∈ W₀) : (coef hW k v h).fn p = iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v := by
  unfold coef
  exact Hol.fn_mk _ _ hp

theorem dw_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    (a : Fin g) : dw a (coef hW k v h) = coef hW k v (dw a h) := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hH : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  obtain ⟨hG, hG'⟩ := GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v hH

  have hL : (dw a (coef hW k v h)).fn p =
      fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) p.2 (Pi.single a 1) := by
    rw [show dw a (coef hW k v h) =
        Hol.der ((0, Pi.single a 1) : Tot I₀ g) (coef hW k v h) from rfl, Hol.fn_der _ _ hp,
      Hol.fderiv_fn_congr (F := fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) _
        (fun q hq ↦ fn_coef hW k v h hq) hp]
    have hc := (hG.differentiableAt.hasFDerivAt.comp p (hasFDerivAt_snd (p := p))).fderiv
    rw [show (fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) =
        (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) ∘ Prod.snd from rfl, hc]
    rfl
  have hR : (coef hW k v (dw a h)).fn p =
      iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1)) 0 v := by
    rw [fn_coef hW k v (dw a h) hp]
    have hev : (fun z : I → ℂ ↦ (dw a h).fn (z, p.2)) =ᶠ[𝓝 0]
        fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1) := by
      filter_upwards [eventually_mem (hW p hp)] with z hz
      exact Hol.fn_der _ _ hz
    exact congrFun (congrArg DFunLike.coe ((hev.iteratedFDeriv (𝕜 := ℂ) k).eq_of_nhds)) v
  rw [hL, hR]
  exact hG' _

variable [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D]

def poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W) : D ⊗[ℂ] Hol W₀ :=
  ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I,
    ((k.factorial : ℂ)⁻¹ • ∏ a, t (s a)) ⊗ₜ[ℂ] coef hW k (fun a ↦ Pi.single (s a) 1) h

theorem ev_poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W)
    (p : Tot I₀ g) (hp : p ∈ W₀) :
    Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
      (poly hW N t h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [poly, map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
    Algebra.ofId_apply, Hol.ev_apply, fn_coef hW _ _ h hp, GlobalTheory.PeriodFamily.taylor]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]

theorem exists_taylor_algHom : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D]
    [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot I₀ g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
    ∃ Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : Tot I₀ g) (hp : p ∈ W₀),
      Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
        (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) ∧
      ∀ a h, Ta (dw (W := W) a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (Ta h) := by
  intro I I₀ _ _ _ g D _ _ N t ht W W₀ hW

  have slice_eq : ∀ {p : Tot I₀ g} (_ : p ∈ W₀) {F : (I → ℂ) → ℂ} (x : Hol W),
      (∀ z, ((z, p.2) : Tot I g) ∈ W → x.fn (z, p.2) = F z) →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ x.fn (z, p.2)) = GlobalTheory.PeriodFamily.taylor N t F := by
    intro p hp F x hx
    apply GlobalTheory.PeriodFamily.taylor_congr_germ
    filter_upwards [eventually_mem (hW p hp)] with z hz
    exact hx z hz
  have hconst : ∀ c : ℂ, poly hW N t (algebraMap ℂ (Hol W) c) = algebraMap ℂ (D ⊗[ℂ] Hol W₀) c := by
    intro c
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [ev_poly, AlgHom.commutes, slice_eq hp (F := fun _ ↦ c) _ fun z hz ↦ Hol.fn_algebraMap c hz,
      GlobalTheory.PeriodFamily.taylor_const_fun]
  have hadd : ∀ x y : Hol W, poly hW N t (x + y) = poly hW N t x + poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_add (f := _), ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) + y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_add x y hz,
      GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  have hmul : ∀ x y : Hol W, poly hW N t (x * y) = poly hW N t x * poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_mul, ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) * y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_mul x y hz,
      GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  refine ⟨{ toFun := poly hW N t
            map_one' := by simpa only [map_one] using hconst 1
            map_mul' := hmul
            map_zero' := by simpa only [map_zero] using hconst 0
            map_add' := hadd
            commutes' := hconst }, fun h p hp ↦ ev_poly hW N t h p hp, fun a h ↦ ?_⟩
  show poly hW N t (dw a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (poly hW N t h)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [poly, map_sum, LinearMap.lTensor_tmul]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← dw_coef]
  rfl

end GlobalTheory.TaylorHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHomHolomorphicNilpotent
section
set_option autoImplicit false

open Filter Topology TopologicalSpace

namespace GlobalTheory.AnPer.TaylorHom

open GlobalTheory.AnPer GlobalTheory.PeriodFamily

variable {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R]

theorem fn_add_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f + g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z + g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_add f g hq

theorem fn_mul_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (f g : Hol V) :
    (f * g).fn =ᶠ[𝓝 0] fun z ↦ f.fn z * g.fn z := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_mul f g hq

theorem fn_algebraMap_eventually {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    (algebraMap ℂ (Hol V) c).fn =ᶠ[𝓝 0] fun _ ↦ c := by
  filter_upwards [V.isOpen.mem_nhds h0] with q hq using Hol.fn_algebraMap c hq

theorem taylor_algebraMap (N : ℕ) (t : I → R) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) (c : ℂ) :
    GlobalTheory.PeriodFamily.taylor N t (algebraMap ℂ (Hol V) c).fn = algebraMap ℂ R c := by
  rw [taylor_congr_germ N t _ _ (fn_algebraMap_eventually h0 c), taylor_const_fun]

noncomputable def taylorHom (N : ℕ) (t : I → R) (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0)
    (V : Opens (I → ℂ)) (h0 : (0 : I → ℂ) ∈ V) : Hol V →ₐ[ℂ] R where
  toFun f := GlobalTheory.PeriodFamily.taylor N t f.fn
  map_one' := by
    have h : (1 : Hol V) = algebraMap ℂ (Hol V) 1 := (map_one _).symm
    change GlobalTheory.PeriodFamily.taylor N t (1 : Hol V).fn = 1
    rw [h, taylor_algebraMap N t h0, map_one]
  map_mul' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f * g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn * GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_mul_eventually h0 f g)]
    exact taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  map_zero' := by
    have h : (0 : Hol V) = algebraMap ℂ (Hol V) 0 := (map_zero _).symm
    change GlobalTheory.PeriodFamily.taylor N t (0 : Hol V).fn = 0
    rw [h, taylor_algebraMap N t h0, map_zero]
  map_add' f g := by
    change GlobalTheory.PeriodFamily.taylor N t (f + g).fn = GlobalTheory.PeriodFamily.taylor N t f.fn + GlobalTheory.PeriodFamily.taylor N t g.fn
    rw [taylor_congr_germ N t _ _ (fn_add_eventually h0 f g)]
    exact taylor_add_of_analyticAt N t _ _ (f.analytic 0 h0) (g.analytic 0 h0)
  commutes' c := taylor_algebraMap N t h0 c

end GlobalTheory.AnPer.TaylorHom

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily

theorem GlobalTheory.AnPer.exists_taylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (V : Opens (I → ℂ)), 0 ∈ V → ∃ θ : Hol V →ₐ[ℂ] R, ∀ f, θ f = GlobalTheory.PeriodFamily.taylor N t f.fn := by
  intro I _ _ R _ _ N t ht V h0
  exact ⟨GlobalTheory.AnPer.TaylorHom.taylorHom N t ht V h0, fun f ↦ rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitsComparingLiftedTransitionsFactor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftUnits

theorem le_pre_inf {X Y : Scheme.{0}} {y : Y ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ y ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V) :
    ⊤ ≤ y ⁻¹ᵁ (U ⊓ V) := fun _ hp => ⟨hU hp, hV hp⟩

theorem le_pre_of_eq {X Y Z : Scheme.{0}} {f : Z ⟶ Y} {y : Y ⟶ X} {z : Z ⟶ X} (e : f ≫ y = z) {U : X.Opens}
    (hU : ⊤ ≤ y ⁻¹ᵁ U) : ⊤ ≤ z ⁻¹ᵁ U := by
  subst e
  intro p _
  exact hU (Set.mem_univ (f p))

theorem map_evalAt {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') {x : Sp C ⟶ X}
    {y : Sp C' ⟶ X} (e : spMap φ ≫ x = y) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) :
    φ (evalAt x U h f) = evalAt y U h' f := by
  subst e
  obtain ⟨_, hn, -⟩ := GlobalTheory.EvalNat.evalAt_natural φ x U h
  exact (hn f).symm

theorem evalAt_g_mul {X : Scheme.{0}} {C : Type} [CommRing C] {M : LB X} (hM : M.IsLB) (y : Sp C ⟶ X) {a b c : M.ι}
    (ha : ⊤ ≤ y ⁻¹ᵁ M.U a) (hb : ⊤ ≤ y ⁻¹ᵁ M.U b) (hc : ⊤ ≤ y ⁻¹ᵁ M.U c) :
    evalAt y _ (le_pre_inf ha hb) (M.g a b).val * evalAt y _ (le_pre_inf hb hc) (M.g b c).val =
      evalAt y _ (le_pre_inf ha hc) (M.g a c).val := by
  have hres : ∀ {U V : X.Opens} (h : V ≤ U) (u : (Γ(X, U))ˣ),
      ((res h u : (Γ(X, V))ˣ) : Γ(X, V)) = (X.presheaf.map (homOfLE h).op).hom (u : Γ(X, U)) := fun _ _ => rfl
  have q2 := congrArg (fun u => evalAt y (M.U a ⊓ M.U b ⊓ M.U c) (le_pre_inf (le_pre_inf ha hb) hc) (Units.val u))
    (hM.cocycle a b c)
  simp only [Units.val_mul, map_mul, hres] at q2
  obtain ⟨_, -, hr⟩ := GlobalTheory.EvalNat.evalAt_natural (RingHom.id C) y (M.U a ⊓ M.U b ⊓ M.U c) (le_pre_inf (le_pre_inf ha hb) hc)
  rw [hr (M.U a ⊓ M.U b) (le_trans inf_le_left le_rfl) (le_pre_inf ha hb),
    hr (M.U b ⊓ M.U c) (le_inf (le_trans inf_le_left inf_le_right) inf_le_right) (le_pre_inf hb hc),
    hr (M.U a ⊓ M.U c) (le_inf (le_trans inf_le_left inf_le_left) inf_le_right) (le_pre_inf ha hc)]
  exact q2

theorem isUnit_evalAt {X : Scheme.{0}} {C : Type} [CommRing C] (y : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ y ⁻¹ᵁ U)
    (u : Γ(X, U)ˣ) : IsUnit (evalAt y U h u.val) := u.isUnit.map (evalAt y U h)

theorem mul_eq_one_of_covolume_identity {R : Type} [CommRing R] {g₁ g₂ g₃ g₄ g₅ u v w A S f : R} (c₁ : g₁ * g₂ = g₅) (c₂ : g₃ * g₄ = g₅)
    (hu : u = g₁) (hv : v = g₂ * S) (hw : w = g₃ * f) (hf : f = g₄ * A * S) : u * v * A = w := by
  subst hu hv hw hf
  linear_combination (S * A) * c₁ - (S * A) * c₂

theorem exists_units : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X), M.IsLB → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ (fr : ∀ k, Hol (K.W k)) (a : Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) → (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) → ∀ (i : K.Obj → M.ι), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) → ∀ (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C), (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) → ∃ e : ∀ T : K.Obj, (T.C)ˣ, (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) := by
  intro I _ g Λ _ F B _ X s σ K r M hM j hj fr a hfr hcoc i hi uu huu
  have hjT : ∀ T : K.Obj, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (j T.k) := fun T =>
    le_pre_of_eq (f := spMap ((Ideal.Quotient.mk T.J).comp T.ρ)) (y := r.x T.k) rfl (hj T.k)
  have hlift : ∀ T : K.Obj, ∃ c : T.C, IsUnit c ∧ Ideal.Quotient.mk T.J c =
      @id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T.J (T.ρ (fr T.k)) := by
    intro T
    have hu : IsUnit (@id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T.J (T.ρ (fr T.k))) :=
      (isUnit_evalAt (r.obj T).x (le_pre_inf (hi T) (hjT T)) (M.g (i T) (j T.k))).mul
        (((hfr T.k).map T.ρ).map (Ideal.Quotient.mk T.J))
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (@id (T.C ⧸ T.J) (evalAt (r.obj T).x _ (le_pre_inf (hi T) (hjT T))
      (M.g (i T) (j T.k)).val) * Ideal.Quotient.mk T.J (T.ρ (fr T.k)))
    obtain ⟨d, hd⟩ := Ideal.Quotient.mk_surjective (((hu.unit⁻¹ : (T.C ⧸ T.J)ˣ)) : T.C ⧸ T.J)
    refine ⟨c, ?_, hc⟩
    have hmem : c * d - 1 ∈ T.J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, hd, map_one, IsUnit.mul_val_inv, sub_self]
    have hnil : IsNilpotent (c * d - 1) := by
      obtain ⟨n, hn⟩ := T.nil
      refine ⟨n, ?_⟩
      have hp := Ideal.pow_mem_pow hmem n
      rwa [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
    have hcd : IsUnit (c * d) := by
      have h1 := hnil.isUnit_one_add
      rwa [add_sub_cancel] at h1
    exact isUnit_of_mul_isUnit_left hcd
  choose c hcu hcε using hlift
  refine ⟨fun T => (hcu T).unit, ?_⟩
  intro T T' φ
  have hle : K.le φ.deg T'.k T.k := Charts.Hom.le φ
  have hiT : ⊤ ≤ (r.obj T').x ⁻¹ᵁ M.U (i T) :=
    le_pre_of_eq (f := spMap (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem)) (y := (r.obj T).x) (r.analyticChartsRealization_comp_point_eq φ) (hi T)
  have hjk : ⊤ ≤ (r.obj T').x ⁻¹ᵁ M.U (j T.k) :=
    le_pre_of_eq (f := spMap (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem)) (y := (r.obj T).x) (r.analyticChartsRealization_comp_point_eq φ) (hjT T)
  have hxk : ⊤ ≤ r.x T'.k ⁻¹ᵁ (M.U (j T'.k) ⊓ M.U (j T.k)) :=
    le_pre_inf (hj T'.k) (le_pre_of_eq (r.compat hle) (hj T.k))
  have c₁ := evalAt_g_mul hM (r.obj T').x (hi T') hiT hjk
  have c₂ := evalAt_g_mul hM (r.obj T').x (hi T') (hjT T') hjk
  have hu := huu T T' φ (le_pre_inf (hi T') hiT)
  have hS : Ideal.Quotient.mk T'.J (φ.φ (T.ρ (fr T.k))) =
      Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) :=
    Ideal.Quotient.eq.mpr (Close.sub_mem φ.close (fr T.k))
  have hv : Ideal.Quotient.mk T'.J (φ.φ (c T)) =
      @id (T'.C ⧸ T'.J) (evalAt (r.obj T').x _ (le_pre_inf hiT hjk) (M.g (i T) (j T.k)).val) *
        Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) := by
    have h1 : Ideal.Quotient.mk T'.J (φ.φ (c T)) =
        Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem (Ideal.Quotient.mk T.J (c T)) := by
      rfl
    have h2 : Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem (Ideal.Quotient.mk T.J (T.ρ (fr T.k))) =
        Ideal.Quotient.mk T'.J (φ.φ (T.ρ (fr T.k))) := by
      rfl
    rw [h1, hcε T, map_mul, h2, hS]
    congr 1
    exact map_evalAt (Ideal.quotientMap T'.J (φ.φ : T.C →+* T'.C) φ.mem) (x := (r.obj T).x) (y := (r.obj T').x)
      (r.analyticChartsRealization_comp_point_eq φ) _ (le_pre_inf hiT hjk) _
  have hf : Ideal.Quotient.mk T'.J (T'.ρ (fr T'.k)) =
      @id (T'.C ⧸ T'.J) (evalAt (r.obj T').x _ (le_pre_inf (hjT T') hjk) (M.g (j T'.k) (j T.k)).val) *
        Ideal.Quotient.mk T'.J (T'.ρ (a φ.deg T'.k)) * Ideal.Quotient.mk T'.J (T'.ρ (Charts.sh hle (fr T.k))) := by
    rw [hcoc φ.deg T'.k T.k hle hxk, map_mul, map_mul, map_mul, map_mul]
    congr 2
    exact map_evalAt ((Ideal.Quotient.mk T'.J).comp T'.ρ) (x := r.x T'.k) (y := (r.obj T').x) rfl _ _ _
  refine Ideal.Quotient.eq.mp ?_
  rw [map_mul, map_mul]
  exact mul_eq_one_of_covolume_identity (R := T'.C ⧸ T'.J) c₁ c₂ hu hv (hcε T') hf

end GlobalTheory.LiftUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilIsSubDPIdeal
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem fil_isSubDPIdeal : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (N : ℕ), 1 ≤ N →
    δ.IsSubDPIdeal (fil δ N) := by
  intro B _ J δ N hN
  refine ⟨GlobalTheory.Cris.ExpBij.dpFil_le δ hN, fun n hn j hj ↦ ?_⟩
  have h := GlobalTheory.Cris.ExpBij.dpow_mem_dpFil_mul δ hN hj n
  exact GlobalTheory.Cris.ExpBij.dpFil_anti δ (Nat.le_mul_of_pos_left N (Nat.pos_of_ne_zero hn)) h

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilProperties
section
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem map_fil_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C]
    {J' : Ideal C} (δ' : DividedPowers J') (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    (fil δ N).map f ≤ fil δ' N := by
  rw [Ideal.map_le_iff_le_comap, fil, Ideal.span_le]
  rintro _ ⟨l, h1, h2, rfl⟩
  have hJ : ∀ p ∈ l, f p.2 ∈ J' := fun p hp ↦ hf.ideal_comp (Ideal.mem_map_of_mem f (h1 p hp))
  refine Ideal.subset_span ⟨l.map fun p ↦ (p.1, f p.2), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hJ p hp
  · simpa [List.map_map, Function.comp_def] using h2
  · rw [map_list_prod, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun p hp ↦ ?_)
    simp only [Function.comp_apply]
    exact (hf.dpow_comp (n := p.1) p.2 (h1 p hp)).symm

theorem fil_properties : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J), fil δ 0 = ⊤ ∧ fil δ 1 = J ∧ (∀ m n, m ≤ n → fil δ n ≤ fil δ m) ∧ (∀ m n, fil δ m * fil δ n ≤ fil δ (m + n)) ∧ (∀ n, ∀ x ∈ J, δ.dpow n x ∈ fil δ n) ∧ (IsNilDP δ ↔ ∃ N, IsLev δ N) ∧ ∀ (C : Type) [CommRing C] (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → ∀ N, (fil δ N).map f ≤ fil δ' N := by
  intro B _ J δ
  refine ⟨fil_zero_eq_top δ, fil_one_eq δ, fun m n h ↦ GlobalTheory.Cris.ExpBij.dpFil_anti δ h, fun m n ↦ ?_,
    fun n x hx ↦ GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hx n, isDPNilpotent_iff_exists_isLevel δ,
    fun C _ J' δ' f hf N ↦ map_fil_le δ δ' f hf N⟩
  rw [Ideal.mul_le]
  exact fun a ha b hb ↦ GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ ha hb

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClosureThetaRatiosOfIsCl
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem RatModel.IsCl.subfield_eq_top_of_ratios {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {M : RatModel o Ω} {J : Type} {t : J → Ω} (h : M.IsCl t) (K : Subfield Ω)
    (hc : ∀ a, algebraMap o Ω a ∈ K) (hr : ∀ i j, t j / t i ∈ K) : K = ⊤ := by
  obtain ⟨i, hi⟩ := h.1 (genericPoint M.Z)
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi.1
  have hne : (U : Set M.Z).Nonempty := ⟨genericPoint M.Z, by rw [hD]; exact hi⟩
  let A : Subalgebra o Ω := { K.toSubring with algebraMap_mem' := hc }
  have hle : M.ringOn U ≤ A := by
    rw [hR]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    exact hr i j
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, -, rfl⟩ := RatModel.exists_eq_div hU hne x
  exact div_mem (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
    (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem finite_closure_theta_ratios_of_isCl (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω) (J : Type) (t : J → Ω) (h : M.IsCl t) :
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) Ω := by
  obtain ⟨x, hx⟩ := S.th_ne
  have htop := h.subfield_eq_top_of_ratios (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)}))
    (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
    (fun i j => Subfield.subset_closure (Or.inr ⟨(x, i), (x, j), (mul_div_mul_left _ _ hx).symm⟩))
  refine Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun y => ⟨⟨y, ?_⟩, rfl⟩
  rw [htop]
  exact Subfield.mem_top y

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFockJointHarmonicsHighestWeightOfShape
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.JointHarm

theorem finrank_joint_highest_of_shape :
    ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), JointShape p q r s μ μ' →
      Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓
        Submodule.span ℂ (jointHarm p q r s)) = 1 :=
  fun _ _ _ _ μ μ' => (joint_harmonics μ μ').1

end GlobalTheory.JointHarm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.JointHarm GlobalTheory.FockSeq in
theorem harmonic_homog_of_type : ∀ (p q r s : ℕ),
    (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P →
      P ∈ harm1 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
    (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P →
      P ∈ harm2 p q r s →
      ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) :=
  fun _ _ _ _ =>
    ⟨fun _ P h0 ht hh => isSide_one.homog_of_type isFockIsometry_embedding emb_injective
        Function.bijective_id h0 ht ((mem_harm1 P).1 hh),
      fun _ P h0 ht hh => isSide_two.homog_of_type isFockIsometry_embedding emb_injective
        Prod.swap_bijective h0 ht ((mem_harm2 P).1 hh)⟩

end GlobalTheory.FockAlg
end

