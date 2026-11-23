module

public import ReciprocityTheory.GroupCohomology.Bundle0003
public import ReciprocityTheory.GroupCohomology.Bundle0004
public import ReciprocityTheory.GroupCohomology.Bundle0006
public import ReciprocityTheory.GroupCohomology.ConnNatHolds
public import ReciprocityTheory.GroupCohomology.Bundle0005
public import ReciprocityTheory.GroupCohomology.InfRes
public import ReciprocityTheory.GroupCohomology.Bundle0007
public import ReciprocityTheory.GroupCohomology.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.GroupCohomology.LowLES
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal LowDeg

universe u

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R] {G G' : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

theorem lowLES_h0Equiv_pair {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (x : M.H 0) :
    cohomZeroEquivContinuous M' (P.hom.H 0 x) = P.h0 (cohomZeroEquivContinuous M x) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x

  exact Subtype.ext (congrArg P.u (congrArg y.1.1 (Subsingleton.elim _ _)))

end SlopeTestRemainingChoices

private theorem exact_of_linearEquiv_conj {R X₁ X₂ X₃ Y₁ Y₂ Y₃ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂] [AddCommGroup X₃] [Module R X₃]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂] [AddCommGroup Y₃] [Module R Y₃]
    {f : X₁ →ₗ[R] X₂} {g : X₂ →ₗ[R] X₃} {f' : Y₁ →ₗ[R] Y₂} {g' : Y₂ →ₗ[R] Y₃}
    (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂) (e₃ : X₃ ≃ₗ[R] Y₃)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (hg : ∀ x, e₃ (g x) = g' (e₂ x))
    (h : Function.Exact f g) : Function.Exact f' g' := by
  intro y
  obtain ⟨x, rfl⟩ := e₂.surjective y
  rw [← hg, LinearEquiv.map_eq_zero_iff, h x]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨e₁ z, (hf z).symm⟩
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := e₁.surjective w
    refine ⟨z, e₂.injective ?_⟩
    rw [hf]
    exact hw

private theorem injective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Injective f) : Function.Injective f' := by
  intro a b hab
  obtain ⟨x, rfl⟩ := e₁.surjective a
  obtain ⟨z, rfl⟩ := e₁.surjective b
  rw [← hf, ← hf] at hab
  rw [h (e₂.injective hab)]

private theorem surjective_of_linearEquiv_conj {R X₁ X₂ Y₁ Y₂ : Type*} [CommRing R]
    [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
    [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₂] [Module R Y₂]
    {f : X₁ →ₗ[R] X₂} {f' : Y₁ →ₗ[R] Y₂} (e₁ : X₁ ≃ₗ[R] Y₁) (e₂ : X₂ ≃ₗ[R] Y₂)
    (hf : ∀ x, e₂ (f x) = f' (e₁ x)) (h : Function.Surjective f) : Function.Surjective f' := by
  intro y
  obtain ⟨x, hx⟩ := h (e₂.symm y)
  refine ⟨e₁ x, ?_⟩
  rw [← hf, hx, LinearEquiv.apply_symm_apply]

theorem low_degree_long_exact_sequence : LowLESStatement.{u} := by
  intro R _ G _ _ _ A B C i p hadm
  have hses := admissibility_holds R G A B C i p hadm
  obtain ⟨⟨δ, hconn, hles⟩, -⟩ := lES_holds R _ _ _ i.hom p.hom hses

  have n0 : ∀ x : C.H 0, h1EquivOfOrderTwo A (δ 0 x) =
      ((h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap) (cohomZeroEquivContinuous C x) := by
    intro x
    show h1EquivOfOrderTwo A (δ 0 x) = h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm (cohomZeroEquivContinuous C x)))
    rw [LinearEquiv.symm_apply_apply]
  have n1 : ∀ x : C.H 1, h2EquivOfOrderTwo A (δ 1 x) =
      ((h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap) (h1EquivOfOrderTwo C x) := by
    intro x
    show h2EquivOfOrderTwo A (δ 1 x) = h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (h1EquivOfOrderTwo C x)))
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨(h1EquivOfOrderTwo A).toLinearMap ∘ₗ δ 0 ∘ₗ (cohomZeroEquivContinuous C).symm.toLinearMap,
    (h2EquivOfOrderTwo A).toLinearMap ∘ₗ δ 1 ∘ₗ (h1EquivOfOrderTwo C).symm.toLinearMap, ?_, ?_,
    injective_of_linearEquiv_conj (cohomZeroEquivContinuous A) (cohomZeroEquivContinuous B) (fun x => lowLES_h0Equiv_pair i x) hles.inj,
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous A) (cohomZeroEquivContinuous B) (cohomZeroEquivContinuous C) (fun x => lowLES_h0Equiv_pair i x)
      (fun x => lowLES_h0Equiv_pair p x) (hles.exB 0),
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous B) (cohomZeroEquivContinuous C) (h1EquivOfOrderTwo A) (fun x => lowLES_h0Equiv_pair p x)
      n0 (hles.exC 0),
    exact_of_linearEquiv_conj (cohomZeroEquivContinuous C) (h1EquivOfOrderTwo A) (h1EquivOfOrderTwo B) n0
      (fun x => h1Equiv_pair (P := i) (x := x)) (hles.exA 0),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo A) (h1EquivOfOrderTwo B) (h1EquivOfOrderTwo C) (fun x => h1Equiv_pair (P := i) (x := x))
      (fun x => h1Equiv_pair (P := p) (x := x)) (hles.exB 1),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo B) (h1EquivOfOrderTwo C) (h2EquivOfOrderTwo A) (fun x => h1Equiv_pair (P := p) (x := x))
      n1 (hles.exC 1),
    exact_of_linearEquiv_conj (h1EquivOfOrderTwo C) (h2EquivOfOrderTwo A) (h2EquivOfOrderTwo B) n1
      (fun x => h2Equiv_pair (P := i) (x := x)) (hles.exA 1),
    exact_of_linearEquiv_conj (h2EquivOfOrderTwo A) (h2EquivOfOrderTwo B) (h2EquivOfOrderTwo C) (fun x => h2Equiv_pair (P := i) (x := x))
      (fun x => h2Equiv_pair (P := p) (x := x)) (hles.exB 2),
    fun hsub => surjective_of_linearEquiv_conj (h2EquivOfOrderTwo B) (h2EquivOfOrderTwo C) (fun x => h2Equiv_pair (P := p) (x := x))
      (fun y => (hles.exC 2 y).1 (@Subsingleton.elim _ hsub _ _))⟩
  ·
    intro c b a hb ha
    let b₀ : B.coch.X 0 := ⟨fun _ => b, continuous_const⟩
    have hz : A.coch.d 1 ((oneCocyclesEquivFunctions A).symm a).1 = 0 := ((oneCocyclesEquivFunctions A).symm a).2
    have key : B.coch.d 0 b₀ = i.hom.f 1 ((oneCocyclesEquivFunctions A).symm a).1 := by
      apply Subtype.ext
      funext v
      show dn B.rho 0 (fun _ => b) v = i.u (a.1 (i.φ (v 0)))
      rw [hadm.i_id]
      show dn B.rho 0 (fun _ => b) v = i.u (a.1 (v 0))
      rw [ha (v 0), dn_zero_apply]
      all_goals rfl
    have hcd : C.coch.d 0 (p.hom.f 0 b₀) = 0 := by
      rw [← p.hom.comm, key]
      exact (hses.exact 1).apply_apply_eq_zero _
    have e₁ : (cohomZeroEquivContinuous C).symm c = C.coch.cls 0 (p.hom.f 0 b₀) hcd := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext hb.symm
    have e₂ : h1EquivOfOrderTwo A (A.coch.cls 1 _ hz) = Submodule.Quotient.mk a := by
      show Submodule.Quotient.mk (oneCocyclesEquivFunctions A ((oneCocyclesEquivFunctions A).symm a)) = _
      rw [LinearEquiv.apply_symm_apply]
    show h1EquivOfOrderTwo A (δ 0 ((cohomZeroEquivContinuous C).symm c)) = _
    rw [e₁, hconn 0 b₀ _ hcd hz key]
    exact e₂
  ·
    intro c b a hbc hpb hia
    let b₁ : B.coch.X 1 := ⟨fun v => b (v 0), hbc.comp (continuous_apply 0)⟩
    have hz : A.coch.d 2 ((twoCocyclesEquivFunctions A).symm a).1 = 0 := ((twoCocyclesEquivFunctions A).symm a).2
    have key : B.coch.d 1 b₁ = i.hom.f 2 ((twoCocyclesEquivFunctions A).symm a).1 := by
      apply Subtype.ext
      funext v
      show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (i.φ (v 0), i.φ (v 1)))
      rw [hadm.i_id]
      show dn B.rho 1 (fun w => b (w 0)) v = i.u (a.1 (v 0, v 1))
      rw [hia (v 0, v 1), dn_one_apply, d1_apply]
      all_goals rfl
    have hcd : C.coch.d 1 (p.hom.f 1 b₁) = 0 := by
      rw [← p.hom.comm, key]
      exact (hses.exact 2).apply_apply_eq_zero _
    have e₁ : (h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c) = C.coch.cls 1 (p.hom.f 1 b₁) hcd := by
      rw [LinearEquiv.symm_apply_eq]
      refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => ?_))
      show c.1 g = p.u (b (p.φ g))
      rw [hadm.p_id]
      exact (hpb g).symm
    have e₂ : h2EquivOfOrderTwo A (A.coch.cls 2 _ hz) = Submodule.Quotient.mk a := by
      show Submodule.Quotient.mk (twoCocyclesEquivFunctions A ((twoCocyclesEquivFunctions A).symm a)) = _
      rw [LinearEquiv.apply_symm_apply]
    show h2EquivOfOrderTwo A (δ 1 ((h1EquivOfOrderTwo C).symm (Submodule.Quotient.mk c))) = _
    rw [e₁, hconn 1 b₁ _ hcd hz key]
    exact e₂

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.TransgressionB
section
namespace ReciprocityTheory.Coh.InflationTransgression

open ReciprocityTheory.Gal ReciprocityTheory.Coh Cx Function InflationRestrictionInvariants

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def ev1 (M : TRep R G) (N : Subgroup G) (f0 : (M.resSub N).coch.X 1) (n : N) : M.V := f0.1 (e1 n)

def conjN (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) : Pair (M.resSub N) (M.resSub N) where
  φ := { toFun := cj N s
         map_one' := Subtype.ext (by simp)
         map_mul' := fun a b => Subtype.ext (by simp only [cj_coe, Subgroup.coe_mul]; group) }
  u := M.rho s
  φ_cont := Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  u_cont := by
    have h := M.cont.comp (Continuous.prodMk (continuous_const (y := s)) (continuous_id (X := M.V)))
    exact h
  equiv g m := by
    have key : ∀ (g : G) (m : M.V), M.rho s (M.rho (s⁻¹ * g * s) m) = M.rho g (M.rho s m) := by
      intro g m
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
    exact key g m

theorem conj_fix_iff (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) (f0 : (M.resSub N).coch.X 1)
    (hf : (M.resSub N).coch.d 1 f0 = 0) :
    (conjN M N s).hom.H 1 ((M.resSub N).coch.cls 1 f0 hf) = (M.resSub N).coch.cls 1 f0 hf ↔
      ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m := by
  rw [Cx.Hom.H_cls, Cx.cls_eq_iff, mem_oneCoboundaries_iff]
  rfl

theorem pair_fix (M : TRep R G) (N : Subgroup G) [N.Normal] (s : G) (c : Pair (M.resSub N) (M.resSub N))
    (hφ : ∀ g, (c.φ g : G) = s⁻¹ * g * s) (hu : ∀ m, c.u m = M.rho s m) (f0 : (M.resSub N).coch.X 1)
    (hf : (M.resSub N).coch.d 1 f0 = 0) (m : M.V)
    (hm : ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m) :
    c.hom.H 1 ((M.resSub N).coch.cls 1 f0 hf) = (M.resSub N).coch.cls 1 f0 hf := by
  rw [Cx.Hom.H_cls, Cx.cls_eq_iff, mem_oneCoboundaries_iff]
  refine ⟨m, fun n => ?_⟩
  have he : (fun i => c.φ (e1 n i)) = e1 (cj N s n) := by
    funext i
    exact Subtype.ext (hφ _)
  show c.u (f0.1 fun i => c.φ (e1 n i)) - f0.1 (e1 n) = _
  rw [he, hu]
  exact hm n

section
variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
  (hP : IsInvRep M N Q P)
include hP

theorem phi_apply (a : G) : P.φ a = (a : G ⧸ N) := by
  rw [hP.1]
  rfl

theorem hom_f_injective (n : ℕ) : Injective (P.hom.f n) := by
  intro f f' h
  apply Subtype.ext
  funext x
  obtain ⟨g, rfl⟩ : ∃ g : Fin n → G, (fun i => (g i : G ⧸ N)) = x :=
    ⟨fun i => (x i).out, funext fun i => QuotientGroup.out_eq' (x i)⟩
  have h1 : P.u (f.1 fun i => P.φ (g i)) = P.u (f'.1 fun i => P.φ (g i)) := congrArg (fun F => F.1 g) h
  have h2 := hP.2.1.injective h1
  simpa [phi_apply M N Q P hP] using h2

theorem inflation_hom_degree_two_apply (z : Q.coch.X 2) (a b : G) :
    (P.hom.f 2 z).1 ![a, b] = P.u (z.1 ![(a : G ⧸ N), b]) := by
  show P.u (z.1 fun i => P.φ (![a, b] i)) = _
  have e : (fun i => P.φ (![a, b] i)) = ![(a : G ⧸ N), (b : G ⧸ N)] := by
    funext i
    fin_cases i <;> simp [phi_apply M N Q P hP]
  rw [e]

theorem inflation_hom_degree_one_apply (v : Q.coch.X 1) (a : G) :
    (P.hom.f 1 v).1 (e1 a) = P.u (v.1 (e1 (a : G ⧸ N))) := by
  show P.u (v.1 fun i => P.φ (e1 a i)) = _
  have e : (fun i => P.φ (e1 a i)) = e1 (a : G ⧸ N) := by
    funext i
    simp [e1, phi_apply M N Q P hP]
  rw [e]

theorem inflD_of_d (y : M.coch.X 1) (z : Q.coch.X 2) (h : M.coch.d 1 y = P.hom.f 2 z) :
    InflD M N (D1 M fun g => y.1 (e1 g)) := by
  have key : ∀ a b, D1 M (fun g => y.1 (e1 g)) a b = P.u (z.1 ![(a : G ⧸ N), b]) := by
    intro a b
    show M.rho a (y.1 (e1 b)) - y.1 (e1 (a * b)) + y.1 (e1 a) = _
    rw [← oneDifferential_val, h, inflation_hom_degree_two_apply M N Q P hP z a b]
  refine ⟨fun a b n => ?_, fun a b n => ?_, fun a b n => ?_⟩
  · rw [key, key, QuotientGroup.mk_mul_of_mem b n.2]
  · rw [key, key, QuotientGroup.mk_mul_of_mem a n.2]
  · rw [key]
    exact (hP.2.2 _).1 ⟨_, rfl⟩ n n.2

theorem descend1 (w : G → M.V) (hw : Continuous w) (hr : ∀ a (n : N), w (a * n) = w a)
    (hi : ∀ a (n : N), M.rho n (w a) = w a) :
    ∃ v : Q.coch.X 1, ∀ a : G, P.u (v.1 (e1 (a : G ⧸ N))) = w a := by
  letI : Setoid G := QuotientGroup.leftRel N
  have hw' : ∀ a b : G, a ≈ b → w a = w b := by
    intro a b hab
    have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.mp hab
    have e := hr a ⟨a⁻¹ * b, hab'⟩
    simp only [mul_inv_cancel_left] at e
    exact e.symm
  let wq : G ⧸ N → M.V := Quotient.lift w hw'
  have hwq : Continuous wq := hw.quotient_lift hw'
  have hmem : ∀ x : G ⧸ N, wq x ∈ LinearMap.range P.u := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H a => exact (hP.2.2 (w a)).2 fun g hg => hi a ⟨g, hg⟩
  let v0 : G ⧸ N → Q.V := fun x => (LinearEquiv.ofInjective P.u hP.2.1.injective).symm ⟨wq x, hmem x⟩
  have hv0u : ∀ x, P.u (v0 x) = wq x := by
    intro x
    have := (LinearEquiv.ofInjective P.u hP.2.1.injective).apply_symm_apply ⟨wq x, hmem x⟩
    exact congrArg Subtype.val this
  have hv0 : Continuous v0 := by
    rw [hP.2.1.continuous_iff]
    have e : (P.u ∘ v0) = wq := funext hv0u
    rw [e]
    exact hwq
  refine ⟨⟨fun g => v0 (g 0), hv0.comp (continuous_apply 0)⟩, fun a => ?_⟩
  exact hv0u _

theorem descend2 (D : G → G → M.V) (hD : Continuous fun p : G × G => D p.1 p.2) (hI : InflD M N D) :
    ∃ z : Q.coch.X 2, ∀ a b : G, P.u (z.1 ![(a : G ⧸ N), b]) = D a b := by
  have hout : ∀ a b : G, D (Quotient.out (a : G ⧸ N)) (Quotient.out (b : G ⧸ N)) = D a b := by
    intro a b
    obtain ⟨h1, e1'⟩ := QuotientGroup.mk_out_eq_mul N a
    obtain ⟨h2, e2'⟩ := QuotientGroup.mk_out_eq_mul N b
    rw [e1', e2', hI.left, hI.right]
  let Dq : (G ⧸ N) × (G ⧸ N) → M.V := fun x => D x.1.out x.2.out
  have hq : Topology.IsQuotientMap (Prod.map (QuotientGroup.mk : G → G ⧸ N) (QuotientGroup.mk : G → G ⧸ N)) :=
    (QuotientGroup.isOpenMap_coe.prodMap QuotientGroup.isOpenMap_coe).isQuotientMap
      (continuous_quot_mk.prodMap continuous_quot_mk)
      (QuotientGroup.mk_surjective.prodMap QuotientGroup.mk_surjective)
  have hDq : Continuous Dq := by
    rw [hq.continuous_iff]
    have e : Dq ∘ Prod.map (QuotientGroup.mk : G → G ⧸ N) (QuotientGroup.mk : G → G ⧸ N) =
        fun p : G × G => D p.1 p.2 := funext fun p => hout p.1 p.2
    rw [e]
    exact hD
  have hmem : ∀ x, Dq x ∈ LinearMap.range P.u := fun x =>
    (hP.2.2 (Dq x)).2 fun g hg => hI.inv _ _ ⟨g, hg⟩
  let z0 : (G ⧸ N) × (G ⧸ N) → Q.V := fun x =>
    (LinearEquiv.ofInjective P.u hP.2.1.injective).symm ⟨Dq x, hmem x⟩
  have hz0u : ∀ x, P.u (z0 x) = Dq x := by
    intro x
    have := (LinearEquiv.ofInjective P.u hP.2.1.injective).apply_symm_apply ⟨Dq x, hmem x⟩
    exact congrArg Subtype.val this
  have hz0 : Continuous z0 := by
    rw [hP.2.1.continuous_iff]
    have e : (P.u ∘ z0) = Dq := funext hz0u
    rw [e]
    exact hDq
  refine ⟨⟨fun g => z0 (g 0, g 1), hz0.comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩, fun a b => ?_⟩
  show P.u (z0 ((a : G ⧸ N), (b : G ⧸ N))) = D a b
  rw [hz0u]
  exact hout a b

theorem exists_lift [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [DiscreteTopology M.V]
    (hNc : IsClosed (N : Set G)) (f0 : (M.resSub N).coch.X 1) (hf : (M.resSub N).coch.d 1 f0 = 0)
    (hinv : ∀ s : G, ∃ m : M.V, ∀ n : N, M.rho s (ev1 M N f0 (cj N s n)) - ev1 M N f0 n = M.rho n m - m) :
    ∃ (y : M.coch.X 1) (z : Q.coch.X 2) (_ : Q.coch.d 2 z = 0), M.coch.d 1 y = P.hom.f 2 z ∧
      (Pair.res M N.subtype continuous_subtype_val).hom.f 1 y = f0 := by
  have hfc := (wach_d1_eq_zero_iff (M.resSub N) f0).1 hf
  obtain ⟨y0, hy0c, hy0N, h2, h3⟩ := exists_ext_cochain M N hNc (ev1 M N f0)
    ((show Continuous f0.1 from f0.2).comp (continuous_pi fun _ => continuous_id)) (fun a b => hfc a b) hinv
  have hDc : Continuous fun p : G × G => D1 M y0 p.1 p.2 :=
    ((M.cont.comp (continuous_fst.prodMk (hy0c.comp continuous_snd))).sub
      (hy0c.comp (continuous_fst.mul continuous_snd))).add (hy0c.comp continuous_fst)
  obtain ⟨z, hz⟩ := descend2 M N Q P hP (D1 M y0) hDc (inflD_of_ext M N _ y0 h2 h3)
  let y : M.coch.X 1 := ⟨fun g => y0 (g 0), hy0c.comp (continuous_apply 0)⟩
  have hd : M.coch.d 1 y = P.hom.f 2 z := Subtype.ext (funext fun g => by
    have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
    rw [hg, oneDifferential_val, inflation_hom_degree_two_apply M N Q P hP, hz]; rfl)
  have hzc : Q.coch.d 2 z = 0 := hom_f_injective M N Q P hP 3 (by
    rw [map_zero, P.hom.comm, ← hd]; exact M.coch.dd 1 y)
  refine ⟨y, z, hzc, hd, Subtype.ext (funext fun g => ?_)⟩
  show y0 (g 0 : G) = f0.1 g
  rw [hy0N]
  exact (oneCochain_apply_fin_one _ f0 g).symm

theorem cls_unique (y y' : M.coch.X 1) (z z' : Q.coch.X 2) (hz : Q.coch.d 2 z = 0)
    (hz' : Q.coch.d 2 z' = 0) (hd : M.coch.d 1 y = P.hom.f 2 z) (hd' : M.coch.d 1 y' = P.hom.f 2 z')
    (hr : (Pair.res M N.subtype continuous_subtype_val).hom.f 1 (y - y') ∈ (M.resSub N).coch.B 1) :
    Q.coch.cls 2 z hz = Q.coch.cls 2 z' hz' := by
  obtain ⟨m, hm⟩ : ∃ m : M.V, ∀ n : N, y.1 (e1 (n : G)) - y'.1 (e1 (n : G)) = M.rho n m - m :=
    (mem_oneCoboundaries_iff _ _).1 hr
  obtain ⟨w, hw⟩ : ∃ w : M.coch.X 1, w = y - y' - M.coch.d 0 (const0 M m) := ⟨_, rfl⟩
  have hwv : ∀ a, w.1 (e1 a) = y.1 (e1 a) - y'.1 (e1 a) - (M.rho a m - m) := fun a => by
    rw [hw]
    show y.1 (e1 a) - y'.1 (e1 a) - (M.coch.d 0 (const0 M m)).1 (e1 a) = _
    rw [zeroDifferential_val]; rfl
  have hwN : ∀ n : N, w.1 (e1 n) = 0 := fun n => by
    rw [hwv, hm n, sub_self]
  have hdw : M.coch.d 1 w = P.hom.f 2 (z - z') := by
    rw [hw, map_sub, map_sub, M.coch.dd, sub_zero, hd, hd', map_sub]
  have hI := inflD_of_d M N Q P hP w (z - z') hdw
  have h1 : (fun g => w.1 (e1 g)) 1 = 0 := by
    have e := hwN 1
    rwa [OneMemClass.coe_one] at e
  obtain ⟨hr1, hr2⟩ := inflD_of_zero M N (fun g => w.1 (e1 g)) h1 hI hwN
  obtain ⟨v, hv⟩ := descend1 M N Q P hP (fun g => w.1 (e1 g))
    ((show Continuous w.1 from w.2).comp (continuous_pi fun _ => continuous_id)) hr1 hr2
  have hvw : P.hom.f 1 v = w := Subtype.ext (funext fun g => by
    rw [oneCochain_apply_fin_one M _ g, oneCochain_apply_fin_one M w g, inflation_hom_degree_one_apply M N Q P hP, hv])
  have hdv : Q.coch.d 1 v = z - z' := hom_f_injective M N Q P hP 2 (by rw [P.hom.comm, hvw, hdw])
  rw [cls_eq_iff]
  exact ⟨v, hdv⟩

end

end

end ReciprocityTheory.Coh.InflationTransgression
end

