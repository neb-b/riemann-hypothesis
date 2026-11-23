module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BorderedMatrixInvariantSpaceExistsCompactOpenSub
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.InverseCompactOpen

theorem inv_exists_compact_open (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F)
    (hU : IsOpen U) (ha : a₀ ∈ U) :
    ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := by
  have hUn : Unram F E := inferInstance
  haveI : LocallyCompactSpace F := hUn.lcF
  haveI : IsUltrametricDist F := hUn.ultraF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU a₀ ha
  have hε2 : 0 < ε / 2 := half_pos hε
  refine ⟨Metric.closedBall a₀ (ε / 2), isCompact_closedBall _ _, ?_,
    Metric.mem_closedBall_self hε2.le, ?_⟩
  · have hpi : ∀ x : Fin r → F, IsOpen (Metric.closedBall x (ε / 2)) := by
      intro x
      rw [closedBall_pi x hε2.le]
      exact isOpen_set_pi Set.finite_univ
        (fun i _ => IsUltrametricDist.isOpen_closedBall (x i) hε2.ne')
    obtain ⟨p, q, l⟩ := a₀
    rw [← closedBall_prod_same, ← closedBall_prod_same]
    exact (hpi p).prod ((hpi q).prod (IsUltrametricDist.isOpen_closedBall l hε2.ne'))
  · exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball

end GlobalTheory.InverseCompactOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerNesbittExistsEquivOfCharpolyEqBindersStatement
section
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.brauerNesbitt_exists_equiv_of_charpoly_eq' : ∀ {k Γ V W : Type} [Field k] [Monoid Γ] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k Γ V) (σ : Representation k Γ W), ρ.IsSemisimpleRepresentation → σ.IsSemisimpleRepresentation → (∀ a : MonoidAlgebra k Γ, LinearMap.charpoly (ρ.asAlgebraHom a) = LinearMap.charpoly (σ.asAlgebraHom a)) → ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  first | exact @GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' | exact GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' | (intros; apply GlobalTheory.CharpolyIso.exists_equiv_of_charpoly_eq' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCommMapsEqCardHomQuot
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

noncomputable section

namespace GlobalTheory.StableLatCount

theorem card_commMaps_eq_card_homQuot : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → Nat.card {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁, φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} = Nat.card {z : (A₂ →ₗ[E] A₁) ⧸ homLat E M₁ M₂ // ∀ ψ : A₂ →ₗ[E] A₁, Submodule.Quotient.mk ψ = z → adE E g₁ g₂ ψ ∈ homLat E M₁ M₂} := by
  intro O _ _ _ E _ _ _ A₁ A₂ _ _ _ _ _ _ _ _ _ _ g₁ g₂ M₁ M₂ hM₂ hg₁ hg₂
  classical
  let F : (A₂ →ₗ[E] A₁) →ₗ[O] (M₂ →ₗ[O] A₁ ⧸ M₁) :=
    { toFun := fun ψ => M₁.mkQ ∘ₗ (ψ.restrictScalars O) ∘ₗ M₂.subtype
      map_add' := fun ψ χ => by ext x; simp
      map_smul' := fun c ψ => by ext x; simp }
  have hF : ∀ ψ (x : M₂), F ψ x = Submodule.Quotient.mk (ψ (x : A₂)) := fun _ _ => rfl
  have hsurj : Function.Surjective F := by
    intro φ
    haveI : Module.Finite O M₂ := Module.Finite.iff_fg.2 hM₂.1
    haveI : Module.IsTorsionFree O A₂ := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      right
      rw [← algebraMap_smul E r m] at h
      have hr' : algebraMap O E r ≠ 0 := by
        intro h0
        exact hr ((IsFractionRing.injective O E) (by rw [h0, map_zero]))
      exact (smul_eq_zero.1 h).resolve_left hr'
    haveI : Module.Free O M₂ := Module.free_of_finite_type_torsion_free'
    let b := Module.Free.chooseBasis O M₂
    let bs : Module.Free.ChooseBasisIndex O M₂ → A₂ := fun i => (b i : A₂)
    have hli : LinearIndependent O bs := b.linearIndependent.map' M₂.subtype (Submodule.ker_subtype M₂)
    have hliE : LinearIndependent E bs := (LinearIndependent.iff_fractionRing O E).1 hli
    have hspan : ⊤ ≤ Submodule.span E (Set.range bs) := by
      rw [← hM₂.2, Submodule.span_le]
      intro x hx
      have h1 : (⟨x, hx⟩ : M₂) ∈ Submodule.span O (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      have h2 := Submodule.mem_map_of_mem (f := M₂.subtype) h1
      rw [Submodule.map_span, ← Set.range_comp] at h2
      exact Submodule.span_le_restrictScalars O E _ h2
    let bE := Module.Basis.mk hliE hspan
    let lift : Module.Free.ChooseBasisIndex O M₂ → A₁ := fun i =>
      Classical.choose (Submodule.Quotient.mk_surjective M₁ (φ (b i)))
    have hlift : ∀ i, Submodule.Quotient.mk (p := M₁) (lift i) = φ (b i) := fun i =>
      Classical.choose_spec (Submodule.Quotient.mk_surjective M₁ (φ (b i)))
    refine ⟨bE.constr E lift, b.ext fun i => ?_⟩
    rw [hF, ← hlift i]
    congr 1
    have : ((b i : M₂) : A₂) = bE i := by simp [bE, bs]
    rw [this, Module.Basis.constr_basis]
  have hker : LinearMap.ker F = homLat E M₁ M₂ := by
    ext ψ
    rw [LinearMap.mem_ker]
    constructor
    · intro h x hx
      have := congrArg (fun f => f ⟨x, hx⟩) h
      simp only [hF, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    · intro h
      ext x
      rw [hF, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact h x x.2
  let e : ((A₂ →ₗ[E] A₁) ⧸ homLat E M₁ M₂) ≃ (M₂ →ₗ[O] A₁ ⧸ M₁) :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective hsurj)).toEquiv
  have he : ∀ ψ, e (Submodule.Quotient.mk ψ) = F ψ := fun ψ => rfl
  refine (Nat.card_congr (e.subtypeEquiv fun z => ?_)).symm
  induction z using Submodule.Quotient.induction_on with
  | H ψ₀ => ?_
  rw [he]
  constructor
  · intro h x y hxy a ha
    have hA : ∀ x ∈ M₂, g₁ * ψ₀ x - ψ₀ (g₂ * x) ∈ M₁ := fun x hx => by
      have := h ψ₀ rfl x hx
      rwa [adE_apply] at this
    rw [hF] at ha ⊢
    rw [Submodule.Quotient.eq] at ha ⊢
    have := M₁.add_mem (M₁.neg_mem (hA x x.2)) (hg₁ _ ha)
    convert this using 1
    rw [hxy]
    ring
  · intro h ψ hψ x hx
    rw [Submodule.Quotient.eq] at hψ
    have hd : ∀ x ∈ M₂, ψ x - ψ₀ x ∈ M₁ := fun x hx => by
      have := hψ x hx
      rwa [LinearMap.sub_apply] at this
    have hc := h ⟨x, hx⟩ ⟨g₂ * x, hg₂ x hx⟩ rfl (ψ₀ x) (hF ψ₀ ⟨x, hx⟩)
    rw [hF, Submodule.Quotient.eq] at hc
    rw [adE_apply]
    have := M₁.sub_mem (M₁.sub_mem (hg₁ _ (hd x hx)) (hd _ (hg₂ x hx))) hc
    convert this using 1
    simp only
    ring

end GlobalTheory.StableLatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardKerMulCardEq
section
namespace GlobalTheory.ZModDual

theorem card_quot_ker_le (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A] [Module (ZMod n) A]
    [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (A ⧸ LinearMap.ker b) ≤ Nat.card (B ⧸ LinearMap.ker b.flip) := by
  set K' := LinearMap.ker b.flip
  have : Finite (B ⧸ K') := Finite.of_surjective K'.mkQ K'.mkQ_surjective
  have : Finite (Module.Dual (ZMod n) B) :=
    Finite.of_injective (fun f : Module.Dual (ZMod n) B => (f : B → ZMod n)) DFunLike.coe_injective
  have hle : LinearMap.range b ≤ K'.dualAnnihilator := by
    rintro _ ⟨a, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    have := LinearMap.congr_fun (LinearMap.mem_ker.1 hy) a
    simpa using this
  calc Nat.card (A ⧸ LinearMap.ker b) = Nat.card (LinearMap.range b) :=
        Nat.card_congr (LinearMap.quotKerEquivRange b).toEquiv
    _ ≤ Nat.card K'.dualAnnihilator :=
        Nat.card_le_card_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
    _ = Nat.card (Module.Dual (ZMod n) (B ⧸ K')) :=
        Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator K').toEquiv.symm
    _ = Nat.card (B ⧸ K') := card_dual_eq n (B ⧸ K')

theorem card_ker_mul_card_eq (n : ℕ) [NeZero n] (A B : Type) [AddCommGroup A]
    [Module (ZMod n) A] [Finite A] [AddCommGroup B] [Module (ZMod n) B] [Finite B]
    (b : A →ₗ[ZMod n] B →ₗ[ZMod n] ZMod n) :
    Nat.card (LinearMap.ker b) * Nat.card B = Nat.card (LinearMap.ker b.flip) * Nat.card A := by
  have h1 := card_quot_ker_le n A B b
  have h2 := card_quot_ker_le n B A b.flip
  rw [LinearMap.flip_flip] at h2
  have heq : Nat.card (A ⧸ LinearMap.ker b) = Nat.card (B ⧸ LinearMap.ker b.flip) := le_antisymm h1 h2
  have eA := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b)
  have eB := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker b.flip)
  rw [eA, eB, heq]
  ring

end GlobalTheory.ZModDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardKernelQuotOfBijective
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory

theorem card_kernel_quot_of_bijective (O : Type) [CommRing O] (P : Type) [AddCommGroup P]
    [Module O P] (N : Submodule O P) (T : P →ₗ[O] P) (hT : Function.Bijective T)
    (hN : ∀ x ∈ N, T x ∈ N) :
    Nat.card {z : P ⧸ N // ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N} =
      Nat.card (↥N ⧸ (N.map T).comap N.subtype) := by
  let e : P ≃ₗ[O] P := LinearEquiv.ofBijective T hT
  have he1 : ∀ y, T (e.symm y) = y := fun y => e.apply_symm_apply y
  have he2 : ∀ x, e.symm (T x) = x := fun x => e.symm_apply_apply x
  let g : N →ₗ[O] P ⧸ N := N.mkQ ∘ₗ (e.symm : P →ₗ[O] P) ∘ₗ N.subtype
  have hg : ∀ y : N, g y = Submodule.Quotient.mk (e.symm (y : P)) := fun y => rfl
  have hker : LinearMap.ker g = (N.map T).comap N.subtype := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker, hg, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.mem_map]
    constructor
    · intro h
      exact ⟨e.symm y, h, he1 y⟩
    · rintro ⟨x, hx, hxy⟩
      simp only at hxy
      subst hxy
      show e.symm (T x) ∈ N
      rw [he2]
      exact hx
  have hrange : ∀ z : P ⧸ N,
      z ∈ LinearMap.range g ↔ ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N := by
    intro z
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩ x hx
      rw [hg] at hx
      have h1 : x - e.symm y ∈ N := (Submodule.Quotient.eq N).mp hx
      have h2 : T (x - e.symm y) ∈ N := hN _ h1
      rw [map_sub, he1] at h2
      simpa using N.add_mem h2 hy
    · intro h
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
      refine ⟨⟨T x, h x rfl⟩, ?_⟩
      rw [hg]
      simp only
      rw [he2]
  calc Nat.card {z : P ⧸ N // ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N}
      = Nat.card (LinearMap.range g) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun z => (hrange z).symm))
    _ = Nat.card (↥N ⧸ LinearMap.ker g) := Nat.card_congr g.quotKerEquivRange.toEquiv.symm
    _ = Nat.card (↥N ⧸ (N.map T).comap N.subtype) :=
        Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallBoundsUltrametric
section
open Polynomial
open Classical

namespace GlobalTheory

theorem card_roots_le_radius_bounds :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ),
      0 < ρ → f.coeff d ≠ 0 →
      ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) →
          d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧
      ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) →
          Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by
  intro K _ _ _ f ρ d hρ hd
  have hf : f ≠ 0 := by
    rintro rfl
    exact hd (by simp)
  obtain ⟨hA, hB⟩ := _root_.GlobalTheory.card_roots_closedBall_eq_dominantIndex K f ρ hρ hf
  set e := Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) with he
  refine ⟨fun H => ?_, fun H => ?_⟩
  · by_contra hlt
    push_neg at hlt
    have h1 := hB d hlt
    have h2 := H e
    linarith
  · by_contra hlt
    push_neg at hlt
    have h1 := H e hlt
    have h2 := hA d
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardStableEqCardHom
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory.StableGraph

variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁]
  [Algebra O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}

theorem mem_of_inl {M : Submodule O (A₁ × A₂)} (h : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    {a : A₁} (ha : (a, (0 : A₂)) ∈ M) : a ∈ M₁ := by
  rw [← h]; exact ha

theorem mem_of_snd {M : Submodule O (A₁ × A₂)} (h : M.map (LinearMap.snd O A₁ A₂) = M₂)
    {a : A₁} {x : A₂} (hx : (a, x) ∈ M) : x ∈ M₂ := by
  rw [← h]; exact Submodule.mem_map_of_mem (f := LinearMap.snd O A₁ A₂) hx

theorem exists_of_map {M : Submodule O (A₁ × A₂)} (h : M.map (LinearMap.snd O A₁ A₂) = M₂)
    (x : M₂) : ∃ a : A₁, (a, (x : A₂)) ∈ M := by
  have hx : (x : A₂) ∈ M.map (LinearMap.snd O A₁ A₂) := h ▸ x.2
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.1 hx
  have hp' : p = (p.1, (x : A₂)) := Prod.ext rfl hpx
  exact ⟨p.1, hp' ▸ hp⟩

noncomputable def classOf {M : Submodule O (A₁ × A₂)} (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂)
    (x : M₂) : A₁ ⧸ M₁ :=
  Submodule.Quotient.mk (exists_of_map h₂ x).choose

theorem classOf_eq {M : Submodule O (A₁ × A₂)} (h₁ : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂) {x : M₂} {a : A₁} (hp : (a, (x : A₂)) ∈ M) :
    classOf (M₁ := M₁) h₂ x = Submodule.Quotient.mk a := by
  unfold classOf
  rw [Submodule.Quotient.eq]
  apply mem_of_inl h₁
  have := M.sub_mem (exists_of_map h₂ x).choose_spec hp
  simpa using this

noncomputable def toHom (M : Submodule O (A₁ × A₂)) (h₁ : M.comap (LinearMap.inl O A₁ A₂) = M₁)
    (h₂ : M.map (LinearMap.snd O A₁ A₂) = M₂) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun := classOf h₂
  map_add' x y := by
    obtain ⟨a, ha⟩ := exists_of_map h₂ x
    obtain ⟨b, hb⟩ := exists_of_map h₂ y
    rw [classOf_eq h₁ h₂ ha, classOf_eq h₁ h₂ hb, ← Submodule.Quotient.mk_add]
    exact classOf_eq h₁ h₂ (by simpa using M.add_mem ha hb)
  map_smul' c x := by
    obtain ⟨a, ha⟩ := exists_of_map h₂ x
    rw [classOf_eq h₁ h₂ ha, RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    exact classOf_eq h₁ h₂ (by simpa using M.smul_mem c ha)

def graph (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : Submodule O (A₁ × A₂) where
  carrier := {p | ∃ h : p.2 ∈ M₂, Submodule.Quotient.mk p.1 = φ ⟨p.2, h⟩}
  add_mem' := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨hx, ha⟩ ⟨hy, hb⟩
    refine ⟨M₂.add_mem hx hy, ?_⟩
    have e : (⟨x + y, M₂.add_mem hx hy⟩ : M₂) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    simp only [Prod.fst_add, Prod.snd_add] at *
    rw [e, map_add (f := _), Submodule.Quotient.mk_add, ha, hb]
  zero_mem' := ⟨M₂.zero_mem, by
    have e : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
    simp only [Prod.fst_zero, Prod.snd_zero]
    rw [e, map_zero, Submodule.Quotient.mk_zero]⟩
  smul_mem' := by
    rintro c ⟨a, x⟩ ⟨hx, ha⟩
    refine ⟨M₂.smul_mem c hx, ?_⟩
    have e : (⟨c • x, M₂.smul_mem c hx⟩ : M₂) = c • ⟨x, hx⟩ := rfl
    simp only [Prod.smul_fst, Prod.smul_snd] at *
    rw [e, map_smul, Submodule.Quotient.mk_smul, ha]

theorem mem_graph {φ : M₂ →ₗ[O] A₁ ⧸ M₁} {a : A₁} {x : A₂} :
    (a, x) ∈ graph φ ↔ ∃ h : x ∈ M₂, Submodule.Quotient.mk a = φ ⟨x, h⟩ := Iff.rfl

theorem graph_comap (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : (graph φ).comap (LinearMap.inl O A₁ A₂) = M₁ := by
    ext a
    simp only [Submodule.mem_comap, LinearMap.inl_apply]
    rw [mem_graph]
    constructor
    · rintro ⟨h, e⟩
      have e0 : (⟨0, h⟩ : M₂) = 0 := rfl
      rw [e0, map_zero, Submodule.Quotient.mk_eq_zero] at e
      exact e
    · intro ha
      refine ⟨M₂.zero_mem, ?_⟩
      have e0 : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
      rw [e0, map_zero, Submodule.Quotient.mk_eq_zero]
      exact ha

theorem graph_map (φ : M₂ →ₗ[O] A₁ ⧸ M₁) : (graph φ).map (LinearMap.snd O A₁ A₂) = M₂ := by
    ext x
    constructor
    · rintro ⟨p, ⟨h, _⟩, rfl⟩
      exact h
    · intro hx
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective M₁ (φ ⟨x, hx⟩)
      exact ⟨(a, x), ⟨hx, ha⟩, rfl⟩

noncomputable def stableEquiv (g₁ : A₁) (g₂ : A₂) (hM₂ : ∀ y ∈ M₂, g₂ * y ∈ M₂) :
    {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧
        M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} ≃
      {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁,
        φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} where
  toFun M := ⟨toHom M.1 M.2.2.1 M.2.2.2, by
    obtain ⟨M, hst, h₁, h₂⟩ := M
    intro x y hy a ha
    obtain ⟨c, hc⟩ := exists_of_map h₂ x
    have hφx : toHom M h₁ h₂ x = Submodule.Quotient.mk c := classOf_eq h₁ h₂ hc
    rw [hφx, Submodule.Quotient.eq] at ha
    have h1 : (c - a, (0 : A₂)) ∈ M := by rw [← h₁] at ha; exact ha
    have h2 := hst _ hc
    have h3 := hst _ h1
    have h4 : (g₁ * a, (y : A₂)) ∈ M := by
      have := M.sub_mem h2 h3
      rw [hy]
      convert this using 1
      ext
      · simp only [Prod.fst_sub, Prod.fst_mul]; ring
      · simp
    exact classOf_eq h₁ h₂ h4⟩
  invFun φ := ⟨graph φ.1, by
    rintro ⟨a, x⟩ ⟨hx, ha⟩
    exact ⟨hM₂ x hx, (φ.2 ⟨x, hx⟩ ⟨g₂ * x, hM₂ x hx⟩ rfl a ha.symm).symm⟩,
    graph_comap φ.1, graph_map φ.1⟩
  left_inv M := by
    obtain ⟨M, hst, h₁, h₂⟩ := M
    apply Subtype.ext
    ext ⟨a, x⟩
    show (a, x) ∈ graph (toHom M h₁ h₂) ↔ (a, x) ∈ M
    rw [mem_graph]
    constructor
    · rintro ⟨hx, e⟩
      obtain ⟨c, hc⟩ := exists_of_map h₂ ⟨x, hx⟩
      have hφx : toHom M h₁ h₂ ⟨x, hx⟩ = Submodule.Quotient.mk c := classOf_eq h₁ h₂ hc
      rw [hφx, Submodule.Quotient.eq] at e
      have h1 : (a - c, (0 : A₂)) ∈ M := by rw [← h₁] at e; exact e
      have := M.add_mem h1 hc
      simpa using this
    · intro hm
      exact ⟨mem_of_snd h₂ hm, (classOf_eq h₁ h₂ hm).symm⟩
  right_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective M₁ (φ.1 x)
    have hm : (a, (x : A₂)) ∈ graph φ.1 := ⟨x.2, ha⟩
    exact (classOf_eq (graph_comap φ.1) (graph_map φ.1) hm).trans ha

end GlobalTheory.StableGraph


open GlobalTheory.StableGraph in
theorem GlobalTheory.StableGraph.card_stable_eq_card_hom : ∀ (O : Type) [CommRing O] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] (g₁ : A₁) (g₂ : A₂) (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), (∀ y ∈ M₂, g₂ * y ∈ M₂) → Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} = Nat.card {φ : M₂ →ₗ[O] A₁ ⧸ M₁ // ∀ x y : M₂, (y : A₂) = g₂ * x → ∀ a : A₁, φ x = Submodule.Quotient.mk a → φ y = Submodule.Quotient.mk (g₁ * a)} := by
  intro O _ A₁ A₂ _ _ _ _ g₁ g₂ M₁ M₂ hM₂
  exact Nat.card_congr (stableEquiv g₁ g₂ hM₂)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClearDenominators
section
namespace GlobalTheory.ClearDenominatorsIntegral

open GlobalTheory.UnitLemma

theorem clear_denominators (K : UQ) {V : Type} [AddCommGroup V] [Module (UQ.E K) V] [Module (UQ.O K) V]
    [IsScalarTower (UQ.O K) (UQ.E K) V] (M : Submodule (UQ.O K) V) {x : V}
    (hx : x ∈ Submodule.span (UQ.E K) (↑M : Set V)) :
    ∃ (d : UQ.O K), d ≠ (0 : UQ.O K) ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul e y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (UQ.O K)) e
    have hb : (b : UQ.O K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : UQ.O K) * d, mul_ne_zero hb hd, ?_⟩
    have key : (b : UQ.O K) • (e • y) = a • y := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm, hab, algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_smul, mul_comm, ← smul_smul]
    exact M.smul_mem _ h

theorem main : ∀ (K : GlobalTheory.UnitLemma.UQ) {V : Type} [inst : AddCommGroup V] [inst_1 : Module (GlobalTheory.UnitLemma.UQ.E K) V] [inst_2 : Module (GlobalTheory.UnitLemma.UQ.O K) V] [IsScalarTower (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) V] (M : Submodule (GlobalTheory.UnitLemma.UQ.O K) V) {x : V}, x ∈ Submodule.span (GlobalTheory.UnitLemma.UQ.E K) (↑M : Set V) → ∃ (d : GlobalTheory.UnitLemma.UQ.O K), d ≠ (0 : GlobalTheory.UnitLemma.UQ.O K) ∧ d • x ∈ M :=
  fun K _ _ _ _ _ M _ hx => clear_denominators K M hx

end GlobalTheory.ClearDenominatorsIntegral
end

