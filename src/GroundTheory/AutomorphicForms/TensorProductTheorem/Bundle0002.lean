module

public import Mathlib
public import GroundTheory.AutomorphicForms.TensorProductTheorem.GenWindow
public import GroundTheory.AutomorphicForms.SmoothRep
public import GroundTheory.AutomorphicForms.TensorProductTheorem.Bundle0001

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.TensorProductTheorem.OuterTensor
section
noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module Set TensorProduct

open scoped TensorProduct

variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂]

theorem nontrivial_of_irreducible {ρ : Representation ℂ M₁ V₁} (h : ρ.IsIrreducible) :
    Nontrivial V₁ := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  obtain ⟨a, b, hab⟩ := h.toNontrivial.exists_pair_ne
  apply hab
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => b.toSubmodule.zero_mem, fun _ => a.toSubmodule.zero_mem⟩

def outerTensor (ρ₁ : Representation ℂ M₁ V₁) (ρ₂ : Representation ℂ M₂ V₂) :
    Representation ℂ (M₁ × M₂) (V₁ ⊗[ℂ] V₂) where
  toFun p := TensorProduct.map (ρ₁ p.1) (ρ₂ p.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, map_one]
    exact TensorProduct.map_one
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    exact TensorProduct.map_mul _ _ _ _

theorem outerTensor_tmul (ρ₁ : Representation ℂ M₁ V₁) (ρ₂ : Representation ℂ M₂ V₂)
    (p : M₁ × M₂) (a : V₁) (b : V₂) :
    outerTensor ρ₁ ρ₂ p (a ⊗ₜ b) = ρ₁ p.1 a ⊗ₜ ρ₂ p.2 b :=
  TensorProduct.map_tmul _ _ _ _

theorem exists_asAlgebraHom_eq {ρ₂ : Representation ℂ M₂ V₂} (hirr : ρ₂.IsIrreducible)
    (hschur : ∀ T : End ℂ V₂, (∀ m, T * ρ₂ m = ρ₂ m * T) → ∃ c : ℂ, T = c • 1)
    (A : End ℂ V₂) (s : Finset V₂) :
    ∃ r : MonoidAlgebra ℂ M₂, ∀ v ∈ s, ρ₂.asAlgebraHom r v = A v := by
  classical
  set R := MonoidAlgebra ℂ M₂
  have hsimple : IsSimpleModule R ρ₂.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ₂).1 hirr
  set E := ρ₂.asModuleEquiv

  have hsc : ∀ φ : Module.End R ρ₂.asModule, ∃ c : ℂ, ∀ x, E (φ x) = c • E x := by
    intro φ
    let T : End ℂ V₂ :=
      { toFun := fun v => E (φ (E.symm v))
        map_add' := fun a b => by simp
        map_smul' := fun c v => by
          rw [RingHom.id_apply, Representation.asModuleEquiv_symm_map_smul, map_smul,
            Representation.asModuleEquiv_map_smul, AlgHom.commutes,
            Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply] }
    obtain ⟨c, hc⟩ := hschur T fun m => by
      ext v
      simp only [Module.End.mul_apply, T, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Representation.asModuleEquiv_symm_map_rho, map_smul,
        Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply,
        Representation.asAlgebraHom_single_one]
    refine ⟨c, fun x => ?_⟩
    have := congrArg (fun F : End ℂ V₂ => F (E x)) hc
    simpa [T] using this
  let f : Module.End (Module.End R ρ₂.asModule) ρ₂.asModule :=
    { toFun := fun x => E.symm (A (E x))
      map_add' := fun a b => by simp
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := hsc φ
        show E.symm (A (E (φ x))) = φ (E.symm (A (E x)))
        apply E.injective
        rw [hc, hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f (s.image E.symm)
  refine ⟨r, fun v hv => ?_⟩
  have := hr (E.symm v) (Finset.mem_image_of_mem _ hv)
  have h2 := congrArg E this
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] at h2
  rw [h2, Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]

theorem isIrreducible_outerTensor {ρ₁ : Representation ℂ M₁ V₁} {ρ₂ : Representation ℂ M₂ V₂}
    (hirr₁ : ρ₁.IsIrreducible) (hirr₂ : ρ₂.IsIrreducible)
    (hschur : ∀ T : End ℂ V₂, (∀ m, T * ρ₂ m = ρ₂ m * T) → ∃ c : ℂ, T = c • 1) :
    (outerTensor ρ₁ ρ₂).IsIrreducible := by
  classical
  haveI := hirr₁
  haveI := hirr₂
  set ρ := outerTensor ρ₁ ρ₂
  have hnt₁ := nontrivial_of_irreducible hirr₁
  have hnt₂ := nontrivial_of_irreducible hirr₂
  let b := Basis.ofVectorSpace ℂ V₂
  set F := TensorProduct.equivFinsuppOfBasisRight (M := V₁) b

  have key : ∀ Y : Subrepresentation ρ, Y ≠ ⊥ → ∀ a b', a ⊗ₜ[ℂ] b' ∈ Y.toSubmodule := by
    intro Y hY
    have hY' : Y.toSubmodule ≠ ⊥ := fun h => hY (Subrepresentation.toSubmodule_injective h)
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY'
    have hfy : F y ≠ 0 := fun h => hy0 (F.injective (h.trans (map_zero F).symm))
    obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.1 hfy
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hj₀

    let A : End ℂ V₂ := b.constr ℂ fun j => if j = j₀ then b j₀ else 0
    obtain ⟨r, hr⟩ := exists_asAlgebraHom_eq hirr₂ hschur A ((F y).support.image b)
    have hstab : ∀ r' : MonoidAlgebra ℂ M₂, ∀ z ∈ Y.toSubmodule,
        TensorProduct.map LinearMap.id (ρ₂.asAlgebraHom r') z ∈ Y.toSubmodule := by
      intro r' z hz
      induction r' using MonoidAlgebra.induction_on with
      | of m =>
        have := Y.apply_mem_toSubmodule (1, m) hz
        rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]
        have h1 : ρ (1, m) = TensorProduct.map LinearMap.id (ρ₂ m) := by
          show TensorProduct.map (ρ₁ 1) (ρ₂ m) = _
          rw [map_one]
          rfl
        rw [← h1]
        exact this
      | add f g hf hg =>
        rw [map_add (f := _), TensorProduct.map_add_right, LinearMap.add_apply]
        exact Y.toSubmodule.add_mem hf hg
      | smul c f hf =>
        rw [map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply]
        exact Y.toSubmodule.smul_mem c hf
    have hy' : y = (F y).sum fun j a => a ⊗ₜ[ℂ] b j := by
      conv_lhs => rw [← F.symm_apply_apply y]
      exact TensorProduct.equivFinsuppOfBasisRight_symm_apply b (F y)
    have hpure : F y j₀ ⊗ₜ[ℂ] b j₀ ∈ Y.toSubmodule := by
      have := hstab r y hy
      rw [hy', map_finsuppSum] at this
      convert this using 1
      rw [Finsupp.sum, Finset.sum_eq_single j₀]
      · rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _
          (Finsupp.mem_support_iff.2 hj₀))]
        simp [A]
      · intro j hj hjj
        rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _ hj)]
        simp [A, hjj]
      · intro h
        exact absurd (Finsupp.mem_support_iff.2 hj₀) h

    intro a b'
    have h1 : ∀ a' ∈ Submodule.span ℂ (range fun m => ρ₁ m (F y j₀)),
        a' ⊗ₜ[ℂ] b j₀ ∈ Y.toSubmodule := by
      intro a' ha'
      induction ha' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        have := Y.apply_mem_toSubmodule (m, 1) hpure
        simpa [ρ, outerTensor_tmul] using this
      | zero => simp
      | add x z _ _ hx hz => rw [TensorProduct.add_tmul]; exact Y.toSubmodule.add_mem hx hz
      | smul c x _ hx => rw [← TensorProduct.smul_tmul']; exact Y.toSubmodule.smul_mem c hx
    have ha := h1 a (mem_span_mOrbit (ρ := ρ₁) hj₀ a)
    have h2 : ∀ b'' ∈ Submodule.span ℂ (range fun m => ρ₂ m (b j₀)),
        a ⊗ₜ[ℂ] b'' ∈ Y.toSubmodule := by
      intro b'' hb''
      induction hb'' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        have := Y.apply_mem_toSubmodule (1, m) ha
        simpa [ρ, outerTensor_tmul] using this
      | zero => simp
      | add x z _ _ hx hz => rw [TensorProduct.tmul_add]; exact Y.toSubmodule.add_mem hx hz
      | smul c x _ hx => rw [TensorProduct.tmul_smul]; exact Y.toSubmodule.smul_mem c hx
    exact h2 b' (mem_span_mOrbit (ρ := ρ₂) (b.ne_zero j₀) b')
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨a, ha⟩ := exists_ne (0 : V₁)
    obtain ⟨v₂, hv₂⟩ := exists_ne (0 : V₂)
    obtain ⟨j, hj⟩ : ∃ j, b.repr v₂ j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv₂ (b.repr.injective (Finsupp.ext fun j => by simp [hcon j]))
    have : a ⊗ₜ[ℂ] v₂ ∈ (⊥ : Subrepresentation ρ).toSubmodule := by rw [h]; trivial
    have h0 : a ⊗ₜ[ℂ] v₂ = 0 := this
    have := congrArg (fun z => F z j) h0
    simp only [F, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_zero,
      Finsupp.coe_zero, Pi.zero_apply] at this
    exact (smul_ne_zero hj ha) this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun Y => ?_ }
  by_cases hY : Y = ⊥
  · exact Or.inl hY
  right
  apply Subrepresentation.toSubmodule_injective
  refine eq_top_iff.2 fun z _ => ?_
  have := TensorProduct.span_tmul_eq_top ℂ V₁ V₂
  have hz : z ∈ Submodule.span ℂ {t | ∃ a b', a ⊗ₜ[ℂ] b' = t} := by rw [this]; trivial
  refine Submodule.span_le.2 ?_ hz
  rintro _ ⟨a, b', rfl⟩
  exact key Y hY a b'

end RestrictedTensor

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.TensorProductTheorem.Window
section
noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}

theorem sub_fixedProj_mem_span (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (u : V) :
    u - (fixedProj ρ hρ hKc hKo u : V) ∈
      Submodule.span ℂ (range fun k : K => ρ k u - u) := by
  classical
  obtain ⟨N, hNo, hNK, hNu, hnorm, hfin⟩ :=
    exists_normal_subgroup hKc hKo (U := (stabilizerOf ρ u : Set G))
      ((hρ u).mem_nhds (one_mem _))
  let _ : Fintype (K ⧸ N.subgroupOf K) := Fintype.ofFinite _
  have hu : u ∈ fixedVectors ρ N := fun n hn => hNu hn
  set c : ℂ := (Fintype.card (K ⧸ N.subgroupOf K) : ℂ)
  have hc : c ≠ 0 := by
    simp only [c, ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  set w : V := c⁻¹ • cosetSum ρ K N u
  have hw : w ∈ fixedVectors ρ K :=
    Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hu)
  have hdiff : u - w = -(c⁻¹ • ∑ q : K ⧸ N.subgroupOf K,
      (ρ ((Quotient.out q : K) : G) u - u)) := by
    rw [Finset.sum_sub_distrib, ← cosetSum_apply, Finset.sum_const, Finset.card_univ,
      smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    simp [w]
  have hspan : u - w ∈ Submodule.span ℂ (range fun k : K => ρ k u - u) := by
    rw [hdiff]
    refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_))
    exact Submodule.subset_span ⟨Quotient.out q, rfl⟩
  have hle : Submodule.span ℂ (range fun k : K => ρ k u - u) ≤ coinvariantsKer ρ K := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact sub_mem_coinvariantsKer k.2 u
  have heq : fixedProj ρ hρ hKc hKo u = ⟨w, hw⟩ :=
    (fixedProj_eq_iff hρ hKc hKo).2 (hle hspan)
  rw [heq]
  exact hspan

theorem fixedProj_mem (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (X : Subrepresentation ρ) {x : V} (hx : x ∈ X.toSubmodule) :
    (fixedProj ρ hρ hKc hKo x : V) ∈ X.toSubmodule := by
  have h1 := sub_fixedProj_mem_span hρ hKc hKo x
  have h2 : Submodule.span ℂ (range fun k : K => ρ k x - x) ≤ X.toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact X.toSubmodule.sub_mem (X.apply_mem_toSubmodule _ hx) hx
  have := X.toSubmodule.sub_mem hx (h2 h1)
  rwa [sub_sub_cancel] at this

variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

def heckeOp (g : G) : End ℂ (fixedVectors ρ K) :=
  fixedProj ρ hρ hKc hKo ∘ₗ ρ g ∘ₗ (fixedVectors ρ K).subtype

def heckeOps : Set (End ℂ (fixedVectors ρ K)) :=
  range (heckeOp hρ hKc hKo)

theorem heckeOp_apply (g : G) (m : fixedVectors ρ K) :
    heckeOp hρ hKc hKo g m = fixedProj ρ hρ hKc hKo (ρ g m) :=
  rfl

theorem heckeOp_mem_heckeOps (g : G) : heckeOp hρ hKc hKo g ∈ heckeOps hρ hKc hKo :=
  ⟨g, rfl⟩

theorem heckeOp_of_mem {g : G} (hg : g ∈ K) : heckeOp hρ hKc hKo g = 1 := by
  ext m
  rw [heckeOp_apply, fixedProj_apply_act hρ hKc hKo hg, fixedProj_apply_of_mem hρ hKc hKo m.2,
    Module.End.one_apply]

theorem heckeOp_mul_apply {a b : G}
    (hab : ∀ h ∈ K, ∃ k ∈ K, k * a = a * k ∧ (k⁻¹ * h) * b = b * (k⁻¹ * h))
    (m : fixedVectors ρ K) :
    heckeOp hρ hKc hKo a (heckeOp hρ hKc hKo b m) = heckeOp hρ hKc hKo (a * b) m := by
  obtain ⟨u, hu⟩ : ∃ u, u = ρ b m := ⟨_, rfl⟩
  have hspan := sub_fixedProj_mem_span hρ hKc hKo u

  have hkill : ∀ y ∈ Submodule.span ℂ (range fun k : K => ρ k u - u),
      fixedProj ρ hρ hKc hKo (ρ a y) = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨h, hh⟩, rfl⟩ := hy
      obtain ⟨k, hk, hka, hkb⟩ := hab h hh
      have hk' : k⁻¹ * h ∈ K := K.mul_mem (K.inv_mem hk) hh
      have h1 : ρ h u = ρ k u := by
        have : ρ (k⁻¹ * h) u = u := by
          rw [hu, ← Module.End.mul_apply, ← map_mul, hkb, map_mul, Module.End.mul_apply,
            m.2 _ hk']
        calc ρ h u = ρ k (ρ (k⁻¹ * h) u) := by
                rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
          _ = ρ k u := by rw [this]
      simp only
      rw [h1, map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, ← hka, map_mul,
        Module.End.mul_apply, fixedProj_apply_act hρ hKc hKo hk, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, map_smul, hx, smul_zero]
  have := hkill _ hspan
  rw [map_sub, map_sub, sub_eq_zero] at this
  subst hu
  rw [heckeOp_apply, heckeOp_apply, heckeOp_apply, ← this, map_mul, Module.End.mul_apply]

theorem isStable_comap (X : Subrepresentation ρ) :
    IsStable (heckeOps hρ hKc hKo) (X.toSubmodule.comap (fixedVectors ρ K).subtype) := by
  rintro _ ⟨g, rfl⟩ m hm
  rw [Submodule.mem_comap, heckeOp_apply]
  exact fixedProj_mem hρ hKc hKo X (X.apply_mem_toSubmodule g hm)

theorem isSimpleUnder_heckeOps [ρ.IsIrreducible] (hK : fixedVectors ρ K ≠ ⊥) :
    IsSimpleUnder (heckeOps hρ hKc hKo) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hK, fun p hp => ?_⟩
  by_cases hp0 : p = ⊥
  · exact Or.inl hp0
  right
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hm0' : (m : V) ≠ 0 := fun h => hm0 (Subtype.ext h)
  rw [eq_top_iff]
  intro m' _
  have hle : Submodule.span ℂ (range fun g => ρ g (m : V)) ≤
      p.comap ((fixedProj ρ hρ hKc hKo)) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hp _ (heckeOp_mem_heckeOps hρ hKc hKo g) m hm
  have := hle (mem_span_orbit (ρ := ρ) hm0' (m' : V))
  rw [Submodule.mem_comap] at this
  have he : fixedProj ρ hρ hKc hKo (m' : V) = m' :=
    Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo m'.2)
  rwa [he] at this


omit hρ hKc hKo in
theorem isIrreducible_of_forall (hρ : IsSmooth ρ) [Nontrivial V]
    (h : ∀ x y : V, x ≠ 0 → ∃ (K : Subgroup G) (hKc : IsCompact (K : Set G))
      (hKo : IsOpen (K : Set G)), x ∈ fixedVectors ρ K ∧ y ∈ fixedVectors ρ K ∧
        IsSimpleUnder (heckeOps hρ hKc hKo)) :
    ρ.IsIrreducible := by
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h0] at this
    exact hx this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun X => ?_ }
  by_cases hX : X.toSubmodule = ⊥
  · left
    ext x
    constructor
    · intro hx
      have : x ∈ X.toSubmodule := hx
      rw [hX] at this
      exact this
    · intro hx
      have : x = 0 := hx
      rw [this]
      exact X.toSubmodule.zero_mem
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  ext y
  refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
  obtain ⟨K, hKc, hKo, hxK, hyK, hsimple⟩ := h x y hx0
  have hst := isStable_comap hρ hKc hKo X
  rcases hsimple.2 _ hst with h0 | h0
  · exfalso
    have : (⟨x, hxK⟩ : fixedVectors ρ K) ∈ X.toSubmodule.comap (fixedVectors ρ K).subtype := hx
    rw [h0, Submodule.mem_bot] at this
    exact hx0 (congrArg Subtype.val this)
  · have : (⟨y, hyK⟩ : fixedVectors ρ K) ∈ X.toSubmodule.comap (fixedVectors ρ K).subtype := by
      rw [h0]; trivial
    exact this


omit hρ hKc hKo in
theorem fixedProj_comp_eq {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L] (ι : L →* G)
    (hρ : IsSmooth ρ) (hρι : IsSmooth (ρ.comp ι)) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {K' : Subgroup L} (hK'c : IsCompact (K' : Set L))
    (hK'o : IsOpen (K' : Set L)) (hK' : ∀ k ∈ K', ι k ∈ K) {u : V}
    (hu : ∀ h ∈ K, ∃ k ∈ K', ρ h u = ρ (ι k) u) :
    (fixedProj (ρ.comp ι) hρι hK'c hK'o u : V) = fixedProj ρ hρ hKc hKo u := by
  have hmem : (fixedProj ρ hρ hKc hKo u : V) ∈ fixedVectors (ρ.comp ι) K' :=
    fun k hk => (fixedProj ρ hρ hKc hKo u).2 _ (hK' k hk)
  have h1 := sub_fixedProj_mem_span hρ hKc hKo u
  have h2 : Submodule.span ℂ (range fun k : K => ρ k u - u) ≤ coinvariantsKer (ρ.comp ι) K' := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨k, hk, hkh⟩ := hu h hh
    simp only [SetLike.mem_coe]
    rw [hkh]
    exact sub_mem_coinvariantsKer (ρ := ρ.comp ι) hk u
  have := (fixedProj_eq_iff hρι hK'c hK'o (w := ⟨_, hmem⟩)).2 (h2 h1)
  rw [this]

end RestrictedTensor

end GroundTheory.Automorphic
end
end

