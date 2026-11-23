module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresGr
section
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

def pq (a : Fin 3) : ZMod 2 := ((w 3 a : ℤ) : ZMod 2)

theorem pw_eq (a b : Fin 3) : pw a b = pq a - pq b := Int.cast_sub _ _

def GrM {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (α β : Fin 3 → ZMod 2)
    (M : Matrix (Fin 3) (Fin 3) R) : Prop := ∀ a b, M a b ∈ evp σ (α a - β b)

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k}

namespace Box

structure Gr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (B : Box F 3 R) (σ : R →ₐ[O] R)
    (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, GrM σ pq pq (B.r s).mat
  g : ∀ v, GrM σ (π v) pq (B.g v : Matrix (Fin 3) (Fin 3) R)

variable {K : Type} [CommRing K]

structure Ev (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, (B.r s).mat ∈ adp K 0
  g : ∀ v a b, π v a ≠ pq b → (B.g v : Matrix (Fin 3) (Fin 3) K) a b = 0
  stab : ∀ j s, adp K j ≤ (adp K j).comap (B.ad s)

variable {B : Box F 3 K} {π : F.V → Fin 3 → ZMod 2}

def Ev.ad (h : B.Ev π) (j : ZMod 2) : Representation K F.Γ (adp K j) := B.ad.subrepresentation (adp K j) (h.stab j)

@[simp] theorem Ev.ad_apply (h : B.Ev π) (j : ZMod 2) (s : F.Γ) (X : adp K j) :
    ((h.ad j s X : adp K j) : Matrix (Fin 3) (Fin 3) K) = B.ad s X := rfl


variable (B) in
def bp (j : ZMod 2) (v : F.V) : Submodule K (adp K j) := (B.b v).comap (adp K j).subtype

end Box

section CO

variable {O : Type} [CommRing O] [IsLocalRing O] {C' C : Type} [CommRing C'] [Algebra O C'] [IsCO O C'] [CommRing C]
  [Algebra O C]

structure SetLift.Gr {p : C' →ₐ[O] C} {B : Box F 3 C} (D : SetLift p B) (σ' : C' →ₐ[O] C')
    (π : F.V → Fin 3 → ZMod 2) : Prop where
  r : ∀ s, GrM σ' pq pq (D.r s : Matrix (Fin 3) (Fin 3) C')
  g : ∀ v, GrM σ' (π v) pq (D.g v : Matrix (Fin 3) (Fin 3) C')
  t : ∀ v s, GrM σ' (π v) (π v) (D.t v s : Matrix (Fin 3) (Fin 3) C')

def formp (σ' : C' →ₐ[O] C') (K : Ideal C') (j : ZMod 2) :
    Submodule (ResidueField O) (K →ₗ[O] ResidueField O) where
  carrier := {u | ∀ i, i ≠ j → ∀ y : K, (y : C') ∈ evp σ' i → u y = 0}
  add_mem' h h' i e y hy := by simp [h i e y hy, h' i e y hy]
  zero_mem' _ _ _ _ := rfl
  smul_mem' c u h i e y hy := by simp [h i e y hy]


variable (O) in
def HasObsG {R : Type} [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) (H : Type) [AddCommGroup H]
    [Module (ResidueField O) H] : Prop :=
  ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (p : C' →ₐ[O] R) (σ' : C' →ₐ[O] C'), Function.Surjective p →
    maximalIdeal C' * RingHom.ker p = ⊥ → (∀ y, σ' (σ' y) = y) → (∀ y, p (σ' y) = σ (p y)) →
    ∃ ob : formp σ' (RingHom.ker p) j →ₗ[ResidueField O] H, ∀ u, ob u = 0 →
      ∀ (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (q : C' →ₐ[O] C'') (p'' : C'' →ₐ[O] R),
        p''.comp q = p → Function.Surjective q → (∀ y : RingHom.ker p, u.1 y = 0 → q y = 0) →
        ∃ s : R →ₐ[O] C'', p''.comp s = AlgHom.id O R

end CO

end UpperTheory.V.Fr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExistsPaddedFamily
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem exists_padded_family {κ M : Type} [Finite κ] [Zero M] (q : κ → Prop) (f : κ → M) (n : ℕ)
    (h : Nat.card {u // q u} ≤ n) :
    ∃ G : Fin n → M, (∀ i, G i = 0 ∨ ∃ u, q u ∧ G i = f u) ∧ ∀ u, q u → ∃ i, G i = f u := by
  classical
  haveI := Fintype.ofFinite κ
  have hc : Fintype.card {u // q u} ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨Function.extend e (fun u => f u.1) 0, ?_, ?_⟩
  · intro i
    by_cases hi : ∃ u, e u = i
    · obtain ⟨u, rfl⟩ := hi
      right
      exact ⟨u.1, u.2, by rw [e.injective.extend_apply]⟩
    · left
      rw [Function.extend_apply' _ _ _ hi]
      rfl
  · intro u hu
    exact ⟨e ⟨u, hu⟩, by rw [e.injective.extend_apply]⟩

theorem UpperTheory.V.Fr.ep_pad :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} (S : Space O F 3) (x : Ideal S.A) (L : S.Loc x) (σ : L.R →ₐ[L.O'] L.R), L.IsInv σ → ∀ P : GPres L.O' σ, Nat.card {u // P.wf u = 0} + (3 * F.d + 1) ≤ P.a → Nat.card {u // P.wf u = 1} ≤ P.g → L.ρ.ee = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (.inr i))) → Nonempty L.EPres := by
  intro l _ O _ _ F S x L σ hσ P h0 h1 hee
  obtain ⟨Fe, hF, hF'⟩ := exists_padded_family (fun u => P.wf u = 0) P.f (P.a - (3 * F.d + 1)) (by omega)
  obtain ⟨Go, hG, hG'⟩ := exists_padded_family (fun u => P.wf u = 1) P.f P.g h1
  have two : ∀ j : ZMod 2, j = 0 ∨ j = 1 := by decide
  refine ⟨{ a := P.a, b := P.a - (3 * F.d + 1), g := P.g, p := P.p, Fe := Fe, Go := Go,
            num := by omega, surj := P.surj, ker := ?_, even := ?_, odd := ?_, min := P.min,
            ent := ?_, base := ?_, ee := hee }⟩
  · rw [P.ker]
    apply le_antisymm
    · apply Ideal.span_mono
      rintro _ ⟨u, rfl⟩
      rcases two (P.wf u) with h | h
      · exact Or.inl (hF' u h)
      · exact Or.inr (hG' u h)
    · rw [Ideal.span_le]
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · rcases hF i with h | ⟨u, -, h⟩
        · rw [h]; exact Ideal.zero_mem _
        · rw [h]; exact Ideal.subset_span ⟨u, rfl⟩
      · rcases hG i with h | ⟨u, -, h⟩
        · rw [h]; exact Ideal.zero_mem _
        · rw [h]; exact Ideal.subset_span ⟨u, rfl⟩
  · intro i
    rcases hF i with h | ⟨u, hu, h⟩
    · rw [h]; exact Submodule.zero_mem _
    · rw [h, ← hu]; exact P.hf u
  · intro i
    rcases hG i with h | ⟨u, hu, h⟩
    · rw [h]; exact Submodule.zero_mem _
    · rw [h, ← hu]; exact P.hf u
  · intro s i j
    rw [P.part]
    exact hσ.ent s i j
  · intro y
    rw [P.part]
    exact hσ.base y
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FinrankStructMapYRange
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.finrank_structMapY_range :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → Module.rank k (F.strY k) ≤ C₀ := by
  intro l _ k _ _ F C₀ hF
  obtain ⟨-, -, hΨst, -, -⟩ := UpperTheory.V.Fr.star hF
  choose gv hgv using hF.f3
  set ρ := chRep (F.Ψ⁻¹.comp F.del.ker.subtype) with hρ
  have hρapp : ∀ (g : F.G0) (w : k), ρ g w = ((F.Ψ (g : F.Γ) : k))⁻¹ * w := by
    intro g w
    simp [hρ, chRep]
  have hne : ∀ γ : F.Γ, ((F.Ψ γ : k)) ≠ 0 := fun γ => Units.ne_zero _
  have hl : ∀ v s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ _ => rfl
  have ha : ∀ v, ((F.Ψ (F.loc v (gv v)) : k)) ≠ 1 := by
    intro v h
    apply hgv v
    rw [Units.val_eq_one.mp h, one_pow]
  have hΨlc : IsLocallyConstant (fun g : F.G0 => F.Ψ (g : F.Γ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun h : F.G0 => g⁻¹ * h) ⁻¹' ((↑) ⁻¹' (F.Ψ.ker : Set F.Γ)), ?_, ?_, ?_⟩
    · exact (hF.Ψ_open.preimage continuous_subtype_val).preimage (continuous_const.mul continuous_id)
    · simp
    · intro h hh
      simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv] at hh
      exact (inv_mul_eq_one.mp hh).symm
  let xf : (F.G0 → k) → F.G0 → k := fun y g => ((F.Ψ (g : F.Γ) : k))⁻¹ * y g
  let af : (F.G0 → k) → F.V × Bool → k := fun y p =>
    if p.2 then (1 - ((F.Ψ (F.loc p.1 (gv p.1)) : k))⁻¹)⁻¹ * y (F.star (F.loc0 p.1 (gv p.1)))
    else -((((F.Ψ (F.loc p.1 (gv p.1)) : k)) - 1)⁻¹ * y (F.loc0 p.1 (gv p.1)))
  have hmem : ∀ y ∈ F.strY k, (xf y, af y) ∈ Z1C F.loc2 ρ (fun _ => ⊥) := by
    intro y hy
    obtain ⟨hlc, hcoc, hg0, hα, hβ⟩ := hy
    refine ⟨?_, ?_, ?_⟩
    · exact hΨlc.comp₂ hlc (fun u w => ((u : k))⁻¹ * w)
    · intro s t
      rw [hρapp]
      simp only [xf]
      rw [hcoc s t, Subgroup.coe_mul, map_mul, Units.val_mul, smul_eq_mul]
      have := hne s
      have := hne t
      field_simp
    · rintro ⟨v, b⟩ s
      rw [Submodule.mem_bot, hρapp]
      dsimp only
      have h1 : ((F.Ψ (F.loc v (gv v)) : k)) - 1 ≠ 0 := sub_ne_zero.mpr (ha v)
      have h2 : 1 - ((F.Ψ (F.loc v (gv v)) : k))⁻¹ ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        exact ha v (inv_eq_one.mp h.symm)
      have := hne (F.loc v (gv v))
      have := hne (F.loc v s)
      cases b
      · obtain ⟨α, hα'⟩ := hα v
        have key : af y (v, false) = -α := by
          simp only [af, Bool.false_eq_true, if_false]
          rw [hα' (gv v), smul_eq_mul]
          field_simp
        rw [key]
        simp only [xf, Frame.loc2, Bool.false_eq_true, if_false]
        rw [hl, hα' s, smul_eq_mul]
        field_simp
        ring
      · obtain ⟨β, hβ'⟩ := hβ v
        have key : af y (v, true) = β := by
          simp only [af, if_true]
          rw [hβ' (gv v), smul_eq_mul, Units.val_inv_eq_inv_val]
          field_simp
        have hc : F.star (F.loc0 v s⁻¹) = F.conj (F.loc0 v s) := by
          show F.conj ((F.loc0 v s⁻¹)⁻¹) = _
          rw [map_inv (F.loc0 v) s, inv_inv]
        have hcv : F.Ψ ((F.conj (F.loc0 v s) : F.G0) : F.Γ) = F.Ψ (F.loc v s) := by
          rw [← hc, hΨst, hl, map_inv, map_inv, inv_inv]
        rw [key]
        simp only [xf, Frame.loc2, if_true, MonoidHom.comp_apply]
        rw [hcv, ← hc, hβ' s⁻¹]
        simp only [map_inv, inv_inv, Units.val_inv_eq_inv_val, smul_eq_mul]
        field_simp
        ring
  let φ : F.strY k →ₗ[k] Z1C F.loc2 ρ (fun _ => ⊥) :=
    { toFun := fun y => ⟨(xf y.1, af y.1), hmem y.1 y.2⟩
      map_add' := by
        intro y z
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun p => ?_)
        · simp [xf, mul_add]
        · simp only [af, Submodule.coe_add, Prod.snd_add, Pi.add_apply]
          split_ifs <;> ring
      map_smul' := by
        intro a y
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun p => ?_)
        · simp [xf]
          ring
        · simp only [af, SetLike.val_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> ring }
  have hinj : Function.Injective
      ((Submodule.mkQ (Submodule.comap (Z1C F.loc2 ρ (fun _ => ⊥)).subtype (continuousCoboundaries1 ρ (fun _ => ⊥)))).comp φ) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap] at hy
    obtain ⟨X, hX, -⟩ := hy
    obtain ⟨-, -, hg0, -, -⟩ := y.2
    have hy' : ∀ g, (y : F.G0 → k) g = X - ((F.Ψ (g : F.Γ) : k)) * X := by
      intro g
      have h := hX g
      rw [hρapp] at h
      have := hne g
      change ((F.Ψ (g : F.Γ) : k))⁻¹ * (y : F.G0 → k) g = _ at h
      field_simp at h
      linear_combination h
    have hd : ((F.Ψ (F.g0 : F.Γ) : k)) - ((F.Ψ (F.g0 : F.Γ) : k))⁻¹ ≠ 0 := by
      intro h
      apply hF.baseSubgroup_spec
      have hu := hne F.g0
      rw [sub_eq_zero] at h
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two]
      calc ((F.Ψ (F.g0 : F.Γ) : k)) * (F.Ψ (F.g0 : F.Γ) : k)
          = (F.Ψ (F.g0 : F.Γ) : k) * ((F.Ψ (F.g0 : F.Γ) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hu
    have hX0 : X = 0 := by
      have h := hg0
      rw [hy', hy', hΨst, Units.val_inv_eq_inv_val] at h
      have h' : (((F.Ψ (F.g0 : F.Γ) : k)) - ((F.Ψ (F.g0 : F.Γ) : k))⁻¹) * X = 0 := by
        linear_combination -h
      exact (mul_eq_zero.mp h').resolve_left hd
    apply Subtype.ext
    funext g
    rw [hy', hX0]
    simp
  exact (LinearMap.rank_le_of_injective _ hinj).trans hF.b1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameExtensionOfLocallyConstant
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_open_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (hf : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f hf

theorem UpperTheory.V.Fr.frame_extension_of_locallyConstant :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ a ∈ F.strS k, ∃ x ∈ Z1C F.loc (chRep (F.Ψ⁻¹ ^ 2 * F.delK k)) (fun _ => ⊥), x.1 F.c = 0 ∧ ∀ g : F.G0, a g = x.1 g * F.Ψ g := by
  classical
  intro l _ k _ _ F C₀ h a ha
  obtain ⟨a1, a2, a3, a4⟩ := ha
  choose γ hγ using a4
  have hd : ∀ g : F.G0, F.del g = 1 := fun g => g.2
  have hcc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right h.c_sq
  have hconj : ∀ g : F.G0, ((F.conj g : F.G0) : F.Γ) = F.c * g * F.c := fun g => by
    rw [← hcc]; nth_rewrite 1 [hcc]; rfl
  have a0 : a 1 = 0 := by
    have := a2 1 1
    simpa using this
  have ainv : ∀ g, a g⁻¹ = - a g := fun g => by
    have := a2 g g⁻¹
    rw [mul_inv_cancel, a0] at this
    simp only [smul_eq_mul, Subgroup.coe_inv, map_inv] at this
    rw [← mul_add] at this
    have h2 := (mul_eq_zero.1 this.symm).resolve_left (Units.ne_zero _)
    linear_combination h2
  have ac : ∀ g, a (F.conj g) = - a g := fun g => by
    rw [← ainv, ← a3 g⁻¹]; simp [Frame.star]
  have Ψc : ∀ g : F.G0, F.Ψ (F.conj g) = F.Ψ g := fun g => by simp [hconj, h.Ψ_c]
  let b : F.G0 → k := fun g => a g * (((F.Ψ g)⁻¹ : kˣ) : k)
  have b1 : IsLocallyConstant b := by
    refine a1.mul ?_
    exact ((lc_of_open_ker F.Ψ h.Ψ_open).comp_continuous continuous_subtype_val).comp
      (fun u : kˣ => ((u⁻¹ : kˣ) : k))
  have b2 : ∀ g g' : F.G0, b (g * g') = b g + ((F.Ψ g : k)⁻¹) ^ 2 * b g' := fun g g' => by
    simp only [b, a2, smul_eq_mul, Subgroup.coe_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_mul]
    have := (F.Ψ g).ne_zero
    have := (F.Ψ g').ne_zero
    field_simp
  have bc : ∀ g, b (F.conj g) = - b g := fun g => by simp only [b, ac, Ψc, neg_mul]
  let e : ℤˣ → F.Γ := fun u => if u = 1 then 1 else F.c
  have he : ∀ s : F.Γ, s * e (F.del s) ∈ F.del.ker := fun s => by
    rw [MonoidHom.mem_ker, map_mul]
    rcases Int.units_eq_one_or (F.del s) with h1 | h1 <;> simp [e, h1, h.del_c]
  let p : F.Γ → F.G0 := fun s => ⟨s * e (F.del s), he s⟩
  have pc : Continuous p :=
    Continuous.subtype_mk (continuous_id.mul ((lc_of_open_ker F.del h.del_open).comp e).continuous) _
  have p1 : ∀ g : F.G0, p g = g := fun g => Subtype.ext (by simp [p, e, hd])
  have p2 : ∀ g : F.G0, p (g * F.c) = g := fun g =>
    Subtype.ext (by simp [p, e, hd, h.del_c, mul_assoc, h.c_sq])
  have dec : ∀ s : F.Γ, ∃ g : F.G0, s = g ∨ s = g * F.c := fun s => by
    refine ⟨p s, ?_⟩
    rcases Int.units_eq_one_or (F.del s) with h1 | h1
    · left; simp [p, e, h1]
    · right; simp [p, e, h1, mul_assoc, h.c_sq]
  have χ1 : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) g : kˣ) : k) = ((F.Ψ g : k)⁻¹) ^ 2 := fun g => by
    simp [Frame.delK, hd]
  have χ2 : ∀ g : F.G0, (((F.Ψ⁻¹ ^ 2 * F.delK k) (g * F.c) : kˣ) : k) = -((F.Ψ g : k)⁻¹) ^ 2 := fun g => by
    simp [Frame.delK, hd, h.del_c, h.Ψ_c]
  refine ⟨(fun s => b (p s), fun v => - γ v), ⟨b1.comp_continuous pc, fun s t => ?_, fun v s => ?_⟩, ?_, fun g => ?_⟩
  · show b (p (s * t)) = b (p s) + chRep _ s (b (p t))
    rw [chRep_apply]
    obtain ⟨g, rfl | rfl⟩ := dec s <;> obtain ⟨g', rfl | rfl⟩ := dec t
    · rw [← Subgroup.coe_mul, p1, p1, p1, χ1, b2]
    · rw [← mul_assoc, ← Subgroup.coe_mul, p2, p1, p2, χ1, b2]
    · have : (g : F.Γ) * F.c * g' = ((g * F.conj g' : F.G0) : F.Γ) * F.c := by
        simp [hconj, mul_assoc, h.c_sq]
      rw [this, p2, p2, p1, χ2, b2, bc]; ring
    · have : (g : F.Γ) * F.c * (g' * F.c) = ((g * F.conj g' : F.G0) : F.Γ) := by
        simp [hconj, mul_assoc]
      rw [this, p1, p2, p2, χ2, b2, bc]; ring
  · show b (p (F.loc0 v s)) - (chRep _ (F.loc0 v s : F.Γ) (- γ v) - - γ v) ∈ (⊥ : Submodule k k)
    rw [chRep_apply, p1, χ1, Submodule.mem_bot]
    have h1 : F.loc v s = (F.loc0 v s : F.Γ) := rfl
    simp only [b, hγ, h1, smul_eq_mul, Units.val_inv_eq_inv_val]
    have := (F.Ψ (F.loc0 v s)).ne_zero
    field_simp
    ring
  · show b (p F.c) = 0
    have := p2 1
    simp only [OneMemClass.coe_one, one_mul] at this
    simp [this, b, a0]
  · show a g = b (p g) * _
    rw [p1]
    simp [b]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FramePointAlgCoordEq
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_alg_coord_eq :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 3 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → ∀ U : Subalgebra k Q, (∀ g, ρ.r g 1 0 ∈ U) → (fun g => (Subalgebra.toSubmodule U).mkQ (ρ.r g 2 0)) ∈ F.strS (Q ⧸ Subalgebra.toSubmodule U) := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hb ht hlc U hU
  have hz : ∀ g (i j : Fin 3), i < j → ρ.r g i j = 0 := by
    intro g i j hij
    have hm : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rw [ht] at hm
    exact (Ideal.mem_bot).1 hm
  have hd : ∀ g (i : Fin 3), ρ.r g i i = algebraMap k Q ↑(F.Ψ ↑g ^ w 3 i) := hb.1
  have h21 : ∀ g, ρ.r g 2 1 ∈ U := by
    intro g
    have e : ρ.r g 2 1 = ρ.r (F.star g) 1 0 := by
      rw [(star hF).2.2.2.2 ρ g 1 0]
      rfl
    rw [e]
    exact hU _
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have hq : ∀ x : Q, x ∈ U → (Subalgebra.toSubmodule U).mkQ x = 0 := by
    intro x hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨(hlc 2 0).comp _, ?_, ?_, ?_⟩
  · intro g h
    dsimp only
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, hd h 0, hd g 2, w0, w2, zpow_one, _root_.zpow_neg_one]
    have e1 : ρ.r g 2 0 * algebraMap k Q ↑(F.Ψ ↑h) = (↑(F.Ψ ↑h) : k) • ρ.r g 2 0 := by
      rw [Algebra.smul_def, mul_comm]
    have e3 : algebraMap k Q ↑(F.Ψ ↑g)⁻¹ * ρ.r h 2 0 = (↑(F.Ψ ↑g)⁻¹ : k) • ρ.r h 2 0 := by
      rw [Algebra.smul_def]
    rw [e1, e3, map_add (f := _), map_add (f := _), map_smul, map_smul, hq _ (U.mul_mem (h21 g) (hU h)), add_zero]
  · intro g
    dsimp only
    rw [(star hF).2.2.2.2 ρ g 2 0]
    rfl
  · intro v
    obtain ⟨t, ht2⟩ := hF.f3 v
    refine ⟨((↑(F.Ψ (F.loc v t)) : k) - ↑(F.Ψ (F.loc v t))⁻¹)⁻¹ • (Subalgebra.toSubmodule U).mkQ (ρ.r (F.loc0 v t) 2 0), fun s => ?_⟩
    have hl : ∀ x, ((F.loc0 v x : F.G0) : F.Γ) = F.loc v x := fun _ => rfl
    have e := congrArg (fun M => M 2 0) (ρ.ord v ![t, t, s])
    have z01 := hz (F.loc0 v t) 0 1 (by decide)
    have z02 := hz (F.loc0 v t) 0 2 (by decide)
    have z12 := hz (F.loc0 v t) 1 2 (by decide)
    have y01 := hz (F.loc0 v s) 0 1 (by decide)
    have y02 := hz (F.loc0 v s) 0 2 (by decide)
    have y12 := hz (F.loc0 v s) 1 2 (by decide)
    simp (config := {decide := true}) only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.one_apply, Matrix.zero_apply, smul_eq_mul, z01, z02, z12, y01, y02, y12, hd, hb.2, hl, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg_one, Units.val_one, map_one, if_true, if_false, mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add] at e
    set x : k := ↑(F.Ψ (F.loc v t)) with hx
    set xi : k := ↑(F.Ψ (F.loc v t))⁻¹ with hxi
    set y : k := ↑(F.Ψ (F.loc v s)) with hy
    set yi : k := ↑(F.Ψ (F.loc v s))⁻¹ with hyi
    have key : algebraMap k Q ((xi - x) * (xi - 1)) * ρ.r (F.loc0 v s) 2 0 + algebraMap k Q ((xi - 1) * (y - yi)) * ρ.r (F.loc0 v t) 2 0 = -(ρ.r (F.loc0 v t) 2 1 * ρ.r (F.loc0 v t) 1 0 * (algebraMap k Q y - algebraMap k Q yi) + (algebraMap k Q xi - algebraMap k Q x) * ρ.r (F.loc0 v t) 2 1 * ρ.r (F.loc0 v s) 1 0) := by
      simp only [map_mul, map_sub, map_one]
      linear_combination e
    have hne1 : xi - 1 ≠ 0 := by
      intro h
      apply ht2
      have h' : (F.Ψ (F.loc v t))⁻¹ = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h)
      rw [inv_eq_one.1 h', one_pow]
    have hne2 : xi - x ≠ 0 := by
      intro h
      apply ht2
      have h' : (F.Ψ (F.loc v t))⁻¹ = F.Ψ (F.loc v t) := Units.ext (sub_eq_zero.1 h)
      calc F.Ψ (F.loc v t) ^ 2 = (F.Ψ (F.loc v t))⁻¹ * F.Ψ (F.loc v t) := by rw [sq, h']
        _ = 1 := inv_mul_cancel _
    have hne3 : x - xi ≠ 0 := fun h => hne2 (by rw [← neg_sub, h, neg_zero])
    have hc : (xi - x) * (xi - 1) ≠ 0 := mul_ne_zero hne2 hne1
    dsimp only
    rw [smul_smul, ← map_smul, ← sub_eq_zero, ← map_sub]
    apply hq
    have eq : ρ.r (F.loc0 v s) 2 0 - ((y - yi) * (x - xi)⁻¹) • ρ.r (F.loc0 v t) 2 0 = algebraMap k Q ((xi - x) * (xi - 1))⁻¹ * (algebraMap k Q ((xi - x) * (xi - 1)) * ρ.r (F.loc0 v s) 2 0 + algebraMap k Q ((xi - 1) * (y - yi)) * ρ.r (F.loc0 v t) 2 0) := by
      rw [Algebra.smul_def, mul_add, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
      have h3 : ((xi - x) * (xi - 1))⁻¹ * ((xi - 1) * (y - yi)) = -((y - yi) * (x - xi)⁻¹) := by
        field_simp
        ring
      rw [h3, map_neg, neg_mul, sub_eq_add_neg]
    rw [eq, key]
    exact mul_mem (U.algebraMap_mem _) (neg_mem (add_mem (mul_mem (mul_mem (h21 _) (hU _)) (sub_mem (U.algebraMap_mem _) (U.algebraMap_mem _))) (mul_mem (mul_mem (sub_mem (U.algebraMap_mem _) (U.algebraMap_mem _)) (h21 _)) (hU _))))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrExt
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_ext :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ},
      F.Ok C₀ → ∀ (C : Type) [CommRing C] (r r' : F.Γ →* GG (m := n) (R := C)),
        (∀ s, (r s).right = F.del s) → (∀ s, (r' s).right = F.del s) →
        (r F.c).mat = (r' F.c).mat → (∀ s : F.G0, (r s).mat = (r' s).mat) → r = r' := by
  intro l _ k _ _ F C₀ n hF C _ r r' h h' hc h0
  have key : ∀ s, (r s).mat = (r' s).mat → r s = r' s := fun s hs =>
    SemidirectProduct.ext (Units.ext hs) ((h s).trans (h' s).symm)
  refine MonoidHom.ext fun s => ?_
  rcases Int.units_eq_one_or (F.del s) with hs | hs
  · exact key s (h0 ⟨s, hs⟩)
  · have hm : s * F.c ∈ F.del.ker := by
      rw [MonoidHom.mem_ker, map_mul, hs, hF.del_c]
      simp
    have e := key _ (h0 ⟨s * F.c, hm⟩)
    rw [map_mul, map_mul, key _ hc] at e
    exact mul_right_cancel e
end

