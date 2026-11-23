module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SingleMemOfSpan
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem single_mem_of_span {C K : Type} [CommRing C] [CommRing K] [Algebra C K]
    (A : Subalgebra C (AddMonoidAlgebra K ℤ)) (j : ℤ) (s : Set K)
    (hs : ∀ x ∈ s, AddMonoidAlgebra.single j x ∈ A) {x : K} (hx : x ∈ Submodule.span C s) :
    AddMonoidAlgebra.single j x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero => rw [AddMonoidAlgebra.single_zero]; exact A.zero_mem
  | add y z _ _ hy hz => rw [AddMonoidAlgebra.single_add]; exact A.add_mem hy hz
  | smul c y _ hy => rw [← AddMonoidAlgebra.smul_single]; exact A.smul_mem hy c

theorem UpperTheory.V.Fr.alg_ft :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} (C : Type) [CommRing C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), (∀ i j, (Submodule.span C (Set.range fun g => ρ.r g i j)).FG) → Algebra.FiniteType C (lauSub (ρ.part C)) := by
  intro l _ k _ F n C _ K _ _ ρ h
  choose S hS using h
  set G : Set (AddMonoidAlgebra K ℤ) :=
    ⋃ i, ⋃ j, (fun x => AddMonoidAlgebra.single (w n i - w n j) x) '' (S i j : Set K) with hG
  have hGfin : G.Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => (S i j).finite_toSet.image _
  have hGmem : ∀ i j x, x ∈ (S i j : Set K) →
      AddMonoidAlgebra.single (w n i - w n j) x ∈ Algebra.adjoin C G := fun i j x hx =>
    Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨x, hx, rfl⟩⟩⟩)
  have hent : ∀ g i j, AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j) ∈ Algebra.adjoin C G :=
    fun g i j => single_mem_of_span (Algebra.adjoin C G) _ (S i j) (hGmem i j)
      (by rw [hS i j]; exact Submodule.subset_span ⟨g, rfl⟩)
  have hlist : ∀ L : List (F.G0 × Fin n × Fin n),
      AddMonoidAlgebra.single ((L.map fun s => w n s.2.1 - w n s.2.2).sum)
        ((L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod) ∈ Algebra.adjoin C G := by
    intro L
    induction L with
    | nil =>
      simp only [List.map_nil, List.sum_nil, List.prod_nil]
      rw [← AddMonoidAlgebra.one_def]
      exact (Algebra.adjoin C G).one_mem
    | cons s L ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [← AddMonoidAlgebra.single_mul_single]
      exact mul_mem (hent _ _ _) ih
  have hmon : ∀ j, ∀ x ∈ ρ.mon j, AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G := by
    rintro j x ⟨L, hL, rfl⟩
    rw [← hL]
    exact hlist L
  have hpart : ∀ j x, x ∈ ρ.part C j → AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G :=
    fun j x hx => single_mem_of_span _ j _ (hmon j) hx
  have heq : Algebra.adjoin C G = lauSub (ρ.part C) := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      obtain ⟨i, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨j, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨x, hx, rfl⟩ := hy
      apply single_mem_lauSub
      have hx' : x ∈ Submodule.span C (Set.range fun g => ρ.r g i j) := by
        rw [← hS i j]
        exact Submodule.subset_span hx
      refine Submodule.span_le.mpr ?_ hx'
      rintro _ ⟨g, rfl⟩
      exact NRep.r_mem_part C ρ g i j
    · intro p hp
      have hp' : ∀ j, p.coeff j ∈ ρ.part C j := hp
      have hsum : p = p.coeff.sum fun j x => AddMonoidAlgebra.single j x := by
        apply AddMonoidAlgebra.ext
        rw [Finsupp.sum, AddMonoidAlgebra.coeff_sum]
        exact (Finsupp.sum_single _).symm
      rw [hsum]
      exact Subalgebra.sum_mem _ fun j _ => hpart j _ (hp' j)
  exact ⟨(Subalgebra.fg_top _).mpr ⟨hGfin.toFinset, by rw [Set.Finite.coe_toFinset]; exact heq⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrSMul
section
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Fr

namespace Frame

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (Q : Type) [CommRing Q] [Algebra k Q]

structure Low (y a : F.G0 → Q) : Prop where
  lcy : IsLocallyConstant y
  lca : IsLocallyConstant a
  muly : ∀ g h : F.G0, y (g * h) = (F.Ψ h : k) • y g + y h
  mula : ∀ g h : F.G0, a (g * h) = (F.Ψ h : k) • a g + y (F.star g) * y h + (((F.Ψ g)⁻¹ : kˣ) : k) • a h
  pol : ∀ g, a (F.star g) = a g
  nor : y F.g0 = y (F.star F.g0)
  loc : ∀ v, ∃ α β γ : Q, ∀ s, y (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - 1) • α ∧
    y (F.star (F.loc0 v s)) = (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • β ∧
    a (F.loc0 v s) = ((F.Ψ (F.loc v s) : k) - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • γ -
      (1 - (((F.Ψ (F.loc v s))⁻¹ : kˣ) : k)) • (α * β)

variable {F Q} {Q' : Type} [CommRing Q'] [Algebra k Q'] {y a : F.G0 → Q}

theorem Low.map (h : F.Low Q y a) (φ : Q →ₐ[k] Q') : F.Low Q' (fun g => φ (y g)) (fun g => φ (a g)) := by
  refine
    { lcy := h.lcy.comp φ
      lca := h.lca.comp φ
      muly g g' := by simp only [h.muly, map_add (f := _), map_smul]
      mula g g' := by simp only [h.mula, map_add (f := _), map_smul, map_mul]
      pol g := by simp only [h.pol]
      nor := congrArg φ h.nor
      loc := ?_ }
  intro v
  obtain ⟨α, β, γ, H⟩ := h.loc v
  refine ⟨φ α, φ β, φ γ, fun s => ?_⟩
  obtain ⟨h1, h2, h3⟩ := H s
  exact ⟨by rw [h1, map_smul], by rw [h2, map_smul], by rw [h3, map_sub, map_smul, map_smul, map_mul]⟩

theorem Low.comb (h : F.Low Q y a) (t : Q) {b : F.G0 → Q} (hb : b ∈ F.strS Q) :
    F.Low Q (fun g => t * y g) (fun g => t ^ 2 * a g + b g) := by
  refine
    { lcy := h.lcy.comp (t * ·)
      lca := (h.lca.comp (t ^ 2 * ·)).add hb.1
      muly g g' := by simp only [h.muly, Algebra.smul_def]; ring
      mula g g' := by simp only [h.mula, hb.2.1 g g', Algebra.smul_def]; ring
      pol g := by simp only [h.pol, hb.2.2.1 g]
      nor := congrArg (t * ·) h.nor
      loc := ?_ }
  intro v
  obtain ⟨α, β, γ, H⟩ := h.loc v
  obtain ⟨δ, H'⟩ := hb.2.2.2 v
  refine ⟨t * α, t * β, t ^ 2 * γ + δ, fun s => ?_⟩
  obtain ⟨h1, h2, h3⟩ := H s
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; simp only [Algebra.smul_def]; ring
  · rw [h2]; simp only [Algebra.smul_def]; ring
  · rw [h3, H' s]; simp only [Algebra.smul_def]; ring

theorem Low.zero : F.Low Q 0 0 :=
  ⟨IsLocallyConstant.const 0, IsLocallyConstant.const 0, by simp, by simp, fun _ => rfl, rfl,
    fun _ => ⟨0, 0, 0, by simp⟩⟩

theorem Low.strS (h : F.Low Q 0 a) : a ∈ F.strS Q := by
  refine ⟨h.lca, fun g g' => by simpa using h.mula g g', h.pol, fun v => ?_⟩
  obtain ⟨α, β, γ, H⟩ := h.loc v
  refine ⟨γ, fun s => ?_⟩
  obtain ⟨-, h2, h3⟩ := H s
  rw [h3, mul_comm α, ← smul_mul_assoc, ← h2]
  simp

theorem strS_mul (t : Q) (ha : a ∈ F.strS Q) : (fun g => t * a g) ∈ F.strS Q :=
  strS_map (LinearMap.mulLeft k t) ha

end Frame

namespace Space

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}
  {Q Q' : Type} [CommRing Q] [Algebra (ResidueField O) Q] [CommRing Q'] [Algebra (ResidueField O) Q']

structure FPt (S : Space O F n) (ξ : S.A →+* Q) : Prop where
  x0 : S.x0 ≤ RingHom.ker ξ
  alg : ∀ c : O, ξ (algebraMap O S.A c) = algebraMap (ResidueField O) Q (residue O c)

theorem FPt.comp {S : Space O F n} {ξ : S.A →+* Q} (h : S.FPt ξ) (φ : Q →ₐ[ResidueField O] Q') :
    S.FPt ((φ : Q →+* Q').comp ξ) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have : ξ x = 0 := h.x0 hx
    show φ (ξ x) = 0
    rw [this, map_zero]
  · intro c
    show φ (ξ _) = _
    rw [h.alg, AlgHom.commutes]

structure At (S : Space O F 3) (ξ : S.A →+* Q) (y a : F.G0 → Q) : Prop where
  fpt : S.FPt ξ
  low : S.u.triM ≤ RingHom.ker ξ
  hy : ∀ g, ξ (S.u.r g 1 0) = y g
  ha : ∀ g, ξ (S.u.r g 2 0) = a g

theorem At.comp {S : Space O F 3} {ξ : S.A →+* Q} {y a : F.G0 → Q} (h : S.At ξ y a) (φ : Q →ₐ[ResidueField O] Q') :
    S.At ((φ : Q →+* Q').comp ξ) (fun g => φ (y g)) (fun g => φ (a g)) := by
  refine ⟨h.fpt.comp φ, ?_, fun g => congrArg φ (h.hy g), fun g => congrArg φ (h.ha g)⟩
  intro x hx
  have : ξ x = 0 := h.low hx
  show φ (ξ x) = 0
  rw [this, map_zero]

end Space

end UpperTheory.V.Fr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TanFinite
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private theorem hom_eq_res (g : R →ₐ[O] ResidueField O) (x : R) : g x = res O R x := by
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap O R a, by rw [g.commutes, IsLocalRing.ResidueField.algebraMap_eq]⟩
  have hker : RingHom.ker (g : R →+* ResidueField O) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 : g (x - algebraMap O R a) = 0 := by
    have hm : x - algebraMap O R a ∈ RingHom.ker (g : R →+* ResidueField O) := by
      rw [hker]
      exact ha
    exact (RingHom.mem_ker).1 hm
  have h2 : res O R (x - algebraMap O R a) = 0 := (res_eq_zero_iff O R _).2 ha
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, AlgHom.commutes, AlgHom.commutes]

private theorem tan_mul (D : Tan O R) (f g : R) :
    D.1 (f * g) = res O R f * D.1 g + res O R g * D.1 f := D.2 f g

private theorem tan_one (D : Tan O R) : D.1 1 = 0 := by
  simpa using tan_mul D 1 1

private theorem tan_alg (D : Tan O R) (a : O) : D.1 (algebraMap O R a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, tan_one, smul_zero]

private theorem tan_finite : Module.Finite (ResidueField O) (Tan O R) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  let φ : Tan O R →ₗ[ResidueField O] (s → ResidueField O) :=
    { toFun := fun D i => D.1 (i : R)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective φ ((injective_iff_map_eq_zero φ).2 fun D hD => ?_)
  have h0 : ∀ i ∈ s, D.1 i = 0 := fun i hi => congrFun hD ⟨i, hi⟩
  have hm : ∀ y ∈ maximalIdeal R, D.1 y = 0 := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h0 z hz
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, add_zero]
    | smul c z hz ih =>
      have hz' : z ∈ maximalIdeal R := by
        rw [← hs]
        exact hz
      rw [smul_eq_mul, tan_mul, ih, (res_eq_zero_iff O R z).2 hz', mul_zero, zero_mul, add_zero]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h := hm _ ha
  rw [map_sub, tan_alg, sub_zero] at h
  exact h

private noncomputable def tanEquiv : (R →ₐ[O] DualNumber (ResidueField O)) ≃ Tan O R where
  toFun f := ⟨{ toFun := fun x => (f x).snd
                map_add' := fun x y => by simp
                map_smul' := fun a x => by simp }, fun x y => by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    show (f (x * y)).snd = res O R x • (f y).snd + res O R y • (f x).snd
    rw [map_mul, DualNumber.snd_mul, h, h, smul_eq_mul, smul_eq_mul, mul_comm (f x).snd]⟩
  invFun D :=
    { toFun := fun x => TrivSqZeroExt.inl (res O R x) + TrivSqZeroExt.inr (D.1 x)
      map_one' := by ext <;> simp [tan_one]
      map_mul' := fun x y => by ext <;> simp [tan_mul, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp
      commutes' := fun a => by
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl']
        · simp [tan_alg, TrivSqZeroExt.algebraMap_eq_inl'] }
  left_inv f := by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    refine AlgHom.ext fun x => ?_
    ext <;> simp [h]
  right_inv D := Subtype.ext (LinearMap.ext fun x => by simp)

end

theorem UpperTheory.V.Fr.pr_tan :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R], Module.Finite (ResidueField O) (Tan O R) ∧ Nat.card (R →ₐ[O] (DualNumber (ResidueField O))) = Nat.card (Tan O R) := by
  intro O _ _ R _ _ _
  exact ⟨tan_finite, Nat.card_congr tanEquiv⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrMap
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section

variable {K G W W' V : Type} [Field K] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module K W]
  [AddCommGroup W'] [Module K W'] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G)

private def trE (G V : Type) (e : W ≃ₗ[K] W') : ((G → W) × (V → W)) ≃ₗ[K] ((G → W') × (V → W')) :=
  (LinearEquiv.piCongrRight fun _ => e).prodCongr (LinearEquiv.piCongrRight fun _ => e)

private theorem trZ (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) (x : (G → W) × (V → W)) :
    trE G V e x ∈ Z1C loc ρ' b' ↔ x ∈ Z1C loc ρ b := by
  have h1 : (trE G V e x).1 = e ∘ x.1 := rfl
  have h2 : (trE G V e x).2 = e ∘ x.2 := rfl
  simp only [Z1C, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [h1, h2]
  simp only [Function.comp_apply]
  apply and_congr
  · constructor
    · intro hl
      exact IsLocallyConstant.desc _ _ hl e.injective
    · intro hl
      exact hl.comp e
  apply and_congr
  · apply forall_congr'
    intro s
    apply forall_congr'
    intro t
    rw [h, ← map_add (f := _)]
    exact e.injective.eq_iff
  · apply forall_congr'
    intro v
    apply forall_congr'
    intro s
    rw [h, ← map_sub, ← map_sub]
    exact hb v _

omit [TopologicalSpace G] in
private theorem trB (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) (x : (G → W) × (V → W)) :
    trE G V e x ∈ continuousCoboundaries1 ρ' b' ↔ x ∈ continuousCoboundaries1 ρ b := by
  have h1 : (trE G V e x).1 = e ∘ x.1 := rfl
  have h2 : (trE G V e x).2 = e ∘ x.2 := rfl
  simp only [continuousCoboundaries1, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  rw [h1, h2]
  simp only [Function.comp_apply]
  constructor
  · rintro ⟨X, hX1, hX2⟩
    refine ⟨e.symm X, fun s => ?_, fun v => ?_⟩
    · apply e.injective
      rw [map_sub, ← h, e.apply_symm_apply]
      exact hX1 s
    · rw [← hb v, map_sub, e.apply_symm_apply]
      exact hX2 v
  · rintro ⟨X, hX1, hX2⟩
    refine ⟨e X, fun s => ?_, fun v => ?_⟩
    · rw [hX1 s, map_sub, h]
    · rw [← map_sub, hb v]
      exact hX2 v

private theorem trMap (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) :
    (Z1C loc ρ b).map (trE G V e : _ →ₗ[K] _) = Z1C loc ρ' b' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (trZ loc e ρ ρ' b b' h hb x).mpr hx
  · intro hy
    refine ⟨(trE G V e).symm y, ?_, ?_⟩
    · exact (trZ loc e ρ ρ' b b' h hb _).mp (by simpa using hy)
    · simp

private theorem trH (e : W ≃ₗ[K] W') (ρ : Representation K G W) (ρ' : Representation K G W')
    (b : V → Submodule K W) (b' : V → Submodule K W') (h : ∀ g x, ρ' g (e x) = e (ρ g x))
    (hb : ∀ v x, e x ∈ b' v ↔ x ∈ b v) :
    Module.rank K (H1C loc ρ' b') = Module.rank K (H1C loc ρ b) := by
  let E : Z1C loc ρ b ≃ₗ[K] Z1C loc ρ' b' :=
    ((trE G V e).submoduleMap (Z1C loc ρ b)).trans (LinearEquiv.ofEq _ _ (trMap loc e ρ ρ' b b' h hb))
  have hE : ∀ z, (E z : (G → W') × (V → W')) = trE G V e z := fun z => rfl
  symm
  refine LinearEquiv.rank_eq (Submodule.Quotient.equiv _ _ E ?_)
  ext y
  rw [Submodule.mem_map_equiv]
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  rw [← trB e ρ ρ' b b' h hb, ← hE, E.apply_symm_apply]

end

theorem UpperTheory.V.Fr.n4ch :
    ∀ {k K G V : Type} [Field k] [Field K] (f : k →+* K) [Group G] [TopologicalSpace G] [CompactSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (χ : G →* kˣ) (b : V → Submodule k k) (b' : V → Submodule K K), (∀ v, (b v = ⊥ ∧ b' v = ⊥) ∨ (b v = ⊤ ∧ b' v = ⊤)) → Z1C loc (chRep ((Units.map f.toMonoidHom).comp χ)) b' = Submodule.span K ((fun y : (G → k) × (V → k) => (f ∘ y.1, f ∘ y.2)) '' (Z1C loc (chRep χ) b : Set ((G → k) × (V → k)))) ∧ Module.rank K (H1C loc (chRep ((Units.map f.toMonoidHom).comp χ)) b') = Module.rank k (H1C loc (chRep χ) b) := by
  intro k K G V _ _ f _ _ _ Gv _ _ loc χ b b' hbb
  letI : Algebra k K := f.toAlgebra
  let ρ' : Representation K G (TensorProduct k K k) :=
    { toFun := fun g => ((chRep χ) g).baseChange K
      map_one' := by
        show ((chRep χ) 1).baseChange K = 1
        rw [map_one]
        exact LinearMap.baseChange_one k k
      map_mul' := fun g g' => by
        show ((chRep χ) (g * g')).baseChange K = ((chRep χ) g).baseChange K * ((chRep χ) g').baseChange K
        rw [map_mul]
        exact LinearMap.baseChange_mul _ _ }
  obtain ⟨hZ, hH⟩ := n4 loc (chRep χ) b ρ' (fun g => rfl)
  let e := TensorProduct.AlgebraTensorModule.rid k K K
  have hρ : ∀ g x, (chRep ((Units.map f.toMonoidHom).comp χ)) g (e x) = e (ρ' g x) := by
    intro g x
    show (((Units.map f.toMonoidHom).comp χ) g : K) • e x = e (((chRep χ) g).baseChange K x)
    have hc : (chRep χ) g = ((χ g : kˣ) : k) • LinearMap.id := rfl
    rw [hc, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply,
      ← algebraMap_smul K ((χ g : kˣ) : k) x, map_smul]
    simp [RingHom.algebraMap_toAlgebra]
  have hb : ∀ v x, e x ∈ b' v ↔ x ∈ (b v).baseChange K := by
    intro v x
    rcases hbb v with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, Submodule.baseChange_bot, Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
    · rw [h1, h2, Submodule.baseChange_top]
      simp
  have hM := trMap loc e ρ' (chRep ((Units.map f.toMonoidHom).comp χ)) (fun v => (b v).baseChange K) b' hρ hb
  refine ⟨?_, ?_⟩
  · rw [← hM, hZ, Submodule.map_span, ← Set.image_comp]
    congr 2
    funext y
    refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
    · show e (1 ⊗ₜ[k] y.1 g) = f (y.1 g)
      simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    · show e (1 ⊗ₜ[k] y.2 v) = f (y.2 v)
      simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  · rw [trH loc e ρ' (chRep ((Units.map f.toMonoidHom).comp χ)) _ b' hρ hb, hH]
end

