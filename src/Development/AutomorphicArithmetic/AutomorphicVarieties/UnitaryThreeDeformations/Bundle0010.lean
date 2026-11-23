module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CardGlobalEulerCharacteristicRationals
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

theorem UpperTheory.card_global_euler_characteristic_rationals :
    GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (ρ : Representation (ZMod (l ^ 1)) (Gam Ω S) M),
            ContainsAbove S l → ContAction ρ → ∀ σ : Formalism.ConjugateSelfDual.G ℚ Ω, IsCC σ →
            Nat.card (H1 ρ) * Nat.card {m : M // ρ (toGS Ω _ σ) m = m} = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M := by
  intro hG Ω _ _ _ l _ _ M _ _ _ _ _ S ρ hS hρ σ hσ
  have h := hG ℚ Ω l 1 M S ρ Nat.one_pos hS hρ (fun _ => σ) (by
    intro w _
    obtain ⟨j, hj⟩ := hσ
    exact ⟨j, hj, Subsingleton.elim _ _⟩)
  have hc : NumberField.InfinitePlace.nrComplexPlaces ℚ = 0 :=
    NumberField.InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ)
  simp only [archH0Card, hc, pow_zero, mul_one, Module.finrank_self, pow_one] at h
  rw [Finset.prod_eq_single_of_mem Rat.infinitePlace
    (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Rat.isReal_infinitePlace)
    (fun b _ hb => absurd (Subsingleton.elim b _) hb)] at h
  exact h.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FinrankGradedPieceAndComplexConjugationInvariant
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private noncomputable def gbEquiv (k : Type) [Field k] (j : ℤ) :
    Gb (k := k) j ≃ₗ[k] ({p : Fin 3 × Fin 3 // wt p.1 p.2 = j} → k) where
  toFun X p := X.val p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := (⟨Matrix.of fun a b => if h : wt a b = j then f ⟨(a, b), h⟩ else 0,
    fun a b h => by simp [h]⟩ : gw (R := k) j)
  left_inv X := by
    apply Subtype.ext
    ext a b
    show (if h : wt a b = j then X.val a b else 0) = X.val a b
    split_ifs with h
    · rfl
    · exact (X.2 a b h).symm
  right_inv f := by
    ext ⟨⟨a, b⟩, h⟩
    show (if h : wt a b = j then f ⟨(a, b), h⟩ else 0) = _
    rw [dite_eq_left h]

private theorem card_wt (j : ℤ) : Fintype.card {p : Fin 3 × Fin 3 // wt p.1 p.2 = j} = (3 - |j|).toNat := by
  rcases (show j ≤ -3 ∨ j = -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega)
    with h | rfl | rfl | rfl | rfl | rfl | h
  · rw [show (3 - |j|).toNat = 0 by rw [abs_of_neg (by omega)]; omega]
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨⟨a, b⟩, hp⟩ => ?_⟩
    simp only [wt, wt1] at hp
    have := a.isLt
    have := b.isLt
    omega
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [show (3 - |j|).toNat = 0 by rw [abs_of_pos (by omega)]; omega]
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨⟨a, b⟩, hp⟩ => ?_⟩
    simp only [wt, wt1] at hp
    have := a.isLt
    have := b.isLt
    omega

private theorem mem_ker_iff {k D : Type} [Field k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (c : D)
    (hη : η c = -1) (hΨ : Ψ c = 1) (j : ℤ) (X : Gb (k := k) j) :
    X ∈ LinearMap.ker (gRep η Ψ j c - LinearMap.id) ↔ ∀ a b, X.val a b = -X.val b.rev a.rev := by
  have hne : η c ≠ 1 := by rw [hη]; decide
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h a b
    have h1 := congrArg (fun Y : Gb (k := k) j => Y.val a b) h
    simp only [gRep_val, adRep_baseLift_apply, hΨ, _root_.one_zpow, Units.val_one, one_mul, if_neg hne] at h1
    exact h1.symm
  · intro h
    apply Subtype.ext
    ext a b
    show ((gRep η Ψ j c) X).val a b = X.val a b
    rw [gRep_val, adRep_baseLift_apply, hΨ, _root_.one_zpow, Units.val_one, one_mul, if_neg hne]
    exact (h a b).symm

private theorem ker_one {k : Type} [Field k] (j : ℤ) (K : Submodule k (Gb (k := k) j))
    (hK : ∀ X, X ∈ K ↔ ∀ a b, X.val a b = -X.val b.rev a.rev) (M : Matrix (Fin 3) (Fin 3) k)
    (hM : M ∈ gw (R := k) j) (hM' : ∀ a b, M a b = -M b.rev a.rev) (a₀ b₀ : Fin 3) (h1 : M a₀ b₀ = 1)
    (hall : ∀ X : Matrix (Fin 3) (Fin 3) k, X ∈ gw (R := k) j → (∀ a b, X a b = -X b.rev a.rev) →
      ∀ a b, X a₀ b₀ * M a b = X a b) : finrank k K = 1 := by
  rw [finrank_eq_one_iff']
  refine ⟨⟨(⟨M, hM⟩ : gw (R := k) j), (hK _).2 hM'⟩, ?_, ?_⟩
  · intro h
    have : M a₀ b₀ = 0 := congrArg (fun Y : K => Y.1.val a₀ b₀) h
    rw [h1] at this
    exact one_ne_zero this
  · intro w
    refine ⟨w.1.val a₀ b₀, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    exact hall w.1.val w.1.2 ((hK _).1 w.2) a b

private theorem half {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {x : k} (h : x = -x) : x = 0 := by
  have h' : (2 : k) * x = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact absurd h'' h2
  · exact h''

theorem UpperTheory.finrank_gradedPiece_and_complexConjugation_invariants :
    ∀ {k D : Type} [Field k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (c : D), (2 : k) ≠ 0 → η c = -1 → Ψ c = 1 → ∀ j : ℤ,
        Module.Finite k (Gb (k := k) j) ∧ finrank k (Gb (k := k) j) = (3 - |j|).toNat ∧
          finrank k (LinearMap.ker (gRep η Ψ j c - LinearMap.id)) = if |j| ≤ 1 then 1 else 0 := by
  intro k D _ _ η Ψ c h2 hη hΨ j
  classical
  have e := gbEquiv k j
  haveI : Module.Finite k (Gb (k := k) j) := Module.Finite.equiv e.symm
  have hdim : finrank k (Gb (k := k) j) = (3 - |j|).toNat := by
    rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, card_wt]
  refine ⟨inferInstance, hdim, ?_⟩
  have hK := mem_ker_iff η Ψ c hη hΨ j
  have zero_case : (∀ X : Gb (k := k) j, (∀ a b, X.val a b = -X.val b.rev a.rev) → X = 0) →
      finrank k (LinearMap.ker (gRep η Ψ j c - LinearMap.id)) = 0 := by
    intro hz
    rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro X hX
    exact hz X ((hK X).1 hX)
  rcases (show j ≤ -3 ∨ j = -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega)
    with h | rfl | rfl | rfl | rfl | rfl | h
  · rw [if_neg (by rw [abs_le]; omega)]
    apply zero_case
    intro X hA
    have hZ : ∀ a b, wt a b ≠ j → X.val a b = 0 := X.2
    apply Subtype.ext
    ext a b
    show X.val a b = 0
    apply hZ
    simp only [wt, wt1]
    have := a.isLt
    have := b.isLt
    omega
  · rw [if_neg (by norm_num)]
    apply zero_case
    intro X hA
    have hZ : ∀ a b, wt a b ≠ -2 → X.val a b = 0 := X.2
    apply Subtype.ext
    ext a b
    show X.val a b = 0
    fin_cases a <;> fin_cases b <;> first
      | exact hZ _ _ (by decide)
      | exact half h2 (hA _ _)
  · rw [if_pos (by norm_num)]
    refine ker_one _ _ hK (!![0, 0, 0; 1, 0, 0; 0, -1, 0]) ?_ ?_ 1 0 (by simp) ?_
    · show ∀ a b, wt a b ≠ -1 → _ = 0
      intro a b hab
      fin_cases a <;> fin_cases b <;> first
        | exact absurd (by decide) hab
        | simp
    · intro a b
      fin_cases a <;> fin_cases b <;> simp [Fin.rev]
    · intro X hX hXa a b
      have hZ : ∀ a b, wt a b ≠ -1 → X a b = 0 := hX
      fin_cases a <;> fin_cases b <;> simp <;> first
        | exact (hZ _ _ (by decide)).symm
        | exact (half h2 (hXa 1 1)).symm
        | exact (hXa 2 1).symm
        | exact (hXa 2 2).symm
        | exact (hXa 1 2).symm
  · rw [if_pos (by norm_num)]
    refine ker_one _ _ hK (!![1, 0, 0; 0, 0, 0; 0, 0, -1]) ?_ ?_ 0 0 (by simp) ?_
    · show ∀ a b, wt a b ≠ 0 → _ = 0
      intro a b hab
      fin_cases a <;> fin_cases b <;> first
        | exact absurd (by decide) hab
        | simp
    · intro a b
      fin_cases a <;> fin_cases b <;> simp [Fin.rev]
    · intro X hX hXa a b
      have hZ : ∀ a b, wt a b ≠ 0 → X a b = 0 := hX
      fin_cases a <;> fin_cases b <;> simp <;> first
        | exact (hZ _ _ (by decide)).symm
        | exact (half h2 (hXa 1 1)).symm
        | exact (hXa 2 1).symm
        | exact (hXa 2 2).symm
        | exact (hXa 1 2).symm
  · rw [if_pos (by norm_num)]
    refine ker_one _ _ hK (!![0, 1, 0; 0, 0, -1; 0, 0, 0]) ?_ ?_ 0 1 (by simp) ?_
    · show ∀ a b, wt a b ≠ 1 → _ = 0
      intro a b hab
      fin_cases a <;> fin_cases b <;> first
        | exact absurd (by decide) hab
        | simp
    · intro a b
      fin_cases a <;> fin_cases b <;> simp [Fin.rev]
    · intro X hX hXa a b
      have hZ : ∀ a b, wt a b ≠ 1 → X a b = 0 := hX
      fin_cases a <;> fin_cases b <;> simp <;> first
        | exact (hZ _ _ (by decide)).symm
        | exact (half h2 (hXa 1 1)).symm
        | exact (hXa 2 1).symm
        | exact (hXa 2 2).symm
        | exact (hXa 1 2).symm
  · rw [if_neg (by norm_num)]
    apply zero_case
    intro X hA
    have hZ : ∀ a b, wt a b ≠ 2 → X.val a b = 0 := X.2
    apply Subtype.ext
    ext a b
    show X.val a b = 0
    fin_cases a <;> fin_cases b <;> first
      | exact hZ _ _ (by decide)
      | exact half h2 (hA _ _)
  · rw [if_neg (by rw [abs_le]; omega)]
    apply zero_case
    intro X hA
    have hZ : ∀ a b, wt a b ≠ j → X.val a b = 0 := X.2
    apply Subtype.ext
    ext a b
    show X.val a b = 0
    apply hZ
    simp only [wt, wt1]
    have := a.isLt
    have := b.isLt
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FinrankUnramifiedCocyclesEqFinrankInvariants
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private def affPairs (N : Type) [AddCommGroup N] : Subgroup (Equiv.Perm N × Equiv.Perm N) where
  carrier := {p | ∀ x y, p.2 (x + y) = p.1 x + p.2 y}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {a b} ha hb x y => by
    show a.2 (b.2 (x + y)) = a.1 (b.1 x) + a.2 (b.2 y)
    rw [hb, ha]
  inv_mem' := fun {a} ha x y => by
    show a.2.symm (x + y) = a.1.symm x + a.2.symm y
    apply a.2.injective
    rw [ha]
    simp

private theorem zhat_lift :
    ∀ {D E E' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group E] [Finite E] [Group E'] (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
      (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
      ∀ (q : E →* E') (w' : D →* E') (e : E), IsLocallyConstant w' → (∀ s ∈ I, w' s = 1) → q e = w' φ →
      ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ q.comp w = w' ∧ w φ = e ∧ ∀ g, w g ∈ Subgroup.zpowers e := by
  intro D E E' _ _ _ _ _ _ I φ hcl hd q w' e hw' hI hq
  have hn : 0 < orderOf e := orderOf_pos e
  haveI : NeZero (orderOf e) := ⟨hn.ne'⟩
  obtain ⟨d, hdl, hdI, hdφ⟩ := hd (orderOf e) hn
  let f : Multiplicative (ZMod (orderOf e)) →* E :=
    MonoidHom.mk' (fun x => e ^ (Multiplicative.toAdd x).val) (by
      intro a b
      simp only [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add])
  have hf1 : f (Multiplicative.ofAdd 1) = e := by
    show e ^ (1 : ZMod (orderOf e)).val = e
    rw [ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  have hwl : IsLocallyConstant (f.comp d) := hdl.comp f
  have hwI : ∀ s ∈ I, (f.comp d) s = 1 := by
    intro s hs
    simp [hdI s hs]
  refine ⟨f.comp d, hwl, hwI, ?_, ?_, ?_⟩
  · have h1 : IsLocallyConstant (q.comp (f.comp d)) := hwl.comp q
    have h2 := (h1.prodMk hw').comp (fun p : E' × E' => p.1 = p.2)
    have hclosed : IsClosed (((q.comp (f.comp d)).eqLocus w' : Subgroup D) : Set D) := by
      have := h2.isClosed_fiber True
      convert this using 1
      ext x
      simp [MonoidHom.eqLocus]
      rfl
    have hle : I ⊔ Subgroup.zpowers φ ≤ (q.comp (f.comp d)).eqLocus w' := by
      refine sup_le ?_ ?_
      · intro s hs
        show q ((f.comp d) s) = w' s
        rw [hwI s hs, hI s hs, map_one]
      · rw [Subgroup.zpowers_le]
        show q (f (d φ)) = w' φ
        rw [hdφ, hf1, hq]
    have := Subgroup.topologicalClosure_minimal _ hle hclosed
    rw [hcl] at this
    ext x
    exact this (Subgroup.mem_top x)
  · show f (d φ) = e
    rw [hdφ, hf1]
  · intro g
    exact Subgroup.npow_mem_zpowers e _

theorem UpperTheory.finrank_unramified_cocycles_eq_finrank_invariants :
    ∀ {k D M : Type} [Field k] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k D M) (I : Subgroup D) (W : Submodule k (D → M)), ContAction ρ → I.Normal → (∃ φ : D, (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧ ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
        (∀ y, y ∈ W ↔ y ∈ Z1 ρ ∧ ∀ s ∈ I, y s = 0) → finrank k W = finrank k (H0 (ρ.comp I.subtype : Representation k I M)) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ I W hρ hI ⟨φ, hcl, hd⟩ hW
  set N : Submodule k M := H0 (ρ.comp I.subtype : Representation k I M) with hNdef
  have hN : ∀ m, m ∈ N ↔ ∀ s ∈ I, ρ s m = m := fun m =>
    ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s.1 s.2⟩
  have hev : ∀ y ∈ W, y φ ∈ N := by
    intro y hy
    obtain ⟨⟨-, hc⟩, h0⟩ := (hW y).1 hy
    rw [hN]
    intro s hs
    have h1 := hc s φ
    have h2 := hc φ (φ⁻¹ * s * φ)
    rw [h0 _ (hI.conj_mem' s hs φ), map_zero, add_zero] at h2
    rw [h0 s hs, zero_add] at h1
    rw [← h1, ← h2]
    congr 1
    group
  let ev : W →ₗ[k] N := ((LinearMap.proj φ).comp W.subtype).codRestrict N (fun y => hev y.1 y.2)
  have hinj : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have hyφ : y.1 φ = 0 := congrArg Subtype.val hy
    obtain ⟨⟨hcont, hc⟩, h0⟩ := (hW y.1).1 y.2
    have h1 : y.1 1 = 0 := h0 1 I.one_mem
    let Z : Subgroup D :=
      { carrier := {g | y.1 g = 0}
        one_mem' := h1
        mul_mem' := fun {a b} ha hb => by
          show y.1 (a * b) = 0
          rw [hc, show y.1 a = 0 from ha, show y.1 b = 0 from hb, map_zero, add_zero]
        inv_mem' := fun {a} ha => by
          have := hc a⁻¹ a
          rw [inv_mul_cancel, h1, show y.1 a = 0 from ha, map_zero, add_zero] at this
          exact this.symm }
    have hZ : IsClosed (Z : Set D) := isClosed_eq hcont continuous_const
    have hle : I ⊔ Subgroup.zpowers φ ≤ Z := sup_le h0 (by rw [Subgroup.zpowers_le]; exact hyφ)
    have := Subgroup.topologicalClosure_minimal _ hle hZ
    rw [hcl] at this
    ext g
    exact this (Subgroup.mem_top g)
  have hst : ∀ g : D, ∀ m : N, ρ g m ∈ N := by
    intro g m
    rw [hN]
    intro s hs
    have h := (hN m).1 m.2 _ (hI.conj_mem' s hs g)
    calc ρ s (ρ g m) = ρ g (ρ (g⁻¹ * s * g) m) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
          congr 2
          group
      _ = ρ g m := by rw [h]
  let a0 : D →* Function.End N :=
    { toFun := fun g m => ⟨ρ g m, hst g m⟩
      map_one' := by
        funext m
        apply Subtype.ext
        show ρ 1 m = m
        simp
      map_mul' := fun g h => by
        funext m
        apply Subtype.ext
        show ρ (g * h) m = ρ g (ρ h m)
        simp }
  let a : D →* Equiv.Perm N := a0.toHomPerm
  have ha : ∀ g m, (a g m : M) = ρ g m := fun _ _ => rfl
  have hal : IsLocallyConstant a := by
    refine IsLocallyConstant.desc a (fun (p : Equiv.Perm N) (m : N) => (p m : M)) ?_ ?_
    · rw [IsLocallyConstant.iff_continuous]
      exact continuous_pi fun m => hρ.comp (continuous_id.prodMk continuous_const)
    · intro p q h
      ext m
      exact congrFun h m
  have haI : ∀ s ∈ I, a s = 1 := by
    intro s hs
    ext m
    exact (hN m).1 m.2 s hs
  have hsurj : Function.Surjective ev := by
    intro m
    obtain ⟨w, hwl, hwI, hq, hwφ, hw⟩ := zhat_lift I φ hcl hd (MonoidHom.fst _ (Equiv.Perm N)) a
      (a φ, Equiv.addRight m * a φ) hal haI rfl
    have hP : ∀ g, w g ∈ affPairs N := by
      intro g
      refine (Subgroup.zpowers_le.2 ?_ : _ ≤ affPairs N) (hw g)
      intro x y
      apply Subtype.ext
      show ρ φ (x + y : M) + m = ρ φ x + (ρ φ y + m)
      rw [map_add (f := _), add_assoc]
    have hw1 : ∀ g, (w g).1 = a g := fun g => DFunLike.congr_fun hq g
    refine ⟨⟨fun g => ((w g).2 0 : M), (hW _).2 ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩
    · exact (hwl.comp (fun p : Equiv.Perm N × Equiv.Perm N => (p.2 0 : M))).continuous
    · intro g h
      have := hP g ((w h).2 0) 0
      rw [add_zero, hw1] at this
      show (((w (g * h)).2 0 : N) : M) = (w g).2 0 + ρ g ((w h).2 0)
      rw [map_mul, Prod.snd_mul, Equiv.Perm.mul_apply, this, Submodule.coe_add, ha, add_comm]
    · intro s hs
      show (((w s).2 0 : N) : M) = 0
      rw [hwI s hs]
      rfl
    · apply Subtype.ext
      show (((w φ).2 0 : N) : M) = m
      rw [hwφ]
      show ρ φ 0 + m = m
      simp
  exact (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).finrank_eq
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GlobalCohomologyFiniteSet
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private theorem twDual_inv_eq_zero {Γ k M : Type} [Group Γ] [Field k] [AddCommGroup M] [Module k M]
    (N : ℕ) [Module (ZMod N) M] (μ : Γ →* (ZMod N)ˣ) (ρ : Representation k Γ M)
    (g : Γ) (a : k) (n : ℕ) (hg : ∀ m, ρ g m = a • m) (hn : (n : ZMod N) = μ g) (han : a ≠ (n : k))
    (y : H0 (twDual μ (GlobalTheory.Published.zmodRep N ρ))) : y = 0 := by
  obtain ⟨φ, hφ⟩ := y
  apply Subtype.ext
  have h1 : twDual μ (GlobalTheory.Published.zmodRep N ρ) g φ = φ := hφ _
  show φ = 0
  apply LinearMap.ext
  intro x
  set m : M := (a - (n : k))⁻¹ • x with hm
  have hx : x = a • m - n • m := by
    rw [← Nat.cast_smul_eq_nsmul k, ← sub_smul, hm, smul_smul,
      mul_inv_cancel₀ (sub_ne_zero.2 han), one_smul]
  have h3 := congrArg (fun ψ : TDual (ZMod N) M => ψ (GlobalTheory.Published.zmodRep N ρ g m)) h1
  simp only [twDual_apply] at h3
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    ← hn] at h3
  have h4 : GlobalTheory.Published.zmodRep N ρ g m = a • m := hg m
  rw [h4] at h3
  show φ x = 0
  rw [hx]
  refine (LinearMap.map_sub (φ : Module.Dual (ZMod N) M) _ _).trans (sub_eq_zero.mpr ?_)
  refine h3.symm.trans ?_
  rw [← nsmul_eq_mul]
  exact (map_nsmul (F := Module.Dual (ZMod N) M) φ n m).symm

theorem UpperTheory.global_cohomology_finite_set :
    GlobalTheory.Published.PoitouTateNormalised → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset Pl) (A : S → ValuationSubring Ω) (ρ : Representation k (Gam Ω S) M),
                 ContainsAbove S l → (∀ v, Formalism.ConjugateSelfDual.IsPlaceOver (A v) v.1) → ContAction ρ →
                 (∃ (σ : Formalism.ConjugateSelfDual.G ℚ Ω) (a : k) (n : ℕ), (∀ m, ρ (toGS Ω _ σ) m = a • m) ∧ (n : ZMod (l ^ 1)) = (cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) ∧ a ≠ (n : k)) →
                 ∀ κ : ∀ v : S, Z2 (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v)).subtype) : Representation k (Dec (F := ℚ) (A v)) M), ∃ z : Z2 ρ, ∀ v : S,
                   (fun p : Dec (F := ℚ) (A v) × Dec (F := ℚ) (A v) => z.1 (toGS Ω _ p.1.1, toGS Ω _ p.2.1)) - (κ v).1 ∈
                     B2 (ρ.comp ((toGS Ω _).comp (Dec (F := ℚ) (A v)).subtype) : Representation k (Dec (F := ℚ) (A v)) M) := by
  intro hPT Ω _ _ _ l _ hl k M _ _ _ _ _ _ _ _ S A ρ hS hA hρ hσ κ
  obtain ⟨σ, a, n, hσa, hn, han⟩ := hσ
  have hM : ∀ m : M, (l ^ 1) • m = 0 := fun m => by
    rw [pow_one, ← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero, zero_smul]
  letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ 1)
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := 1) hS
  obtain ⟨inv, -, h⟩ := hPT ℚ Ω l 1 (Or.inl hl) Nat.one_pos ζ hζ
  have hex := (h S hS A hA μ hμ M (GlobalTheory.Published.zmodRep (l ^ 1) ρ) hρ).1
  have hμσ : μ (toGS Ω _ σ) = cycMod ℚ Ω l 1 σ := DFunLike.congr_fun hμ σ
  obtain ⟨z, hz⟩ := (hex.mem_range_localization_H2_iff
    (fun v => Submodule.Quotient.mk ⟨(κ v).1, (κ v).2⟩)).2 (fun y => by
      rw [twDual_inv_eq_zero (l ^ 1) μ ρ _ a n hσa (by rw [hμσ]; exact hn) han y]
      simp only [map_zero, Finset.sum_const_zero])
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    refine ⟨⟨z.1, z.2⟩, fun v => ?_⟩
    have e : (Submodule.Quotient.mk (restrictCocycles2 (GlobalTheory.Published.zmodRep (l ^ 1) ρ) (locFam S A v)
        (continuous_locFam S A v) z) : H2 ((GlobalTheory.Published.zmodRep (l ^ 1) ρ).comp (locFam S A v))) =
        Submodule.Quotient.mk ⟨(κ v).1, (κ v).2⟩ := congrFun hz v
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.eq _).1 e)
    exact (separated_dvr_second_cohomology_mem _ _).2 ⟨c, hc, hcf⟩
end

