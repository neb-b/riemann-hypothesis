module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesSiegelLevelStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesPolarizedFanLevelStructure
section
open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.UPoinc.CellCones

theorem cong_addHom {Y : Type} [AddCommGroup Y] {n N : ℕ} (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (g : Y →+ Y) {x y : Y}
    (h : ∀ i, ((eb x i : ℤ) : ZMod N) = (eb y i : ZMod N)) (i : Fin n) :
    ((eb (g x) i : ℤ) : ZMod N) = (eb (g y) i : ZMod N) := by
  have := GlobalTheory.Poinc.Cells.cong_map (eb.toLinearMap ∘ₗ g.toIntLinearMap ∘ₗ eb.symm.toLinearMap) h i
  simpa using this

theorem exists_transport {O : Type} [CommRing O] {Y : Type} [AddCommGroup Y] [Module O Y] {n N : ℕ} [NeZero N]
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y) (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (b : LinearMap.BilinForm ℤ Y) (e : Y ≃ₗ[O] Y)
    (hb : ∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) :
    ∃ μ' : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ' cl) i : ℤ) : ZMod N) = cl i) ∧
      (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) →
        pull e.toLinearMap b (μ' cl) (μ' cl) ≤ pull e.toLinearMap b α α) ∧
      ∀ cl, ∃ d, e (μ' cl) = μ d := by
  let lift : (Fin n → ZMod N) → Y := fun cl => eb.symm fun i => ((cl i).val : ℤ)
  have hlift : ∀ cl i, ((eb (lift cl) i : ℤ) : ZMod N) = cl i := fun cl i => by simp [lift]
  let d : (Fin n → ZMod N) → (Fin n → ZMod N) := fun cl i => ((eb (e (lift cl)) i : ℤ) : ZMod N)
  refine ⟨fun cl => e.symm (μ (d cl)), fun cl i => ?_, fun cl α hα => ?_, fun cl => ⟨d cl, by simp⟩⟩
  · have h1 : ∀ i, ((eb (μ (d cl)) i : ℤ) : ZMod N) = ((eb (e (lift cl)) i : ℤ) : ZMod N) := fun i => hμ _ _
    have h2 := cong_addHom eb e.symm.toLinearMap.toAddMonoidHom h1 i
    simp only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2
    rw [h2, hlift]
  · simp only [pull_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hb _ _ fun i => cong_addHom eb e.toLinearMap.toAddMonoidHom (fun i => by rw [hα, hlift]) i

theorem exists_nat_comb_of_infinite {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    {b' b₀ : LinearMap.BilinForm ℤ X} (hb' : b' ∈ balForms bar X) (hb₀ : b₀ ∈ balForms bar X)
    {s : Set ℕ} (hs : s.Infinite)
    (hk : ∀ n ∈ s, ∃ (k : ℕ) (cf : Fin m → ℕ), 0 < k ∧ k • (n • b' + b₀) = ∑ j, cf j • γ j) :
    ∃ cf : Fin m → ℕ, b' = ∑ j, cf j • γ j := by
  classical
  obtain ⟨t, bb, hbb⟩ := hγ.basis
  let B' : balForms bar X := ⟨b', hb'⟩
  let B₀ : balForms bar X := ⟨b₀, hb₀⟩
  have hc : ∀ n ∈ s, ∀ o, (∀ j, o ≠ Sum.inl j) → (n : ℤ) * bb.repr B' o + bb.repr B₀ o = 0 := by
    intro n hn o ho
    obtain ⟨k, cf, hk0, he⟩ := hk n hn
    have hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j) := Subtype.ext (by simpa [hbb, B', B₀] using he)
    have := congrArg (fun x => bb.repr x o) hE
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_nsmul, map_add (f := _), map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply,
      Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply, nsmul_eq_mul] at this
    rw [Finset.sum_eq_zero fun j _ => by rw [if_neg (ho j).symm]; simp] at this
    have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    push_cast at this
    exact (mul_eq_zero.1 this).resolve_left hk'
  have hp : ∀ n ∈ s, ∀ j, 0 ≤ (n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j) := by
    intro n hn j
    obtain ⟨k, cf, hk0, he⟩ := hk n hn
    have hE : k • (n • B' + B₀) = ∑ j, cf j • bb (Sum.inl j) := Subtype.ext (by simpa [hbb, B', B₀] using he)
    have := congrArg (fun x => bb.repr x (Sum.inl j)) hE
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_nsmul, map_add (f := _), map_sum, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.add_apply,
      Finset.sum_apply', Finsupp.smul_apply, Finsupp.single_apply, nsmul_eq_mul, Sum.inl.injEq] at this
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk0
    have h2 : (0 : ℤ) ≤ k * ((n : ℤ) * bb.repr B' (Sum.inl j) + bb.repr B₀ (Sum.inl j)) := by
      push_cast at this ⊢; rw [this]; positivity
    exact nonneg_of_mul_nonneg_right (by linarith) hk'
  let M : ℕ := ∑ o, (bb.repr B₀ o).natAbs
  obtain ⟨n₁, hn₁, h₁⟩ := hs.exists_gt M
  obtain ⟨n₂, hn₂, h₂⟩ := hs.exists_gt n₁
  have hM : ∀ o, (bb.repr B₀ o).natAbs ≤ M := fun o =>
    Finset.single_le_sum (f := fun o => (bb.repr B₀ o).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ o)
  have hR : ∀ o, (∀ j, o ≠ Sum.inl j) → bb.repr B' o = 0 := fun o ho => by
    have e1 := hc n₁ hn₁ o ho
    have e2 := hc n₂ hn₂ o ho
    have : ((n₂ : ℤ) - n₁) * bb.repr B' o = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by omega)
  have hL : ∀ j, 0 ≤ bb.repr B' (Sum.inl j) := fun j => by
    have e1 := hp n₁ hn₁ j
    have e2 := hM (Sum.inl j)
    by_contra hneg
    push_neg at hneg
    have : (bb.repr B₀ (Sum.inl j)) ≤ M := by omega
    have : (n₁ : ℤ) * bb.repr B' (Sum.inl j) ≤ - n₁ := by nlinarith
    omega
  refine ⟨fun j => (bb.repr B' (Sum.inl j)).toNat, ?_⟩
  have hsum := bb.sum_repr B'
  have h0 : ∑ a₂ : Fin t, bb.repr B' (Sum.inr a₂) • bb (Sum.inr a₂) = 0 :=
    Finset.sum_eq_zero fun o _ => by rw [hR (Sum.inr o) fun j => Sum.inr_ne_inl, zero_smul]
  rw [Fintype.sum_sum_type, h0, add_zero] at hsum
  have := congrArg Subtype.val hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, hbb] at this
  rw [show b' = (B' : LinearMap.BilinForm ℤ X) from rfl, ← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← natCast_zsmul, Int.toNat_of_nonneg (hL j)]

theorem exists_finite_cones : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) → ∃ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ Y), (∀ i, IsCone bar φ (γ i)) ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → ∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j := by
  intro O _ bar φ Y _ _ _ _ hF n N _ hN eb μ hμ b₀ hb₀ hb₀p hb₀m
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  let Mn : ((Fin n → ZMod N) → Y) → LinearMap.BilinForm ℤ Y → Prop :=
    fun μ b => ∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α
  let T : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) := {x | IsCone bar φ x.2 ∧
    (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) ∧ ∃ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin x.1 → ℕ),
      0 < k ∧ (∀ j, 0 < cf j) ∧ k • b = ∑ j, cf j • x.2 j ∧ Mn μ b}
  have hT : T.Finite := by
    obtain ⟨S, hS, hSe⟩ := hF.finite
    let TS : Set (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) := {x | (∀ j, x.2 j ∈ S) ∧
      Function.Injective x.2 ∧ IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)}
    have hTS : TS.Finite := (GlobalTheory.Poinc.Cells.finite_families _ S hS).subset fun x hx => ⟨hx.1, hx.2.1⟩
    have hfin := fun (x : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y)
      (h : IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y)) =>
        _root_.GlobalTheory.Poinc.MinSysLat.finite_minimiser_systems_lat Y n N eb x.1 x.2 (fun j => (h.1.mem j).1) h.1.nonneg h.2
    let Fμ : (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) → Set ((Fin n → ZMod N) → Y) := fun x =>
      if h : IsCone bar φ x.2 ∧ (∀ y, y ≠ 0 → 0 < ∑ j, x.2 j y y) then ((hfin x h).choose : Set _) else ∅
    let M := (⋃ x ∈ TS, Fμ x) ∩ {μ' | ∀ cl i, ((eb (μ' cl) i : ℤ) : ZMod N) = cl i}
    have hM : M.Finite := (hTS.biUnion fun x _ => by
      simp only [Fμ]; split_ifs
      · exact Finset.finite_toSet _
      · exact Set.finite_empty).inter_of_left _
    let V : Set Y := Set.range μ
    let E := ⋃ μ' ∈ M, {e : Y ≃ₗ[O] Y | ∀ cl, e (μ' cl) ∈ V}
    have hl : ∀ (e : Y ≃ₗ[O] Y) x,
        (eb.toLinearMap ∘ₗ e.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap) x = eb (e (eb.symm x)) :=
      fun e x => rfl
    have hE : E.Finite := hM.biUnion fun μ' hμ' => by
      let Φ : (Y ≃ₗ[O] Y) → (Fin n → ZMod N) → Y := fun e cl => e (μ' cl)
      refine Set.Finite.of_finite_image (f := Φ)
        ((Set.Finite.pi (t := fun _ => V) fun _ => Set.finite_range _).subset ?_) ?_
      · rintro _ ⟨e, he, rfl⟩ cl -
        exact he cl
      · intro e₁ _ e₂ _ h
        have key := GlobalTheory.Poinc.Cells.linearMap_eq_of_eq_on_residues N (by omega) n
          (eb.toLinearMap ∘ₗ e₁.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap)
          (eb.toLinearMap ∘ₗ e₂.toLinearMap.toAddMonoidHom.toIntLinearMap ∘ₗ eb.symm.toLinearMap)
          (Set.range fun cl => eb (μ' cl))
          (fun x => ⟨eb (μ' fun i => (x i : ZMod N)), ⟨_, rfl⟩, fun i => hμ'.2 _ _⟩) (by
            rintro _ ⟨cl, rfl⟩
            rw [hl, hl]
            simp only [LinearEquiv.symm_apply_apply]
            exact congrArg eb (congrFun h cl))
        refine LinearEquiv.ext fun y => eb.injective ?_
        have := LinearMap.congr_fun key (eb y)
        rw [hl, hl] at this
        simpa using this
    refine ((hTS.prod hE).image fun q => (⟨q.1.1, fun j => pull q.2.symm.toLinearMap (q.1.2 j)⟩ :
      Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y)).subset ?_
    rintro ⟨m, γ⟩ ⟨hγ, hγd, b, k, cf, hk, hcf, hkb, hbm⟩
    obtain ⟨e, he⟩ := hSe m γ hγ
    obtain ⟨μ', hμ'1, hμ'2, hμ'3⟩ := exists_transport eb μ hμ b e hbm
    have hc' := hγ.pull_equiv e
    have hd' : ∀ y, y ≠ 0 → 0 < ∑ j, pull e.toLinearMap (γ j) y y := fun y hy => by
      simpa using hγd (e y) (by simpa using hy)
    have hkb' : k • pull e.toLinearMap b = ∑ j, cf j • pull e.toLinearMap (γ j) := LinearMap.ext₂ fun x y => by
      simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hkb (e x) (e y)
    have hx' : (⟨m, fun j => pull e.toLinearMap (γ j)⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) ∈ TS :=
      ⟨he, hc'.injective, hc', hd'⟩
    refine ⟨⟨⟨m, fun j => pull e.toLinearMap (γ j)⟩, e⟩, ⟨hx', ?_⟩, ?_⟩
    · refine Set.mem_biUnion (x := μ') ⟨Set.mem_biUnion hx' ?_, hμ'1⟩ fun cl => ?_
      · show μ' ∈ Fμ ⟨m, fun j => pull e.toLinearMap (γ j)⟩
        simp only [Fμ]
        rw [dite_eq_left (show IsCone bar φ (fun j => pull e.toLinearMap (γ j)) ∧ _ from ⟨hc', hd'⟩)]
        exact (hfin ⟨m, fun j => pull e.toLinearMap (γ j)⟩ ⟨hc', hd'⟩).choose_spec (pull e.toLinearMap b) k cf hk hcf
          hkb' μ' hμ'1 hμ'2
      · obtain ⟨d, hd⟩ := hμ'3 cl
        exact ⟨d, hd.symm⟩
    · simp
  obtain ⟨L, hL⟩ : ∃ L : List (Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y), ∀ x, x ∈ L ↔ x ∈ T :=
    ⟨hT.toFinset.toList, fun x => by simp⟩
  refine ⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, fun i => ((hL _).1 (List.get_mem L i)).1, ?_⟩
  intro b' hb' hb'p hb'm
  have key : ∀ n' : ℕ, ∃ i : Fin L.length, ∃ (k : ℕ) (cf : Fin (L.get i).1 → ℕ), 0 < k ∧
      k • (n' • b' + b₀) = ∑ j, cf j • (L.get i).2 j := by
    intro n'
    have hβs : n' • b' + b₀ ∈ balForms bar Y := add_mem (nsmul_mem hb' _) hb₀
    have hβp : ∀ x, x ≠ 0 → 0 < (n' • b' + b₀) x x := fun x hx => by
      have h1 := hb'p x
      have h2 := hb₀p x hx
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      positivity
    have hβm : Mn μ (n' • b' + b₀) := fun cl α hα => by
      have h1 := hb'm cl α hα
      have h2 := hb₀m cl α hα
      have h3 : (n' : ℤ) * b' (μ cl) (μ cl) ≤ n' * b' α α := mul_le_mul_of_nonneg_left h1 (by positivity)
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
      linarith
    obtain ⟨m, γ, k, cf, hγ, hk, hcf, hkβ⟩ := GlobalTheory.Poinc.Cover.exists_cone O bar φ Y hF _ hβs hβp
    have hγd : ∀ y, y ≠ 0 → 0 < ∑ j, γ j y y := fun y hy => by
      by_contra hcon
      push_neg at hcon
      have h0 : ∀ j, γ j y y = 0 := fun j => le_antisymm ((Finset.single_le_sum (fun j _ => hγ.nonneg j y)
        (Finset.mem_univ j)).trans hcon) (hγ.nonneg j y)
      have h1 := LinearMap.congr_fun₂ hkβ y y
      have h2 := hβp y hy
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, h0, smul_zero, Finset.sum_const_zero, nsmul_eq_mul] at h1
      have : (k : ℤ) * (n' • b' + b₀) y y > 0 := mul_pos (by exact_mod_cast hk) h2
      simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at this h1
      linarith
    have hmem : (⟨m, γ⟩ : Σ m : ℕ, Fin m → LinearMap.BilinForm ℤ Y) ∈ T :=
      ⟨hγ, hγd, _, k, cf, hk, hcf, hkβ, hβm⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 ((hL _).2 hmem)
    refine ⟨i, ?_⟩
    rw [hi]
    exact ⟨k, cf, hk, hkβ⟩
  choose f hf using key
  obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber f
  obtain ⟨cf, hcf⟩ := exists_nat_comb_of_infinite ((hL _).1 (List.get_mem L i)).1 hb' hb₀ (s := f ⁻¹' {i})
    (Set.infinite_coe_iff.1 hi) fun n' hn' => by
      have := hf n'
      rw [show f n' = i from hn'] at this
      exact this
  exact ⟨i, 1, cf, one_pos, by rw [one_smul]; exact hcf⟩

end GlobalTheory.UPoinc.CellCones
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleDeeperLevelSiegelCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

theorem locEq : ∀ (X : Scheme.{0}) (N : ℕ) (c₀ u : Γ(X, ⊤)ˣ), IsUnit (N : Γ(X, ⊤)) → c₀ ^ N = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X), Units.map g.appTop.hom.toMonoidHom u ^ N = 1) → GlobalTheory.HkClopen.Loc (S := X) (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ X) => Units.map g.appTop.hom.toMonoidHom c₀ = Units.map g.appTop.hom.toMonoidHom u) := GlobalTheory.T.isClopen_geometricPoints_rootOfUnity_eq_unit

theorem pairValue : ∀ (h n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ s) (N : ℕ) (T : Over S) (x y : T ⟶ c.A), Out.RelAmple c.A c.diag → 0 < N → IsUnit (N : Γ(T.left, ⊤)) → x ^ N = 1 → y ^ N = 1 → ∃ c₀ : Γ(T.left, ⊤)ˣ, c₀ ^ N = 1 ∧ Out.WeilIs c.A c.diag N x y c₀ := GlobalTheory.DiagPairing.exists_weilIs_diag_root

theorem geomLift : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := _root_.GlobalTheory.SiegGeomLift.exists_geom_level

theorem geomBij : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := _root_.GlobalTheory.GeomBasis.basis_of_weil

theorem buildCover : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (S V : Scheme.{0}) (s : S ⟶ Sp B) (sV : V ⟶ Sp B') (π : V ⟶ S) (c : SiegPre h n ζ s) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk π ⟶ c.A)), (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a, e a ^ d = toUnit (Over.mk π) ≫ c.lev a) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V) (β : B' →+* k) (z : kˣ), x ≫ sV = spMap β → (z : k) = β ζ' → (∀ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk (x ≫ π) ⟶ c.A, g ^ N = 1 → ∃ a, (Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a) ((Over.homMk x rfl : Over.mk (x ≫ π) ⟶ Over.mk π) ≫ e a') (unitOn (z ^ (2 * omegaStd a a')))) → ∃ (C : SiegPre h N ζ' sV) (φ : C.A.left ⟶ c.A.left), SRelBy C c d 1 π φ ∧ (∀ a, (C.lev a).left ≫ φ = (e a).left) ∧ ∀ (T : Scheme.{0}) (t : T ⟶ V) (B'' : Type) [CommRing B''] (ζ'' : B'') (sT : T ⟶ Sp B'') (C' : SiegPre h N ζ'' sT), SiegPB C' C t ↔ ∃ φ' : C'.A.left ⟶ c.A.left, SRelBy C' c d 1 (t ≫ π) φ' ∧ ∀ a, (C'.lev a).left ≫ φ' = t ≫ (e a).left := _root_.GlobalTheory.siegCover_build


open GlobalTheory.LevCover in
theorem exists_levelCover : ∀ (h n N : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (b : TBase B' N) (j : B →+* B') (S : Scheme.{0}) (s' : S ⟶ Sp B') (c : SiegPre h n ζ (s' ≫ spMap j)), 3 ≤ n → Odd N → n ∣ N → j ζ = (b.ζ : B') ^ (N / n) → c.Principal → ∃ (S₁ : Scheme.{0}) (π : S₁ ⟶ S) (C : SiegPre h N (b.ζ : B') (π ≫ s')), IsFinite π ∧ Etale π ∧ Surjective π ∧ SRel C c (N / n) 1 π ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')), SRel C' c (N / n) 1 t → ∃! t₁ : T ⟶ S₁, t₁ ≫ π = t ∧ SiegPB C' C t₁ := by
  intro h n N B B' _ _ ζ b j S s' c hn hN hnN hζ hc
  have hNpos : 0 < N := hN.pos
  have hnodd : Odd n := hN.of_dvd_nat hnN
  have hNn : N / n * n = N := Nat.div_mul_cancel hnN
  let b₀ : TBase B' n :=
    { ζ := b.ζ ^ (N / n)
      unit := by
        have := b.unit
        rw [← hNn, Nat.cast_mul] at this
        exact isUnit_of_mul_isUnit_right this
      prim := fun K _ β => by
        rw [Units.val_pow_eq_pow_val, map_pow]
        exact (b.prim K β).pow hNpos hNn.symm }
  have hb₀ : (b₀.ζ : B') = (b.ζ : B') ^ (N / n) := Units.val_pow_eq_pow_val _ _
  have hj : j ζ = (b₀.ζ : B') := hζ.trans hb₀.symm
  have RC := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n B B' ζ (b₀.ζ : B') j S S (s' ≫ spMap j) s' (𝟙 S) hj
    (Category.id_comp _)
  obtain ⟨c₀, hpb⟩ := RC.1 c
  have hc₀ : c₀.Principal := RC.2.1 c c₀ hpb hc
  have hrel : ∀ (T : Scheme.{0}) (t : T ⟶ S) (C' : SiegPre h N (b.ζ : B') (t ≫ s')),
      SRel C' c₀ (N / n) 1 t ↔ SRel C' c (N / n) 1 t := fun T t C' => by
    have := (_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n N B B' B' ζ (b₀.ζ : B') (b.ζ : B') S S T (s' ≫ spMap j) s' (t ≫ s') c c₀ C'
      (𝟙 S) t 1 1 (N / n) ((sRel_one_one_iff c₀ c (𝟙 S)).2 hpb)).1
    rwa [Category.comp_id] at this
  have hNS : IsUnit (N : Γ(S, ⊤)) := by
    have := b.unit.map (fnOn s')
    rwa [map_natCast] at this
  obtain ⟨Z, et, hfin, het, hadd, hpow, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom S c₀.A N (Fin h ⊕ Fin h → ℤ) c₀.ab hNS
  have R : RepTors c₀.A N _ Z et := ⟨hfin, het, hadd, hpow, huniv⟩
  haveI := hfin
  haveI := het
  have hNZ : IsUnit (N : Γ(Z.left, ⊤)) := by
    have := hNS.map Z.hom.appTop.hom
    rwa [map_natCast] at this
  have hlevN : ∀ a, c₀.lev a ^ N = 1 := fun a => by
    rw [← hNn, mul_comm, pow_mul, c₀.lev_tors, one_pow]
  obtain ⟨Ul, hUl, HUl⟩ := R.clopenCond (fun a => et a ^ (N / n)) (fun a => toUnit Z ≫ c₀.lev a)
    (fun a a' => by rw [hadd, mul_pow]) (fun a => by rw [← pow_mul, mul_comm, pow_mul, hpow, one_pow])
    (fun a a' => by rw [c₀.lev_add, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, hlevN, MonObj.comp_one])
  have hG := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hLB : c₀.diag.IsLB := pull_isLB c₀.isLB _
  let P2 : (Fin h ⊕ Fin h → ℤ) → (Fin h ⊕ Fin h → ℤ) → HkClopen.GeoCond Z.left := fun a a' k _ _ g =>
    ∀ β : B' →+* k, g ≫ Z.hom ≫ s' = spMap β →
      Out.WeilIs c₀.A c₀.diag N ((Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) ≫ et a)
        ((Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) ≫ et a')
        (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a')))
  have hzN : ∀ (k : Type) [Field k] (β : B' →+* k), Units.map β.toMonoidHom b.ζ ^ N = 1 := fun k _ β =>
    Units.ext (by simpa using (b.prim k β).pow_eq_one)
  have locPair : ∀ a a', HkClopen.Loc (P2 a a') := fun a a' => by
    obtain ⟨v, hv, hW⟩ := pairValue h n B' _ S s' c₀ N Z (et a) (et a') hc₀.1 hNpos hNZ (hpow a) (hpow a')
    refine (locEq Z.left N v (Units.map (fnOn (Z.hom ≫ s')).toMonoidHom (b.ζ ^ (2 * omegaStd a a'))) hNZ hv
      fun k _ _ g => ?_).congr fun k _ _ g => ?_
    · obtain ⟨β, hβ⟩ := exists_spMap (g ≫ Z.hom ≫ s')
      rw [map_fnOn _ g β hβ, ← unitOn_pow', map_zpow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hzN, one_zpow]
      exact unitOn_one'
    · have hW' := CommPairing.weilIs_pull hG c₀.ab hLB (Over.homMk g rfl : Over.mk (g ≫ Z.hom) ⟶ Z) hW
      obtain ⟨β, hβ⟩ := exists_spMap (g ≫ Z.hom ≫ s')
      have hu := map_fnOn _ g β hβ (b.ζ ^ (2 * omegaStd a a'))
      rw [show Units.map β.toMonoidHom (b.ζ ^ (2 * omegaStd a a')) =
        Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a') from map_zpow _ _ _] at hu
      constructor
      · intro e β' hβ'
        obtain rfl : β' = β := spMap_inj' (hβ'.symm.trans hβ)
        rw [← hu, ← e]
        exact hW'
      · intro H
        exact CommutatorPairing.weilIs_unique hG c₀.ab hLB hW' (hu ▸ H β hβ)

  obtain ⟨κ, hκ, q, hq⟩ := exists_finite_mod (Fin h ⊕ Fin h → ℤ) hNpos
  haveI := hκ
  have inv : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ),
      P2 a a' k g → P2 (a + N • c₁) (a' + N • c₂) k g := by
    intro k _ _ g a a' c₁ c₂ H β hβ
    have e1 : ∀ a c, et (a + N • c) = et a := fun a c => by rw [hadd, add_map_nsmul hadd, hpow, _root_.mul_one]
    rw [e1, e1]
    obtain ⟨m, hm⟩ : ∃ m : ℤ, omegaStd (a + N • c₁) (a' + N • c₂) = omegaStd a a' + N * m :=
      ⟨_, omegaStd_add_nsmul N a a' c₁ c₂⟩
    have hz : Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd (a + N • c₁) (a' + N • c₂)) =
        Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a') := by
      rw [hm, mul_add, zpow_add, show (2 : ℤ) * (N * m) = N * (2 * m) by ring, zpow_mul _ (N : ℤ), zpow_natCast,
        hzN, one_zpow, _root_.mul_one]
    rw [hz]
    exact H β hβ
  let r : κ → (Fin h ⊕ Fin h → ℤ) := Function.invFun q
  have localization₂ : HkClopen.Loc (fun (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ Z.left) => ∀ a a', P2 a a' k g) := by
    refine (HkClopen.Loc.all (I₀ := κ × κ) (P := fun i => P2 (r i.1) (r i.2)) fun i => locPair _ _).congr
      fun k _ _ g => ⟨fun H a a' => ?_, fun H i => H _ _⟩
    obtain ⟨c₁, e₁⟩ := hq (r (q a)) a (Function.invFun_eq ⟨a, rfl⟩)
    obtain ⟨c₂, e₂⟩ := hq (r (q a')) a' (Function.invFun_eq ⟨a', rfl⟩)
    rw [e₁, e₂]
    exact inv k g _ _ c₁ c₂ (H (q a, q a'))
  obtain ⟨Wp, hWp, HWp⟩ := localization₂
  let U : Z.left.Opens := Ul ⊓ ⟨Wp, hWp.isOpen⟩
  have hU : IsClosed (U : Set Z.left) := hUl.inter hWp.isClosed
  obtain ⟨V, i, hV1, hV2, hi, Hi⟩ := exists_sub U hU
  have memWp : ∀ (Tw : Over S) (w : Tw ⟶ Z), (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Tw.left) (a a'),
      P2 a a' k (x ≫ w.left)) → Set.range w.left ⊆ Wp := by
    rintro Tw w H _ ⟨p, rfl⟩
    obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point Tw.left p
    have h₁ := (HWp k (x ≫ w.left)).2 (H k x)
    have hp : x (default : PrimeSpectrum k) = p := by
      have : x (default : PrimeSpectrum k) ∈ Set.range x := ⟨_, rfl⟩
      rwa [hx] at this
    exact (show (x ≫ w.left) (default : PrimeSpectrum k) = w.left p by rw [← hp]; rfl) ▸ h₁
  have hir : Set.range i.left ⊆ U := (Hi V i).2 ⟨𝟙 _, Category.id_comp _⟩
  have hiL := (HUl V i).2 fun _ hp => (hir hp).1
  have iW : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ V.left) (a a'), P2 a a' k (x ≫ i.left) :=
    fun k _ _ x => (HWp k (x ≫ i.left)).1 (hir ⟨x (default : PrimeSpectrum k), rfl⟩).2

  have hprim : ∀ (k : Type) [Field k] (β : B' →+* k), IsPrimitiveRoot (Units.map β.toMonoidHom b.ζ) N :=
    fun k _ β => IsPrimitiveRoot.coe_units_iff.1 (b.prim k β)
  obtain ⟨C, φ, hsrel, hlev, huniv'⟩ := buildCover h n N (N / n) B' B' (b₀.ζ : B') (b.ζ : B') S V.left s'
    (V.hom ≫ s') V.hom c₀ (fun a => i ≫ et a) (fun a a' => by rw [hadd, MonObj.comp_mul])
    (fun a => by rw [← MonObj.comp_pow, hpow, MonObj.comp_one])
    (fun a => by rw [← MonObj.comp_pow, hiL a, comp_toUnit_assoc]; rfl)
    (fun k _ _ x β z hx hz => by
      obtain rfl : z = Units.map β.toMonoidHom b.ζ := Units.ext hz
      have hxS : (x ≫ V.hom) ≫ s' = spMap β := by rw [Category.assoc]; exact hx
      obtain ⟨e₀, a1, -, -, k1, o1, -⟩ := geomLift h n N B' b (b₀.ζ : B') S s' c₀ k (x ≫ V.hom) β hn hN hnN hb₀
        hc₀ hxS
      have hpair : ∀ a a', Out.WeilIs c₀.A c₀.diag N
          ((Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a)
          ((Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a')
          (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := fun a a' =>
        weilIs_congr_base (by rw [Category.assoc, Over.w i]) (by simp) (by simp)
          (iW k x a a' β (by rw [← hx, Category.assoc, reassoc_of% (Over.w i)]))
      obtain ⟨b1, b2⟩ := geomBij h N k S (x ≫ V.hom) c₀.A c₀.diag (Units.map β.toMonoidHom b.ζ) e₀
        (fun a => (Over.homMk x rfl : Over.mk (x ≫ V.hom) ⟶ Over.mk V.hom) ≫ i ≫ et a) hLB hN (hprim k β) a1 k1 o1
        (fun a a' => by simp only [hadd, MonObj.comp_mul])
        (fun a => by rw [← MonObj.comp_pow, ← MonObj.comp_pow, hpow, MonObj.comp_one, MonObj.comp_one]) hpair
      exact ⟨b1, b2, hpair⟩)

  have h1T : ∀ (T : Scheme.{0}), (𝟙_ (Over T)).hom = 𝟙 T := fun T => rfl
  refine ⟨V.left, V.hom, C, hV1, hV2, ⟨fun pt => ?_⟩, (hrel V.left V.hom C).1 ⟨φ, hsrel⟩, fun T t C' hC' => ?_⟩
  · obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point S pt
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s')
    obtain ⟨e₀, a1, p1, l1, -, -, w1⟩ := geomLift h n N B' b (b₀.ζ : B') S s' c₀ k x β hn hN hnN hb₀ hc₀ hβ
    obtain ⟨w, hw, -⟩ := huniv (Over.mk x) e₀ a1 p1
    have hx' : w.left ≫ Z.hom = x := Over.w w
    have hwl : Set.range w.left ⊆ Ul := (HUl (Over.mk x) w).1 fun a => by
      rw [MonObj.comp_pow, hw, l1, comp_toUnit_assoc]
    have hwW : w.left (default : PrimeSpectrum k) ∈ Wp := (HWp k w.left).2 fun a a' β' hβ' => by
      obtain rfl : β' = β := spMap_inj' (hβ'.symm.trans (by rw [← Category.assoc, hx', hβ]))
      exact weilIs_congr_base hx'.symm (by rw [← hw a]; rfl) (by rw [← hw a']; rfl) (w1 a a')
    obtain ⟨w', hw'⟩ := (Hi _ w).1 fun _ hq => ⟨hwl hq, (HkClopen.range_subset_iff w.left Wp).2 hwW hq⟩
    obtain ⟨p, hp⟩ : pt ∈ Set.range x := by rw [hx]; rfl
    exact ⟨w'.left p, by rw [← Scheme.Hom.comp_apply, Over.w w']; exact hp⟩
  · obtain ⟨φ', pb', hφ', low'⟩ := (hrel T t C').2 hC'
    let Tt : Over S := Over.mk ((𝟙_ (Over T)).hom ≫ t)
    let et' : (Fin h ⊕ Fin h → ℤ) → (Tt ⟶ c₀.A) := fun a => pushHom pb' (𝟙_ (Over T)) (C'.lev a)
    have a' : ∀ a a₂, et' (a + a₂) = et' a * et' a₂ := fun a a₂ => by simp only [et', C'.lev_add, map_mul]
    have p' : ∀ a, et' a ^ N = 1 := fun a => by simp only [et', ← map_pow, C'.lev_tors, map_one]
    obtain ⟨u, hu, -⟩ := huniv Tt et' a' p'
    have hul : ∀ a, (u ≫ et a).left = (C'.lev a).left ≫ φ' := fun a => by rw [hu]; rfl
    have hut : u.left ≫ Z.hom = t := (Over.w u).trans (Category.id_comp t)
    have hulow : Set.range u.left ⊆ Ul := (HUl Tt u).1 fun a => by
      rw [MonObj.comp_pow, hu, comp_toUnit_assoc]
      apply Over.OverMorphism.ext
      simp only [et', ← map_pow]
      show (C'.lev a ^ (N / n)).left ≫ φ' = (toUnit Tt).left ≫ (c₀.lev a).left
      rw [low' a, pow_one, Over.toUnit_left]
      exact (Category.id_comp t ▸ rfl : t ≫ (c₀.lev a).left = Tt.hom ≫ (c₀.lev a).left)
    have huW : Set.range u.left ⊆ Wp := memWp Tt u fun k _ _ x a a₂ β hβ =>
      weilTransport h N n B' B' (b₀.ζ : B') (b.ζ : B') S T s' (t ≫ s') c₀ C' t φ' pb' hφ' k x β
        (Units.map β.toMonoidHom b.ζ) ((x ≫ u.left) ≫ Z.hom) _ _ a a₂
        (by rw [← hβ, Category.assoc, reassoc_of% hut])
        rfl (by rw [Category.assoc, hut])
        (by rw [Over.comp_left, ← hul, Over.comp_left]; simp)
        (by rw [Over.comp_left, ← hul, Over.comp_left]; simp)
    obtain ⟨t₁, ht₁⟩ := (Hi Tt u).1 fun _ hq => ⟨hulow hq, huW hq⟩
    have ht₁π : t₁.left ≫ V.hom = t := (Over.w t₁).trans (Category.id_comp t)
    refine ⟨t₁.left, ⟨ht₁π, (huniv' T t₁.left B' (b.ζ : B') (t ≫ s') C').2 ⟨φ', by rw [ht₁π]; exact ⟨pb', hφ', low'⟩,
      fun a => (hul a).symm.trans (by rw [← ht₁]; simp)⟩⟩, ?_⟩
    rintro t₂ ⟨ht₂, hpb₂⟩
    obtain ⟨φ₂, hsr₂, hl₂⟩ := (huniv' T t₂ B' (b.ζ : B') (t ≫ s') C').1 hpb₂
    rw [ht₂] at hsr₂
    have e := _root_.GlobalTheory.SiegRigid.eq_of_sRelBy h n N (N / n) B' B' b₀ (b.ζ : B') S T s' (t ≫ s') c₀ C' t φ' φ₂ hn hnodd hc₀
      ⟨pb', hφ', low'⟩ hsr₂
    subst e
    let h₂ : Tt ⟶ V := Over.homMk t₂ (ht₂.trans (Category.id_comp t).symm)
    have : h₂ ≫ i = u := R.ext fun a => Over.OverMorphism.ext (by rw [hul, hl₂ a]; simp [h₂])
    exact congrArg (fun q => q.left) ((cancel_mono i).1 (this.trans ht₁.symm))

end GlobalTheory.SiegCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatChartEtaleOfQuasiFiniteAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → (∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ Etale (W.ι ≫ pullback.snd τ h) := by
  intro R _ _ _ hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxc hxm hinj hsurj hqf
  have hτf : LocallyOfFiniteType τ := by
    have : LocallyOfFiniteType (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUf
    exact locallyOfFiniteType_of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have hτs : IsSeparated τ := by
    have : IsSeparated (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUs
    exact IsSeparated.of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have : IsNoetherianRing R := hR.1
  have hA : IsLocallyNoetherian 𝔸(Fin g; Sp R) := LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin g; Sp R) ↘ Sp R)
  obtain ⟨T, h, W, p, het, hcon, hpW, hpx, hfin, hone, hgeo⟩ := _root_.GlobalTheory.EtaleFinitePiece.main _ _ τ hA hτf hτs x hqf
  have hiso := _root_.GlobalTheory.Mum.FlatChartDeg.isIso_finite_piece R hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxm hinj hsurj
    T h W p inferInstance hcon hpW hpx hfin hone hgeo
  exact ⟨T, h, W, p, inferInstance, hpW, hpx, inferInstance⟩
end

