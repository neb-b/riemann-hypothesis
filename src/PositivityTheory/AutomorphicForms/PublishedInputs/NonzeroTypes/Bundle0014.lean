module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0012
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLat
section
noncomputable section

open scoped Classical

open GlobalTheory.SmGL

namespace UpperTheory.TNZ.P_spLat

variable {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {I : Representation ℂ Γ V}

theorem eqvInt {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {α : Representation ℂ Γ A} {β : Representation ℂ Γ B} (e : α.Equiv β) (g : Γ) (v : A) :
    e (α g v) = β g (e v) :=
  Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v

def eqvTrans {A B C : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] {α : Representation ℂ Γ A} {β : Representation ℂ Γ B}
    {γ : Representation ℂ Γ C} (e : α.Equiv β) (f : β.Equiv γ) : α.Equiv γ :=
  Representation.Equiv.mk (e.toLinearEquiv.trans f.toLinearEquiv) (fun g => by
    ext v
    show f (e (α g v)) = γ g (f (e v))
    rw [eqvInt e, eqvInt f])

theorem dich {A : Type} [AddCommGroup A] [Module ℂ A] {α : Representation ℂ Γ A} (hα : α.IsIrreducible)
    (X Y S : Subrepresentation I) (e : (subQuot Y X).Equiv α) :
    Y ⊓ S ≤ X ∨ Y ≤ S ⊔ X := by
  let T : Subrepresentation α :=
    ⟨((S.toSubmodule.comap Y.toSubmodule.subtype).map
        (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ).map e.toLinearMap, by
      rintro g _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨_, ⟨Y.toRepresentation g v, S.apply_mem_toSubmodule g hv, rfl⟩, ?_⟩
      exact eqvInt e g (Submodule.Quotient.mk v)⟩
  rcases hα.eq_bot_or_eq_top T with hT | hT
  · left
    intro v hv
    obtain ⟨hvY, hvS⟩ := hv
    have hm : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) ∈ T.toSubmodule :=
      ⟨_, ⟨⟨v, hvY⟩, hvS, rfl⟩, rfl⟩
    rw [hT] at hm
    have h0 : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) = 0 := (Submodule.mem_bot ℂ).1 hm
    rw [map_eq_zero_iff e (EquivLike.injective e), Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · right
    intro v hvY
    have hm : e (Submodule.Quotient.mk (⟨v, hvY⟩ : Y.toSubmodule)) ∈ T.toSubmodule := by
      rw [hT]; exact Submodule.mem_top
    obtain ⟨_, ⟨w, hwS, rfl⟩, hw⟩ := hm
    have hw' := EquivLike.injective e hw
    have hx0 := (Submodule.Quotient.eq (X.toSubmodule.comap Y.toSubmodule.subtype)).1 hw'
    have hx : (w : V) - v ∈ X.toSubmodule := hx0
    show v ∈ S.toSubmodule ⊔ X.toSubmodule
    refine Submodule.mem_sup.2 ⟨w, hwS, v - w, ?_, by abel⟩
    simpa using X.toSubmodule.neg_mem hx

def eqv (Z W Y X : Subrepresentation I) (hZY : Z ≤ Y) (hY : Y ≤ Z ⊔ X)
    (hW : Z ⊓ W = Z ⊓ X) : (subQuot Z W).Equiv (subQuot Y X) := by
  let f : Z.toSubmodule →ₗ[ℂ] (Y.toSubmodule ⧸ X.toSubmodule.comap Y.toSubmodule.subtype) :=
    (X.toSubmodule.comap Y.toSubmodule.subtype).mkQ ∘ₗ Submodule.inclusion hZY
  have hf : Function.Surjective f := by
    rintro ⟨⟨v, hv⟩⟩
    obtain ⟨z, hz, x, hx, rfl⟩ := Submodule.mem_sup.1 (hY hv)
    refine ⟨⟨z, hz⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    refine (Submodule.Quotient.eq _).2 ?_
    show z - (z + x) ∈ X.toSubmodule
    simpa using X.toSubmodule.neg_mem hx
  have hker : W.toSubmodule.comap Z.toSubmodule.subtype = LinearMap.ker f := by
    ext ⟨v, hv⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f,
      LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show v ∈ W.toSubmodule ↔ v ∈ X.toSubmodule
    have h := congrArg Subrepresentation.toSubmodule hW
    simp only [Subrepresentation.toSubmodule_inf] at h
    constructor
    · intro hw
      have : v ∈ Z.toSubmodule ⊓ W.toSubmodule := ⟨hv, hw⟩
      rw [h] at this
      exact this.2
    · intro hx
      have : v ∈ Z.toSubmodule ⊓ X.toSubmodule := ⟨hv, hx⟩
      rw [← h] at this
      exact this.2
  refine Representation.Equiv.mk ((Submodule.quotEquivOfEq _ _ hker).trans
    (f.quotKerEquivOfSurjective hf)) (fun g => ?_)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply]
  rfl

end UpperTheory.TNZ.P_spLat

namespace UpperTheory.TNZ

open P_spLat in
theorem step_spLat : SpecialLatticeProp := by
  intro Γ V _ _ _ I d hmono hmod htop A B _ _ _ _ α β hα hβ h₁ h₂
  obtain ⟨X₁, Y₁, hXY₁, hd₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨X₂, Y₂, hXY₂, hd₂, ⟨e₂⟩⟩ := h₂
  have hY₁ : d Y₁ ≤ 1 := (hmono le_top).trans htop
  have hY₂ : d Y₂ ≤ 1 := (hmono le_top).trans htop
  have hZ : d (Y₁ ⊓ Y₂) = 1 := by
    have := hmod Y₁ Y₂
    have := (hmono (le_top : Y₁ ⊔ Y₂ ≤ ⊤)).trans htop
    have := hmono (inf_le_left : Y₁ ⊓ Y₂ ≤ Y₁)
    omega
  have hN : d (X₁ ⊔ X₂) = 0 := by
    have := hmod X₁ X₂
    omega
  set Z := Y₁ ⊓ Y₂ with hZdef
  set N := X₁ ⊔ X₂ with hNdef
  have side : ∀ (C : Type) [AddCommGroup C] [Module ℂ C] (γ : Representation ℂ Γ C), γ.IsIrreducible →
      ∀ X Y : Subrepresentation I, X ≤ Y → X ≤ N → Z ≤ Y → d X = 0 → (subQuot Y X).Equiv γ →
      Y ≤ Z ⊔ X ∧ Z ⊓ N = Z ⊓ X := by
    intro C _ _ γ hγ X Y hXY hXN hZY hX e
    refine ⟨?_, ?_⟩
    · rcases dich hγ X Y Z e with h | h
      · exfalso
        have h' : Z ≤ X := by
          have : Y ⊓ Z = Z := inf_eq_right.2 hZY
          rw [← this]; exact h
        have := hmono h'
        omega
      · exact h
    · rcases dich hγ X Y N e with h | h
      · apply le_antisymm
        · exact le_inf inf_le_left ((inf_le_inf_right N hZY).trans h)
        · exact inf_le_inf_left Z hXN
      · exfalso
        have h' : Z ≤ N := hZY.trans (h.trans (sup_le le_rfl hXN))
        have := hmono h'
        omega
  have hd1 : d X₁ = 0 := by omega
  have hd2 : d X₂ = 0 := by omega
  obtain ⟨s₁, t₁⟩ := side A α hα X₁ Y₁ hXY₁ le_sup_left inf_le_left hd1 e₁
  obtain ⟨s₂, t₂⟩ := side B β hβ X₂ Y₂ hXY₂ le_sup_right inf_le_right hd2 e₂
  exact ⟨eqvTrans (eqvTrans e₁.symm (eqv Z N Y₁ X₁ inf_le_left s₁ t₁).symm)
    (eqvTrans (eqv Z N Y₂ X₂ inf_le_right s₂ t₂) e₂)⟩

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpLift
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spLift

variable {Γ V W : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_eigen_lift {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (hρ : IsSmooth ρ)
    (f : ρ.IntertwiningMap σ) {L : Subgroup Γ} (hL : IsCompact (L : Set Γ)) (χ : Γ → ℂ)
    (u : V) (hu : f u ≠ 0) (hχ : ∀ g ∈ L, σ g (f u) = χ g • f u) :
    ∃ v : V, v ≠ 0 ∧ ∀ g ∈ L, ρ g v = χ g • v :=
  _root_.UpperTheory.Reformulated.B.DYka2.main hρ f hL χ u hu hχ

end UpperTheory.TNZ.Grp.P_spLift

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_spLift {n : ℕ} (G : Grp k n) : G.SpecialLiftProp := by
  intro W X _ _ _ _ ρ σ hρ hsq hη
  obtain ⟨S, f, hf⟩ := hsq
  obtain ⟨y, hy, hyη⟩ := hη
  obtain ⟨u, rfl⟩ := hf y
  have hS : IsSmooth S.toRepresentation := fun v => by
    have : {g | S.toRepresentation g v = v} = {g | ρ g (v : W) = v} := by
      ext g
      simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
      rfl
    rw [this]
    exact hρ v
  have hL : IsCompact ((leviK k (fun a : Fin G.s => Fin (G.d a))) :
      Set (Levi k fun a : Fin G.s => Fin (G.d a))) := by
    rw [leviK, Subgroup.coe_pi]
    exact isCompact_univ_pi fun a => GlobalTheory.SplitFlip.isCompact_KO
  obtain ⟨v, hv, hvη⟩ := P_spLift.exists_eigen_lift hS f hL G.eta u hy hyη
  refine ⟨(v : W), fun h => hv (Subtype.ext h), fun m hm => ?_⟩
  exact congrArg Subtype.val (hvη m hm)

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpOrd
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spOrd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_one (n : ℕ) : ∑ _a : Fin n, (1 : ℕ) = n := by simp

theorem stdBlocks_one (n : ℕ) :
    (stdBlocks (fun _ : Fin n => 1) (sum_one n) : (Σ _ : Fin n, Fin 1) ≃ Fin n) =
      Equiv.sigmaUnique (Fin n) (fun _ => Fin 1) := by
  refine Equiv.ext fun x => ?_
  obtain ⟨a, i⟩ := x
  refine Fin.ext ?_
  rw [stdBlocks_val]
  simp

theorem isSmooth_detRep1 {χ : kˣ →* ℂˣ} (h : IsSmoothChar χ) : IsSmooth (detRep (Fin 1) χ) :=
  (isSmooth_ofChar_iff _).2 (h.detChar (n := Fin 1))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hasFiniteLength_detRep1 (χ : kˣ →* ℂˣ) : HasFiniteLength (detRep (R := k) (Fin 1) χ) :=
  hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _)

theorem prin_sub_multi {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) :
    IsSubquotient (prinSeries χ)
      (multiProd (stdBlocks (fun _ : Fin n => 1) (sum_one n)) fun i => detRep (Fin 1) (χ i)) := by
  have h := GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n χ
  rw [← stdBlocks_one] at h
  exact h

end UpperTheory.TNZ.Grp.P_spOrd

namespace UpperTheory.TNZ.Grp

open UpperTheory.TNZ.Grp.P_spOrd GlobalTheory.LocGL.SupportRing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem step_spOrd : SpecialOrderProp (k := k) (n := n) := by
  intro hL V _ _ π hs hi c hc σ h
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hL.loc.zel k
  obtain ⟨hp1, e1⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c (σ i))) (fun i => isSmooth_detRep1 (hc (σ i)))
    (fun i => hasFiniteLength_detRep1 (c (σ i)))
  obtain ⟨hp2, e2⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c i)) (fun i => isSmooth_detRep1 (hc i))
    (fun i => hasFiniteLength_detRep1 (c i))
  have hcl : clsGL _ hp1 = clsGL _ hp2 := by
    apply Ψ.injective
    rw [e1, e2]
    exact Equiv.prod_comp σ (fun i => Ψ (clsGL (detRep (Fin 1) (c i)) (hasFiniteLength_detRep1 (c i))))
  have h1 := h.trans (prin_sub_multi (fun i => c (σ i)))
  have h2 := clsGL_of_pos hp1 hs hi h1
  rw [hcl] at h2
  exact (isSubquotient_of_clsGL_ne hp2 hs hi h2.ne').trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ c)

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiEta
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ.Grp

namespace P_spPiEta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)

theorem twD_hasDetVec {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s)
    (h : HasDetVec (τ a) (G.μ a)) : HasDetVec (G.twD τ a) (G.μ a) := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, fun g hg => ?_⟩
  have h1 := detChar_of_mem_KO
    (isUnram_absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) hg
  rw [twD, twist_apply, h1, hv g hg, Units.val_one, one_smul]

theorem twD_isSmooth {Y : Fin G.s → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)) (a : Fin G.s)
    (h : IsSmooth (τ a)) : IsSmooth (G.twD τ a) :=
  isSmooth_twist h (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem jacU_eq_jac {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (m : Levi k fun a : Fin G.s => Fin (G.d a)) (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)))
    (y : Jacquet π (unipRad k G.e)) : jacU G.e π m y = jac G.e π m y := by
  rw [jac, twist_apply, MonoidHom.inv_apply, deltaHalf_of_mem_leviK hm, inv_one, Units.val_one, one_smul]

end P_spPiEta

theorem step_spPiEta {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.SpecialRepresentationEtaProp := by
  unfold SpecialRepresentationEtaProp
  intro hLift Y _ _ τ hsm hdet
  obtain ⟨v, hv0, hv⟩ := step_tensorVec k G.s G.d Y (G.twD τ) G.μ
    (fun a => P_spPiEta.twD_hasDetVec G τ a (hdet a))
  have hsm' : IsSmooth (piTensor (G.twD τ)) :=
    isSmooth_piTensor fun a => P_spPiEta.twD_isSmooth G τ a (hsm a)
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one G.e (piTensor (G.twD τ)) hsm' v
  let φ := Model.evalOne G.e (Representation.IntertwiningMap.id (multiProd G.e (G.twD τ)))
  have hφ : φ (Submodule.Quotient.mk f) = v := hf1
  let T : Subrepresentation (piTensor (G.twD τ)) := φ.range
  have hmem : ∀ x, φ x ∈ T.toSubmodule := fun x =>
    (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨x, rfl⟩
  let ψ : (jac G.e (multiProd G.e (G.twD τ))).IntertwiningMap T.toRepresentation :=
    ⟨LinearMap.codRestrict T.toSubmodule φ.toLinearMap hmem, fun g => LinearMap.ext fun x => Subtype.ext (φ.isIntertwining _ _ g x)⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hw
    exact ⟨x, rfl⟩
  have hsub : IsSubquotient T.toRepresentation (jac G.e (multiProd G.e (G.twD τ))) :=
    IsSubquotient.of_surjective ψ hψ
  have hη : G.HasEtaVec T.toRepresentation := by
    refine ⟨⟨v, hφ ▸ hmem _⟩, fun h => hv0 (congrArg Subtype.val h), fun m hm => ?_⟩
    apply Subtype.ext
    exact hv m fun a => hm a (Set.mem_univ a)
  obtain ⟨y, hy0, hy⟩ := hLift _ _ _ T.toRepresentation
    (isSmooth_jac G.e (isSmooth_parInd _ _)) hsub hη
  refine ⟨y, hy0, fun m hm => ?_⟩
  exact (P_spPiEta.jacU_eq_jac G _ m hm y).trans (hy m hm)

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiSub
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_spPiSub

theorem exists_equiv_of_map_eq {ι κ α : Type*} [Fintype ι] [Fintype κ] (f : ι → α) (g : κ → α)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ e : ι ≃ κ, ∀ i, g (e i) = f i := by
  have hc : ∀ c, Fintype.card {i // f i = c} = Fintype.card {j // g j = c} := by
    intro c
    have h1 := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using h1
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hc c), fun i => Equiv.ofFiberEquiv_map _ i⟩

theorem map_univ_eq_sum {ι α : Type*} [Fintype ι] (φ : ι → α) :
    Finset.univ.val.map φ = ∑ i, ({φ i} : Multiset α) := by
  rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Multiset.map φ Finset.univ.val),
    Multiset.map_map]
  rfl

theorem sum_map_univ {s n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {α : Type*}
    (F : ∀ a, Fin (d a) → α) :
    ∑ a, Finset.univ.val.map (F a) = Finset.univ.val.map fun i => F (e.symm i).1 (e.symm i).2 := by
  calc ∑ a, Finset.univ.val.map (F a) = ∑ a, ∑ j, ({F a j} : Multiset α) := by
        simp only [map_univ_eq_sum]
    _ = ∑ p : Σ a, Fin (d a), ({F p.1 p.2} : Multiset α) := (Fintype.sum_sigma (fun p : Σ a, Fin (d a) => ({F p.1 p.2} : Multiset α))).symm
    _ = ∑ i, ({F (e.symm i).1 (e.symm i).2} : Multiset α) :=
        (Equiv.sum_comp e.symm (fun p : Σ a, Fin (d a) => ({F p.1 p.2} : Multiset α))).symm
    _ = _ := (map_univ_eq_sum _).symm

end UpperTheory.TNZ.Grp.P_spPiSub

namespace UpperTheory.TNZ.Grp

open P_spPiSub

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_spPiSub {n : ℕ} (G : Grp k n) : G.SpecialRepresentationSubProp := by
  intro hOrd hL Y _ _ τ _ _ ν hν hc hI
  let χ : Fin G.s → kˣ →* ℂˣ := fun a => absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  have hsupp : ∀ a, HasSupport (G.twD τ a)
      (Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) := by
    intro a
    have h1 := (hasSupport_of_isCuspSupport (hc a)).tw (χ a) (hχ a)
    rw [Multiset.map_map] at h1
    convert h1 using 2
    · rfl
    · rename_i j _
      exact (IrrGL.tw_ofChar (ν a j) (χ a) (hν a j) (hχ a)).symm
  have hcOf : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hS := SupportRing.hasSupport_multiProd hL.loc.zel G.hd (G.twD τ) (fun a => (hsupp a).isSmooth)
    (fun a => (hsupp a).isIrreducible) hsupp hI
  have hsum : (∑ a, Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) =
      Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i) :=
    sum_map_univ G.e (fun a j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a)))
  obtain ⟨h, x, hx, -, -, e', he⟩ := hS
  rw [hsum] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x (fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i)) hx
  obtain rfl : x = fun b => IrrGL.ofChar (G.cOf ν (σ b)) (hcOf _) := funext fun b => (hσ b).symm
  have hn : h = n := by simpa using Fintype.card_congr σ
  subst hn
  let φ := multiProdEquiv e' fun b =>
    (equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ b)) (hcOf _))).symm
  have hsq : IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries fun b => G.cOf ν (σ b)) :=
    (he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)).trans
      (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e' _)
  exact hOrd hL _ _ (isSmooth_parInd _ _) hI _ hcOf σ hsq

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTwBasic
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

namespace P_spTwBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_detAbsPow (N : ℕ) (s : ℂ) : IsSmoothChar (detChar (Fin N) (absPow k s)) :=
  (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow k s)).detChar

theorem hasDetVec_twist_absPow {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (s : ℂ) (h : HasDetVec ρ η) :
    HasDetVec (GlobalTheory.SmGL.twist ρ (detChar (Fin N) (absPow k s))) η := by
  obtain ⟨v, hv0, hv⟩ := h
  refine ⟨v, hv0, fun g hg => ?_⟩
  rw [GlobalTheory.SmGL.twist_apply, GlobalTheory.LocGL.detChar_of_mem_KO (GlobalTheory.SmGL.isUnram_absPow k s) hg, hv g hg,
    Units.val_one, one_smul]

end P_spTwBasic

theorem step_spTwBasic {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.NonzeroBasicTwistOfSpecialForm := by
  intro Y _ _ τ a hs hi hd
  unfold twD
  exact ⟨GlobalTheory.SmGL.isSmooth_twist hs (P_spTwBasic.isSmoothChar_detAbsPow _ _),
    GlobalTheory.LocGL.isIrreducible_twist hi _, P_spTwBasic.hasDetVec_twist_absPow _ _ _ hd⟩

end UpperTheory.TNZ.Grp
end
end

