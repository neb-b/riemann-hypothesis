module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0516

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormIndicatorValueInvariantHostFixingAut
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark

namespace GlobalTheory.PolFan.Mark

section Transport

variable {O : Type} [CommRing O] {bar : O → O} {ψ lab : InvFun O} {i : ℕ}
  {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
  {T : X ≃ X} {e : LinearMap.BilinForm ℤ X ≃+ LinearMap.BilinForm ℤ X}
  (he : ∀ β y z, e β y z = β (T y) (T z))
  (hbal : ∀ β, e β ∈ balForms bar X ↔ β ∈ balForms bar X)
  (hψ : ∀ β, ψ.evalZ (e β) = ψ.evalZ β) (hlab : ∀ β, lab.evalZ (e β) = lab.evalZ β)
include he hbal hψ hlab

theorem inFace_transport (β x : LinearMap.BilinForm ℤ X) :
    InFace bar ψ lab (e β) (e x) ↔ InFace bar ψ lab β x := by
  unfold InFace
  simp only [he]
  rw [hbal, ← map_add (f := _), hψ, hψ, hψ, hlab, hlab]
  refine and_congr Iff.rfl (and_congr ?_ (and_congr ?_ Iff.rfl))
  · exact ⟨fun h y => by simpa using h (T.symm y), fun h y => h (T y)⟩
  · exact ⟨fun h y => by simpa using h (T.symm y), fun h y => h (T y)⟩

theorem isIndec_transport (β x : LinearMap.BilinForm ℤ X) :
    IsIndec bar ψ lab (e β) (e x) ↔ IsIndec bar ψ lab β x := by
  unfold IsIndec
  rw [inFace_transport he hbal hψ hlab, e.map_ne_zero_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h y z hy hz hy0 hz0 hs => ?_, fun h y z hy hz hy0 hz0 hs => ?_⟩)
  · refine h (e y) (e z) ((inFace_transport he hbal hψ hlab β y).2 hy) ((inFace_transport he hbal hψ hlab β z).2 hz)
      (e.map_ne_zero_iff.2 hy0) (e.map_ne_zero_iff.2 hz0) ?_
    rw [← map_add (f := _), hs]
  · refine h (e.symm y) (e.symm z) ?_ ?_ ?_ ?_ ?_
    · rw [← inFace_transport he hbal hψ hlab, e.apply_symm_apply]; exact hy
    · rw [← inFace_transport he hbal hψ hlab, e.apply_symm_apply]; exact hz
    · exact fun h0 => hy0 (by rw [← e.apply_symm_apply y, h0, map_zero])
    · exact fun h0 => hz0 (by rw [← e.apply_symm_apply z, h0, map_zero])
    · apply e.injective; rw [map_add (f := _), e.apply_symm_apply, e.apply_symm_apply, hs]

theorem isMarked_transport_of (β : LinearMap.BilinForm ℤ X) (h : IsMarked bar ψ lab i X β) :
    IsMarked bar ψ lab i X (e β) := by
  obtain ⟨hb, hn, hp, hl, S, hS, k, hk, hsum⟩ := h
  refine ⟨(hbal β).2 hb, fun y => by rw [he]; exact hn _, fun k' β' h' => hp k' (e.symm β') ?_, by rw [hlab]; exact hl,
    S.map e.toEquiv.toEmbedding, fun x => ?_, k, hk, ?_⟩
  · apply e.injective; rw [map_zsmul, e.apply_symm_apply, h']
  · rw [Finset.mem_map_equiv, hS, ← isIndec_transport he hbal hψ hlab]
    show IsIndec bar ψ lab (e β) (e (e.symm x)) ↔ _
    rw [e.apply_symm_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_map, ← map_zsmul, hsum, map_sum]; rfl

theorem isMarked_transport (β : LinearMap.BilinForm ℤ X) :
    IsMarked bar ψ lab i X (e β) ↔ IsMarked bar ψ lab i X β := by
  refine ⟨fun h => ?_, isMarked_transport_of he hbal hψ hlab β⟩
  have := isMarked_transport_of (T := T.symm) (e := e.symm) (fun β y z => ?_) (fun β => ?_) (fun β => ?_)
    (fun β => ?_) (e β) h
  · simpa using this
  · have := he (e.symm β) (T.symm y) (T.symm z); simp only [AddEquiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    exact this.symm
  · rw [← hbal, e.apply_symm_apply]
  · rw [← hψ, e.apply_symm_apply]
  · rw [← hlab, e.apply_symm_apply]

end Transport

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def twPi (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) : (Fin n → 𝓞 E) ≃+ (Fin n → 𝓞 E) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

def twForm (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → 𝓞 E) ≃+ LinearMap.BilinForm ℤ (Fin n → 𝓞 E) where
  toFun β := β.compl₁₂ (twPi σ n).toIntLinearEquiv.toLinearMap (twPi σ n).toIntLinearEquiv.toLinearMap
  invFun β := β.compl₁₂ (twPi σ.symm n).toIntLinearEquiv.toLinearMap (twPi σ.symm n).toIntLinearEquiv.toLinearMap
  left_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ (σ.symm (a j))) (fun j => σ (σ.symm (b j))) = β a b
    simp only [RingEquiv.apply_symm_apply]
  right_inv β := LinearMap.ext₂ fun a b => by
    change β (fun j => σ.symm (σ (a j))) (fun j => σ.symm (σ (b j))) = β a b
    simp only [RingEquiv.symm_apply_apply]
  map_add' _ _ := LinearMap.ext₂ fun a b => by simp

@[simp] theorem twForm_apply (σ : 𝓞 E ≃+* 𝓞 E) (n : ℕ) (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) (a b : Fin n → 𝓞 E) :
    twForm σ n β a b = β (fun j => σ (a j)) (fun j => σ (b j)) := rfl

end Twist

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem twForm_mem_balForms (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} {β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)}
    (h : β ∈ balForms H.bar (Fin n → 𝓞 E)) : twForm σ n β ∈ balForms H.bar (Fin n → 𝓞 E) := by
  refine ⟨fun y z => by simp only [twForm_apply]; exact h.1 _ _, fun a y z => ?_⟩
  simp only [twForm_apply]
  have e1 : (fun j => σ ((a • y) j)) = σ a • fun j => σ (y j) := funext fun j => by simp
  have e2 : (fun j => σ ((H.bar a • z) j)) = H.bar (σ a) • fun j => σ (z j) := funext fun j => by
    simp [host_bar_map_comm]
  rw [e1, e2]
  exact h.2 _ _ _

theorem twForm_symm_twForm (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) :
    twForm σ.symm n (twForm σ n β) = β := LinearMap.ext₂ fun a b => by simp

theorem twForm_mem_balForms_iff (H : Host E) (σ : 𝓞 E ≃+* 𝓞 E) {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) :
    twForm σ n β ∈ balForms H.bar (Fin n → 𝓞 E) ↔ β ∈ balForms H.bar (Fin n → 𝓞 E) :=
  ⟨fun h => by simpa [twForm_symm_twForm] using twForm_mem_balForms H σ.symm h, twForm_mem_balForms H σ⟩

theorem evalZ_twForm {H : Host E} {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) {σ : 𝓞 E ≃+* 𝓞 E} (hσ : σ H.w0 = H.w0)
    {n : ℕ} (β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E)) : φ.evalZ (twForm σ n β) = φ.evalZ β := by
  unfold InvFun.evalZ
  rw [InvFun.eval_pi, InvFun.eval_pi]
  exact hφ σ hσ n fun a b => (β a b : ℝ)

theorem markVal_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ lab : InvFun (𝓞 E))
    (i : ℕ), IsTwInv H ψ → IsTwInv H lab → ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 →
    ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
      markVal H.bar ψ lab i n (fun a b => B (fun j => σ (a j)) (fun j => σ (b j))) = markVal H.bar ψ lab i n B := by
  intro E _ _ _ H ψ lab i hψ hlab σ hσ n B
  classical
  unfold markVal
  by_cases h2 : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b, B a b = β a b
  · have h1 : ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b, B (fun j => σ (a j)) (fun j => σ (b j)) = β a b :=
      ⟨twForm σ n h2.choose, fun a b => h2.choose_spec _ _⟩
    rw [dite_eq_left h1, dite_eq_left h2]
    have e : h1.choose = twForm σ n h2.choose := LinearMap.ext₂ fun a b => by
      have := (h1.choose_spec a b).symm.trans (h2.choose_spec _ _)
      exact_mod_cast this
    rw [e, isMarked_transport (T := (twPi σ n).toEquiv) (fun _ _ _ => rfl) (twForm_mem_balForms_iff H σ)
      (evalZ_twForm hψ hσ) (evalZ_twForm hlab hσ)]
  · have h1 : ¬ ∃ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E), ∀ a b,
        B (fun j => σ (a j)) (fun j => σ (b j)) = β a b := fun ⟨β, hβ⟩ =>
      h2 ⟨twForm σ.symm n β, fun a b => by
        have := hβ (fun j => σ.symm (a j)) (fun j => σ.symm (b j))
        simpa using this⟩
    rw [dite_eq_right h1, dite_eq_right h2]

end Main

end GlobalTheory.PolFan.Mark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaxSimplicialCellMultiplicityLtTopOfIsPolyFan
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section
namespace GlobalTheory.PolFan

namespace MultBound
variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁] {m : ℕ}

theorem cellMult_map {Y : Type} [AddCommGroup Y] [Module O Y] (f : balForms bar X ≃ₗ[ℤ] balForms bar Y)
    (δ : Fin m → balForms bar X) : cellMult bar (fun i => f (δ i)) = cellMult bar δ := by
  unfold cellMult
  have hs : (Submodule.span ℤ (Set.range δ)).map (f : balForms bar X →ₗ[ℤ] balForms bar Y) =
      Submodule.span ℤ (Set.range fun i => f (δ i)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  let g := Submodule.Quotient.equiv _ _ f hs
  symm
  refine Nat.card_congr (g.toEquiv.subtypeEquiv fun x => ?_)
  simp only [Submodule.mem_torsion_iff]
  refine exists_congr fun a => ?_
  rw [Submonoid.smul_def, Submonoid.smul_def]
  change _ ↔ (a : ℤ) • g x = 0
  rw [← g.map_smul, LinearEquiv.map_eq_zero_iff]

theorem cellMult_le_of_finite (T : Set (balForms bar X)) (hT : T.Finite) :
    ∃ C : ℕ, ∀ (m : ℕ) (δ : Fin m → balForms bar X), (∀ i, δ i ∈ T) → cellMult bar δ ≤ C := by
  classical
  let F : Set (balForms bar X) → ℕ := fun s => Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ Submodule.span ℤ s))
  refine ⟨hT.toFinset.powerset.sup fun s => F ↑s, fun m δ hδ => ?_⟩
  have hr : Set.range δ ⊆ T := Set.range_subset_iff.2 hδ
  have e : Set.range δ = ↑((hT.subset hr).toFinset) := by simp
  have hmem : (hT.subset hr).toFinset ∈ hT.toFinset.powerset :=
    Finset.mem_powerset.2 (Set.Finite.toFinset_subset_toFinset.2 hr)
  show F (Set.range δ) ≤ _
  rw [e]
  exact Finset.le_sup_of_le hmem le_rfl

theorem zsmul_cancel {g : ℤ} (hg : g ≠ 0) {u w : balForms bar X} (h : g • u = g • w) : u = w :=
  Subtype.ext (LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ (congrArg Subtype.val h) a b
    simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hg this)

theorem prim_eq_of_smul {β β' : balForms bar X} (hβ : IsPrim bar β) (hβ' : IsPrim bar β') {p q : ℕ} (hp : 0 < p)
    (h : p • β = q • β') : β = β' := by
  have hd0 : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left _ hp
  obtain ⟨p', q', hcop, hp', hq'⟩ := Nat.exists_coprime p q
  have h' : (p' : ℤ) • β = (q' : ℤ) • β' := by
    refine zsmul_cancel (g := (Nat.gcd p q : ℤ)) (by exact_mod_cast hd0.ne') ?_
    rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, mul_comm, ← hp', mul_comm, ← hq', natCast_zsmul,
      natCast_zsmul]
    exact h
  have hb : ((Nat.gcd p' q' : ℕ) : ℤ) = p' * Nat.gcdA p' q' + q' * Nat.gcdB p' q' := Nat.gcd_eq_gcd_ab p' q'
  rw [hcop, Nat.cast_one] at hb
  set A := Nat.gcdA p' q'
  set B := Nat.gcdB p' q'
  set x : balForms bar X := B • β + A • β'
  have e1 : β = q' • x := by
    rw [← natCast_zsmul, smul_add, smul_smul, smul_smul,
      show ((q' : ℤ) * A) • β' = (A * p') • β by rw [mul_comm, ← smul_smul, ← h', smul_smul], ← add_smul]
    conv_lhs => rw [← one_smul ℤ β]
    congr 1
    rw [hb]; ring
  have e2 : β' = p' • x := by
    rw [← natCast_zsmul, smul_add, smul_smul, smul_smul,
      show ((p' : ℤ) * B) • β = (B * q') • β' by rw [mul_comm, ← smul_smul, h', smul_smul], ← add_smul]
    conv_lhs => rw [← one_smul ℤ β']
    congr 1
    rw [hb]; ring
  have h1 := hβ _ _ e1
  have h2 := hβ' _ _ e2
  rw [e1, e2, h1, h2]

theorem transport [Module.Finite O X] [Module.Finite O X₁] (e : X ≃ₗ[O] X₁) {δ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar φ δ) (hl : LinearIndependent ℤ δ) (hp : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X₁)) :
    ∃ h' : IsCell bar φ (fun i => pull e.toLinearMap (δ i)), LinearIndependent ℤ (fun i => pull e.toLinearMap (δ i)) ∧
      (∀ i, IsPrim bar (⟨_, h'.mem i⟩ : balForms bar X)) ∧
      cellMult bar (fun i => (⟨pull e.toLinearMap (δ i), h'.mem i⟩ : balForms bar X)) =
        cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X₁)) := by
  have h' : IsCell bar φ (fun i => pull e.toLinearMap (δ i)) :=
    ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
      IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩
  have e0 : ∀ i, (pullBalEquiv bar e) ⟨δ i, h.mem i⟩ = ⟨pull e.toLinearMap (δ i), h'.mem i⟩ := fun i => rfl
  have hfam : (fun i => (pullBalEquiv bar e) ⟨δ i, h.mem i⟩) =
      fun i => (⟨pull e.toLinearMap (δ i), h'.mem i⟩ : balForms bar X) := funext e0
  refine ⟨h', ?_, fun i k β' hk => ?_, by rw [← hfam]; exact cellMult_map _ _⟩
  · let P : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
      { toFun := pull e.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact hl.map' P (LinearMap.ker_eq_bot.2 fun a b hab => by
      rw [← pull_symm_pull e a, ← pull_symm_pull e b]; exact congrArg _ hab)
  · exact hp i k ((pullBalEquiv bar e).symm β') (by rw [← (pullBalEquiv bar e).symm_apply_apply ⟨δ i, h.mem i⟩, e0, hk]; exact map_nsmul (pullBalEquiv bar e).symm.toAddMonoidHom k β')

theorem perModule [Module.Finite O X] (hF : IsPolyFanOn bar φ X)
    (hpsd : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone (bar := bar) (X := X)) :
    ∃ C : ℕ, ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ), LinearIndependent ℤ δ →
      (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) → cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) ≤ C := by
  classical
  obtain ⟨S, hS, hcov⟩ := hF.finite
  let T : Set (balForms bar X) :=
    {β | IsPrim bar β ∧ ∃ γ : balForms bar X, γ.1 ∈ S ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • β = b • γ}
  have hT : T.Finite := by
    have hS' : {γ : balForms bar X | γ.1 ∈ S}.Finite := hS.preimage Subtype.val_injective.injOn
    choose! f hf using fun β (hβ : β ∈ T) => hβ.2
    refine Set.Finite.of_injOn (f := f) (fun β hβ => (hf β hβ).1) (fun β hβ β' hβ' hff => ?_) hS'
    obtain ⟨-, a, b, ha, hb, h1⟩ := hf β hβ
    obtain ⟨-, a', b', ha', hb', h2⟩ := hf β' hβ'
    rw [hff] at h1
    refine prim_eq_of_smul hβ.1 hβ'.1 (p := b' * a) (q := b * a') (by positivity) ?_
    rw [mul_smul, h1, mul_smul, h2, smul_comm]
  obtain ⟨C, hC⟩ := cellMult_le_of_finite T hT
  refine ⟨C, fun m δ h hl hp => ?_⟩
  have hB : toReal (∑ i, δ i) ∈ psdCone (bar := bar) (X := X) := hpsd _ (Submodule.sum_mem _ fun i _ => h.mem i) fun y => by
    simp only [LinearMap.sum_apply]; exact Finset.sum_nonneg fun i _ => h.nonneg i y
  obtain ⟨e, n, γ, c, hγ, hγS, hc, hrel⟩ := hcov _ hB
  obtain ⟨h', hl', hp', hm⟩ := transport e h hl hp
  rw [← hm]
  refine hC m _ fun i => ⟨hp' i, ?_⟩
  have hrel' : ∑ i, toReal (pull e.toLinearMap (δ i)) = ∑ j, c j • toReal (γ j) := by
    rw [← hrel]; ext a b; simp [LinearMap.sum_apply]
  obtain ⟨j, a, b, ha, hb, hab⟩ := _root_.GlobalTheory.PolFan.cell_gen_on_ray O bar φ X m n _ γ c h' hγ hl' hc hrel' i
  exact ⟨⟨γ j, hγ.mem j⟩, hγS j, a, b, ha, hb, Subtype.ext (by simpa using hab)⟩

end MultBound


open MultBound in
theorem maxMult_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → maxMult H.bar q φ < ⊤ := by
  intro E _ _ _ H q φ hφ
  obtain ⟨n, Y, hY⟩ := _root_.GlobalTheory.ProjModFinIso.finitely_many_iso_classes E q
  have hb : ∀ k : Fin n, ∃ C : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
      [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Nonempty (X ≃ₗ[𝓞 E] Y k) → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
      LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
      cellMult H.bar (fun i => (⟨δ i, h.mem i⟩ : balForms H.bar X)) ≤ C := by
    intro k
    by_cases hk : ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X)
      (_ : Module.Projective (𝓞 E) X), Module.finrank (𝓞 E) X ≤ q ∧ Nonempty (X ≃ₗ[𝓞 E] Y k)
    · obtain ⟨X, _, _, _, _, hX, ⟨e⟩⟩ := hk
      haveI : Module.Finite (𝓞 E) (Y k) := Module.Finite.equiv e
      haveI : Module.Projective (𝓞 E) (Y k) := Module.Projective.of_equiv e
      have hYr : Module.finrank (𝓞 E) (Y k) ≤ q := e.finrank_eq ▸ hX
      obtain ⟨C, hC⟩ := perModule (hφ (Y k) hYr) (GlobalTheory.T.intBilinFormToReal_mem_balancedPsdCone E H (Y k))
      refine ⟨C, fun X' _ _ _ _ _ he' m δ h hl hp => ?_⟩
      obtain ⟨e'⟩ := he'
      obtain ⟨h', hl', hp', hc⟩ := transport e'.symm h hl hp
      rw [← hc]
      exact hC m _ h' hl' hp'
    · exact ⟨0, fun X _ _ _ _ hX he => (hk ⟨X, _, _, inferInstance, inferInstance, hX, he⟩).elim⟩
  choose C hC using hb
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hX =>
    iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hl => iSup_le fun hp => ?_
  obtain ⟨k, he⟩ := hY X hX
  exact_mod_cast (hC k X hX he m δ h hl hp).trans (Finset.le_sup (Finset.mem_univ k))

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfChernClassesOfRootsEqZero
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrassKernel

section Esymm

variable (R : Type) [CommRing R] {ι : Type} (m : ι → ℕ)

def blockEsymm : MvPolynomial (Root m) R →ₐ[R] MvPolynomial (Root m) R :=
  aeval fun x : Root m => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) R (x.2 + 1))

theorem split_blockEsymm [DecidableEq ι] (τ₀ : ι) :
    (GlobalTheory.BlockSymm.splitEquiv R τ₀).toAlgHom.comp (blockEsymm R m) =
      ((aeval fun i : Fin (m τ₀) =>
          esymm (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) (i + 1)).restrictScalars R).comp
        ((mapAlgHom (blockEsymm R (fun τ : {τ // τ ≠ τ₀} => m τ.1))).comp
          (GlobalTheory.BlockSymm.splitEquiv R τ₀).toAlgHom) := by
  ext ⟨τ, i⟩ : 1
  by_cases h : τ = τ₀
  · subst h
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, blockEsymm, aeval_X,
      GlobalTheory.BlockSymm.splitEquiv_X_self, mapAlgHom_apply, map_X, AlgHom.restrictScalars_apply]
    have hc : rename (Sigma.mk τ) (esymm (Fin (m τ)) R ((i : ℕ) + 1)) =
        GlobalTheory.BlockSymm.chernRootsOver R m (X (τ, (i : ℕ) + 1)) := by
      simp [GlobalTheory.BlockSymm.chernRootsOver]
    rw [hc, ← GlobalTheory.BlockSymm.splitEquiv_symm_esymm, AlgEquiv.apply_symm_apply]
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, blockEsymm, aeval_X,
      GlobalTheory.BlockSymm.splitEquiv_X_ne R τ₀ h, mapAlgHom_apply, map_C, AlgHom.restrictScalars_apply, aeval_C]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [esymm, map_sum, map_prod, GlobalTheory.BlockSymm.splitEquiv_X_ne R τ₀ h]

end Esymm

theorem blockEsymm_injective (n : ℕ) : ∀ (ι : Type) [Fintype ι], Fintype.card ι = n →
    ∀ (R : Type) [CommRing R] (m : ι → ℕ), Function.Injective (blockEsymm R m) := by
  induction n with
  | zero =>
    intro ι _ hc R _ m
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    haveI : IsEmpty (Root m) := ⟨fun x => IsEmpty.false x.1⟩
    intro p q hpq
    rw [eq_C_of_isEmpty p, eq_C_of_isEmpty q] at hpq ⊢
    simp only [blockEsymm, aeval_C, algebraMap_eq] at hpq
    rw [hpq]
  | succ n ih =>
    intro ι _ hc R _ m
    classical
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hc' : Fintype.card {τ // τ ≠ τ₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let R' := MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R
    have h1 : Function.Injective (aeval (R := R') fun i : Fin (m τ₀) => esymm (Fin (m τ₀)) R' (i + 1)) := by
      intro p q hpq
      apply esymmAlgHom_fin_injective R' (m := m τ₀) (n := m τ₀) le_rfl
      apply Subtype.ext
      rw [esymmAlgHom_apply, esymmAlgHom_apply]
      exact hpq
    have h2 : Function.Injective (mapAlgHom (R := R) (σ := Fin (m τ₀))
        (blockEsymm R (fun τ : {τ // τ ≠ τ₀} => m τ.1))) := by
      intro p q hpq
      exact map_injective _ (ih _ hc' R _) hpq
    have key := split_blockEsymm R m τ₀
    intro p q hpq
    apply (GlobalTheory.BlockSymm.splitEquiv R τ₀).injective
    apply h2
    apply h1
    have := congrArg (fun F => F p) key
    have h' := congrArg (fun F => F q) key
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.restrictScalars_apply] at this h'
    rw [← this, ← h', hpq]

variable {ι : Type} (m : ι → ℕ)

def truncChern : MvPolynomial (ι × ℕ) ℝ →ₐ[ℝ] MvPolynomial (Root m) ℝ :=
  aeval fun x : ι × ℕ =>
    if x.2 = 0 then 1 else if h : x.2 - 1 < m x.1 then X (⟨x.1, ⟨x.2 - 1, h⟩⟩ : Root m) else 0

def liftChern : MvPolynomial (Root m) ℝ →ₐ[ℝ] MvPolynomial (ι × ℕ) ℝ :=
  aeval fun x : Root m => X (x.1, (x.2 : ℕ) + 1)

theorem chernRoots_eq_comp : chernRoots m = (blockEsymm ℝ m).comp (truncChern m) := by
  ext ⟨τ, k⟩ : 1
  simp only [AlgHom.comp_apply, truncChern, aeval_X]
  rcases k with _ | j
  · simp [chernRoots, esymm_zero]
  · by_cases h : j < m τ
    · simp [chernRoots, h, blockEsymm]
    · have hc : (Finset.univ : Finset (Fin (m τ))).card < j + 1 := by simp; omega
      simp [chernRoots, h, esymm, Finset.powersetCard_eq_empty.mpr hc]

def rankIdeal : Ideal (MvPolynomial (ι × ℕ) ℝ) :=
  Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪
    {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)})

theorem mk_liftChern_truncChern :
    (Ideal.Quotient.mkₐ ℝ (rankIdeal m)).comp ((liftChern m).comp (truncChern m)) =
      Ideal.Quotient.mkₐ ℝ (rankIdeal m) := by
  ext ⟨τ, k⟩ : 1
  simp only [AlgHom.comp_apply, truncChern, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  rcases k with _ | j
  · simp only [if_true, map_one]
    rw [← map_one (Ideal.Quotient.mk (rankIdeal m)), Ideal.Quotient.eq]
    rw [← neg_mem_iff, neg_sub]
    exact Ideal.subset_span (Or.inl ⟨τ, rfl⟩)
  · by_cases h : j < m τ
    · simp [h, liftChern]
    · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, h, dif_neg, not_false_eq_true, map_zero]
      rw [eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Or.inr ⟨τ, j + 1, by omega, rfl⟩)

theorem mem_span_of_chernRoots_eq_zero : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ),
    chernRoots m Q = 0 → Q ∈ Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪
      {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)}) := by
  intro ι _ m Q hQ
  have h0 : truncChern m Q = 0 := by
    apply blockEsymm_injective _ ι rfl ℝ m
    rw [map_zero, ← AlgHom.comp_apply, ← chernRoots_eq_comp, hQ]
  have h1 := congrArg (fun F => F Q) (mk_liftChern_truncChern m)
  simp only [AlgHom.comp_apply, h0, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h1
  exact (Ideal.Quotient.eq_zero_iff_mem).mp h1.symm

end GlobalTheory.GrassKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefEqConjTransposeMulSelfOfIsUnitDet
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory


open scoped MatrixOrder in
theorem posDef_eq_conjTranspose_mul_self_of_isUnit_det :
    ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef →
      ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  intro p P hP
  have h0 : (0 : Matrix (Fin p) (Fin p) ℂ) ≤ P := Matrix.nonneg_iff_posSemidef.mpr hP.posSemidef
  have hB : star (CFC.sqrt P) * CFC.sqrt P = P := by
    rw [(CFC.sqrt_nonneg P).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self P h0]
  refine ⟨CFC.sqrt P, ?_, hB⟩
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  rw [← hB, Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

end GlobalTheory
end

