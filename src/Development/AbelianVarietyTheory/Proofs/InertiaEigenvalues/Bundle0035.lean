module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonLastDominantIndexMulXSubC
section
open Polynomial

namespace GlobalTheory

theorem newton_step_root_in_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ),
      0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧
        ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j <
          ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by
  intro K _ _ g a ρ d hρ ha hle hlt
  have hsub : ∀ x y : K, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
    intro x y
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hcoef : ∀ k, ((X - C a) * g).coeff (k + 1) = g.coeff k - g.coeff (k + 1) * a := by
    intro k
    rw [mul_comm]
    exact coeff_mul_X_sub_C
  have hcoef0 : ((X - C a) * g).coeff 0 = -a * g.coeff 0 := by
    rw [mul_coeff_zero]
    simp

  have hM : 0 < ‖g.coeff d‖ * ρ ^ d := by
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    linarith
  have hsmall : ‖g.coeff (d + 1) * a‖ < ‖g.coeff d‖ := by
    rw [norm_mul]
    have hp : 0 < ρ ^ (d + 1) := by positivity
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have hn : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    have h2 : ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1) < ‖g.coeff d‖ * ρ ^ (d + 1) := by
      calc ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1)
          = (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ‖a‖ := by ring
        _ ≤ (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
        _ < (‖g.coeff d‖ * ρ ^ d) * ρ := mul_lt_mul_of_pos_right h hρ
        _ = ‖g.coeff d‖ * ρ ^ (d + 1) := by ring
    exact lt_of_mul_lt_mul_right h2 hp.le
  have htopn : ‖((X - C a) * g).coeff (d + 1)‖ = ‖g.coeff d‖ := by
    rw [hcoef d, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hsmall.ne'),
      norm_neg]
    exact max_eq_left hsmall.le
  have htop : ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) = ρ * (‖g.coeff d‖ * ρ ^ d) := by
    rw [htopn]; ring

  have key : ∀ k, ‖((X - C a) * g).coeff (k + 1)‖ * ρ ^ (k + 1) ≤
      max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
    intro k
    rw [hcoef k]
    have h1 := hsub (g.coeff k) (g.coeff (k + 1) * a)
    rw [norm_mul] at h1
    have hp : 0 ≤ ρ ^ (k + 1) := by positivity
    have hn : 0 ≤ ‖g.coeff (k + 1)‖ * ρ ^ (k + 1) := by positivity
    calc ‖g.coeff k - g.coeff (k + 1) * a‖ * ρ ^ (k + 1)
        ≤ max ‖g.coeff k‖ (‖g.coeff (k + 1)‖ * ‖a‖) * ρ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right h1 hp
      _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)) :=
          max_mul_of_nonneg _ _ hp
      _ ≤ max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
          apply max_le_max
          · exact le_of_eq (by ring)
          · calc ‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)
                = (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ‖a‖ := by ring
              _ ≤ (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
              _ = ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) := by ring
  constructor
  · intro j
    rw [htop]
    cases j with
    | zero =>
      rw [hcoef0, norm_mul, norm_neg, pow_zero, mul_one]
      have h0 := hle 0
      rw [pow_zero, mul_one] at h0
      calc ‖a‖ * ‖g.coeff 0‖ ≤ ρ * ‖g.coeff 0‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ ≤ ρ * (‖g.coeff d‖ * ρ ^ d) := mul_le_mul_of_nonneg_left h0 hρ.le
    | succ k =>
      exact (key k).trans (max_le (mul_le_mul_of_nonneg_left (hle k) hρ.le)
        (mul_le_mul_of_nonneg_left (hle (k + 1)) hρ.le))
  · intro j hj
    rw [htop]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (key k).trans_lt (max_lt (mul_lt_mul_of_pos_left (hlt k (by omega)) hρ)
      (mul_lt_mul_of_pos_left (hlt (k + 1) (by omega)) hρ))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfCharacterEq
section
namespace GlobalTheory.CharacterDetermines

open Representation Module

variable {G V W V' W' : Type} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']

noncomputable def prodEquivOfIsCompl {ρ : Representation ℂ G V} (p q : Subrepresentation ρ)
    (h : IsCompl p.toSubmodule q.toSubmodule) :
    (p.toRepresentation.prod q.toRepresentation).Equiv ρ :=
  Representation.Equiv.mk (Submodule.prodEquivOfIsCompl _ _ h) fun g => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    simp [Representation.prod, Subrepresentation.toRepresentation]

noncomputable def prodCongr {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}
    (e : ρ.Equiv σ) (e' : ρ'.Equiv σ') : (ρ.prod ρ').Equiv (σ.prod σ') :=
  Representation.Equiv.mk (e.toLinearEquiv.prodCongr e'.toLinearEquiv) fun g => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, b⟩ := x
    refine Prod.ext ?_ ?_
    · exact e.toIntertwiningMap.isIntertwining _ _ g a
    · exact e'.toIntertwiningMap.isIntertwining _ _ g b

theorem character_prod [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    (ρ.prod σ).character = ρ.character + σ.character := by
  funext g
  change LinearMap.trace ℂ (V × W) ((ρ g).prodMap (σ g)) = LinearMap.trace ℂ V (ρ g) + LinearMap.trace ℂ W (σ g)
  rw [LinearMap.trace_prodMap']

theorem exists_isCompl [Finite G] {ρ : Representation ℂ G V} (p : Subrepresentation ρ) :
    ∃ q : Subrepresentation ρ, IsCompl p.toSubmodule q.toSubmodule := by
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨c, hc⟩ := MonoidAlgebra.Submodule.exists_isCompl (Subrepresentation.asSubmodule p)
  refine ⟨Subrepresentation.ofSubmodule' c, ?_⟩
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    exact (Submodule.disjoint_def.mp hc.disjoint) x hx hx'
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro x
    have hx : (show ρ.asModule from x) ∈ (Subrepresentation.asSubmodule p ⊔ c) := by
      rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, hyz⟩

theorem nonempty_equiv_range {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : IntertwiningMap ρ σ) (q : Subrepresentation ρ)
    (h : IsCompl f.ker.toSubmodule q.toSubmodule) :
    Nonempty (q.toRepresentation.Equiv f.range.toRepresentation) := by
  let φ : q.toSubmodule →ₗ[ℂ] f.range.toSubmodule :=
    (f.toLinearMap.comp q.toSubmodule.subtype).codRestrict f.range.toSubmodule
      (fun v => LinearMap.mem_range_self _ _)
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : f.toLinearMap (a : V) = 0 := congrArg Subtype.val ha
    have hk : (a : V) ∈ f.ker.toSubmodule := ha'
    exact Subtype.ext ((Submodule.disjoint_def.mp h.disjoint) _ hk a.2)
  have hsurj : Function.Surjective φ := by
    rintro ⟨w, v, rfl⟩
    have hv : v ∈ f.ker.toSubmodule ⊔ q.toSubmodule := by
      rw [h.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨k, hk, u, hu, hku⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    have hk' : f.toLinearMap k = 0 := hk
    change f.toLinearMap u = f.toLinearMap v
    rw [← hku, map_add (f := _), hk', zero_add]
  let ψ : IntertwiningMap q.toRepresentation f.range.toRepresentation :=
    φ.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      apply Subtype.ext
      change f.toLinearMap (ρ g (v : V)) = σ g (f.toLinearMap v)
      exact IntertwiningMap.isIntertwining _ _ f g v)
  exact ⟨ψ.ofBijective ⟨hinj, hsurj⟩⟩

theorem exists_ne_zero [Finite G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [Nontrivial V]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (h : ρ.character = σ.character) :
    ∃ f : IntertwiningMap ρ σ, f ≠ 0 := by
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h1 := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h2 := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
  rw [← h, h2] at h1
  have hid : IntertwiningMap.id ρ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h0
    exact hv (by simpa using DFunLike.congr_fun h0 v)
  have hpos : 0 < finrank ℂ (IntertwiningMap ρ ρ) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hid⟩
  have heq : finrank ℂ (IntertwiningMap ρ ρ) = finrank ℂ (IntertwiningMap ρ σ) := by
    exact_mod_cast h1
  rw [heq] at hpos
  exact Module.finrank_pos_iff_exists_ne_zero.mp hpos

theorem aux [Finite G] (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W), finrank ℂ V = n →
    ρ.character = σ.character → Nonempty (ρ.Equiv σ) := by
  refine Nat.strong_induction_on n ?_
  intro n ih V W _ _ _ _ _ _ ρ σ hn h
  rcases subsingleton_or_nontrivial V with hV | hV
  · have hW : finrank ℂ V = finrank ℂ W := by
      have h1 := congrFun h 1
      rw [char_one, char_one] at h1
      exact_mod_cast h1
    refine ⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hW) fun g => ?_⟩
    ext v
    rw [Subsingleton.elim v 0]
    simp
  · obtain ⟨f, hf⟩ := exists_ne_zero ρ σ h
    obtain ⟨q, hq⟩ := exists_isCompl f.ker
    obtain ⟨r, hr⟩ := exists_isCompl f.range
    obtain ⟨e⟩ := nonempty_equiv_range f q hq
    have h1 := char_iso (prodEquivOfIsCompl q f.ker hq.symm)
    have h2 := char_iso (prodEquivOfIsCompl f.range r hr)
    rw [character_prod] at h1 h2
    have h3 := char_iso e
    have hsum : q.toRepresentation.character + f.ker.toRepresentation.character =
        f.range.toRepresentation.character + r.toRepresentation.character := by
      rw [h1, h2, h]
    rw [h3] at hsum
    have hK := add_left_cancel hsum
    have hlt : finrank ℂ f.ker.toSubmodule < n := by
      rw [← hn]
      apply Submodule.finrank_lt
      intro htop
      apply hf
      ext v
      have hv : v ∈ f.ker.toSubmodule := htop ▸ Submodule.mem_top
      have hv' : f.toLinearMap v = 0 := hv
      simpa using hv'
    obtain ⟨eK⟩ := ih _ hlt f.ker.toSubmodule r.toSubmodule f.ker.toRepresentation
      r.toRepresentation rfl hK
    exact ⟨((prodEquivOfIsCompl q f.ker hq.symm).symm.trans (prodCongr e eK)).trans
      (prodEquivOfIsCompl f.range r hr)⟩

theorem nonempty_equiv_of_character_eq : ∀ (G V W : Type) [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W), ρ.character = σ.character → Nonempty (ρ.Equiv σ) := by
  intro G V W _ _ _ _ _ _ _ _ ρ σ h
  exact aux (finrank ℂ V) V W ρ σ rfl h

end GlobalTheory.CharacterDetermines
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLinearEquivOfCharpolyEq
section
noncomputable section

namespace GlobalTheory.TraceIso

open Module

variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def tr (k : Type) [Field k] {A : Type} [Ring A] [Algebra k A] (V : Type) [AddCommGroup V] [Module k V]
    [Module A V] [IsScalarTower k A V] (a : A) : k :=
  LinearMap.trace k V (Algebra.lsmul k k V a)

section

variable {V W : Type} [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
  [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]

theorem tr_congr (e : V ≃ₗ[A] W) (a : A) : tr k V a = tr k W a := by
  have h : Algebra.lsmul k k W a = (e.restrictScalars k).conj (Algebra.lsmul k k V a) := by
    ext w
    simp [LinearEquiv.conj_apply]
  rw [tr, tr, h, LinearMap.trace_conj']

theorem tr_prod [FiniteDimensional k V] [FiniteDimensional k W] (a : A) :
    tr k (V × W) a = tr k V a + tr k W a := by
  have h : Algebra.lsmul k k (V × W) a = (Algebra.lsmul k k V a).prodMap (Algebra.lsmul k k W a) := by
    ext <;> simp
  rw [tr, h, LinearMap.trace_prodMap']
  rfl

theorem finiteDimensional_sub [FiniteDimensional k V] (P : Submodule A V) : FiniteDimensional k P := inferInstanceAs (FiniteDimensional k (P.restrictScalars k))

theorem finrank_eq_zero_of_hom [CharZero k] [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (h : ∀ a : A, tr k V a = tr k W a)
    (h₁ : ∀ f : V →ₗ[A] W, f = 0) (h₂ : ∀ f : W →ₗ[A] V, f = 0) : finrank k V = 0 := by
  classical
  let p : End A (V × W) := (LinearMap.inl A V W).comp (LinearMap.fst A V W)
  let F : End (End A (V × W)) (V × W) :=
    { toFun := p
      map_add' := p.map_add
      map_smul' := by
        rintro φ ⟨v, w⟩
        have e₁ := LinearMap.congr_fun
          (h₁ ((LinearMap.snd A V W).comp (φ.comp (LinearMap.inl A V W)))) v
        have e₂ := LinearMap.congr_fun
          (h₂ ((LinearMap.fst A V W).comp (φ.comp (LinearMap.inr A V W)))) w
        have e₃ : φ (v, w) = φ (v, 0) + φ (0, w) := by rw [← map_add (f := _)]; simp
        simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.snd_apply,
          LinearMap.fst_apply, LinearMap.zero_apply] at e₁ e₂
        change ((φ (v, w)).1, (0 : W)) = φ (v, 0)
        rw [e₃]
        ext
        · simp [e₂]
        · exact e₁.symm }
  let b := Module.finBasis k (V × W)
  haveI : IsSemisimpleModule A (V × W) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl A V W))
      (IsSemisimpleModule.range (LinearMap.inr A V W))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have hall : (p.restrictScalars k) = Algebra.lsmul k k (V × W) r :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hV : Algebra.lsmul k k V r = 1 := by
    ext v
    exact (congrArg Prod.fst (LinearMap.congr_fun hall (v, 0))).symm
  have hW : Algebra.lsmul k k W r = 0 := by
    ext w
    exact (congrArg Prod.snd (LinearMap.congr_fun hall (0, w))).symm
  have := h r
  unfold tr at this
  rw [hV, hW, LinearMap.trace_one, map_zero] at this
  exact_mod_cast this

theorem split_of_hom [FiniteDimensional k V] [FiniteDimensional k W]
    [IsSemisimpleModule A V] [IsSemisimpleModule A W] (f : V →ₗ[A] W) (hf : f ≠ 0) :
    ∃ (P : Submodule A V) (Q S : Submodule A W), Nonempty (V ≃ₗ[A] P × S) ∧ Nonempty (W ≃ₗ[A] Q × S) ∧
      finrank k P < finrank k V ∧ finrank k Q < finrank k W := by
  obtain ⟨P', hP'⟩ := exists_isCompl (LinearMap.ker f)
  obtain ⟨Q, hQ⟩ := exists_isCompl (LinearMap.range f)
  let e₁ : V ≃ₗ[A] (LinearMap.ker f) × (LinearMap.range f) :=
    (Submodule.prodEquivOfIsCompl _ _ hP').symm.trans
      ((LinearEquiv.refl A _).prodCongr
        ((Submodule.quotientEquivOfIsCompl _ _ hP').symm.trans f.quotKerEquivRange))
  let e₂ : W ≃ₗ[A] Q × (LinearMap.range f) := (Submodule.prodEquivOfIsCompl _ _ hQ.symm).symm
  haveI := finiteDimensional_sub (k := k) (LinearMap.ker f)
  haveI := finiteDimensional_sub (k := k) (LinearMap.range f)
  haveI := finiteDimensional_sub (k := k) Q
  haveI : Nontrivial (LinearMap.range f) :=
    Submodule.nontrivial_iff_ne_bot.2 fun h => hf (LinearMap.range_eq_bot.1 h)
  have hpos : 0 < finrank k (LinearMap.range f) := Module.finrank_pos
  refine ⟨_, Q, _, ⟨e₁⟩, ⟨e₂⟩, ?_, ?_⟩
  · rw [(e₁.restrictScalars k).finrank_eq, finrank_prod]; omega
  · rw [(e₂.restrictScalars k).finrank_eq, finrank_prod]; omega

end

theorem nonempty_linear_equiv_of_charpoly_eq [CharZero k] (n : ℕ) : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
    [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
    finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → Nonempty (V ≃ₗ[A] W) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have step : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Module A V]
      [IsScalarTower k A V] [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
      [FiniteDimensional k V] [FiniteDimensional k W] [IsSemisimpleModule A V] [IsSemisimpleModule A W],
      finrank k V + finrank k W ≤ n → (∀ a : A, tr k V a = tr k W a) → ∀ f : V →ₗ[A] W, f ≠ 0 →
      Nonempty (V ≃ₗ[A] W) := by
    intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h f hf
    obtain ⟨P, Q, S, ⟨e₁⟩, ⟨e₂⟩, hP, hQ⟩ := split_of_hom (k := k) f hf
    haveI := finiteDimensional_sub (k := k) P
    haveI := finiteDimensional_sub (k := k) Q
    haveI := finiteDimensional_sub (k := k) S
    obtain ⟨e⟩ := ih (finrank k P + finrank k Q) (by omega) P Q le_rfl fun a => by
      have := h a
      rw [tr_congr e₁, tr_congr e₂, tr_prod, tr_prod] at this
      exact add_right_cancel this
    exact ⟨e₁.trans ((e.prodCongr (LinearEquiv.refl A _)).trans e₂.symm)⟩
  intro V W _ _ _ _ _ _ _ _ _ _ _ _ hn h
  by_cases h₁ : ∀ f : V →ₗ[A] W, f = 0
  · by_cases h₂ : ∀ f : W →ₗ[A] V, f = 0
    · haveI : Subsingleton V := Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom h h₁ h₂)
      haveI : Subsingleton W :=
        Module.finrank_zero_iff.1 (finrank_eq_zero_of_hom (fun a => (h a).symm) h₂ h₁)
      exact ⟨LinearEquiv.ofSubsingleton V W⟩
    · push_neg at h₂
      obtain ⟨f, hf⟩ := h₂
      obtain ⟨e⟩ := step W V (by omega) (fun a => (h a).symm) f hf
      exact ⟨e.symm⟩
  · push_neg at h₁
    obtain ⟨f, hf⟩ := h₁
    exact step V W hn h f hf

theorem exists_equiv_of_trace_eq [CharZero k] {Γ V W : Type} [Monoid Γ] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W) (hρ : ρ.IsSemisimpleRepresentation)
    (hσ : σ.IsSemisimpleRepresentation)
    (h : ∀ g, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) :
    ∃ e : V ≃ₗ[k] W, ∀ g v, e (ρ g v) = σ g (e v) := by
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).1 hρ
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).1 hσ
  have key : ∀ a : MonoidAlgebra k Γ, tr k ρ.asModule a = tr k σ.asModule a := by
    intro a
    unfold tr
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      have e₁ : LinearMap.trace k _ (Algebra.lsmul k k ρ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k V (ρ g) := by
        rw [← LinearMap.trace_conj' (ρ g) ρ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      have e₂ : LinearMap.trace k _ (Algebra.lsmul k k σ.asModule (MonoidAlgebra.of k Γ g)) =
          LinearMap.trace k W (σ g) := by
        rw [← LinearMap.trace_conj' (σ g) σ.asModuleEquiv.symm]
        congr 1
        ext v
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
          Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]
        rfl
      rw [e₁, e₂, h]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | smul c a ha => simp only [map_smul, ha]
  obtain ⟨e⟩ := nonempty_linear_equiv_of_charpoly_eq (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule σ.asModule le_rfl key
  refine ⟨ρ.asModuleEquiv.symm.trans ((e.restrictScalars k).trans σ.asModuleEquiv), fun g v => ?_⟩
  change σ.asModuleEquiv (e (ρ.asModuleEquiv.symm (ρ g v))) =
    σ g (σ.asModuleEquiv (e (ρ.asModuleEquiv.symm v)))
  rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul]
  simp

end GlobalTheory.TraceIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqMulNormIdempotentCorner
section
open NumberField IsDedekindDomain TensorProduct

namespace GlobalTheory

theorem norm_scale_idem_add_compl {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A) (he : ψ e = 1)
    (hea : ∀ a, e * a = algebraMap K A (ψ a) * e) (c : K) :
    Algebra.norm K (algebraMap K A c * e + (1 - e)) = c := by
  classical
  let b := Module.Free.chooseBasis K A
  rw [Algebra.norm_apply, ← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b (Algebra.lmul K A (algebraMap K A c * e + (1 - e))) =
      1 + Matrix.replicateCol Unit (fun i => (c - 1) * b.repr e i) *
        Matrix.replicateRow Unit (fun j => ψ (b j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change b.repr ((algebraMap K A c * e + (1 - e)) * b j) i = _
    have h1 : (algebraMap K A c * e + (1 - e)) * b j = b j + ((c - 1) * ψ (b j)) • e := by
      have := hea (b j)
      rw [Algebra.smul_def, map_mul, map_sub, map_one]
      linear_combination (algebraMap K A c - 1) * this
    simp only [h1, map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul]
    rw [Finsupp.single_apply]
    congr 1
    · split_ifs with h h' h' <;> first | rfl | (exfalso; exact h' h.symm) | (exfalso; exact h h'.symm)
    · ring
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : ∑ j, ψ (b j) * ((c - 1) * b.repr e j) = (c - 1) * ψ e := by
    conv_rhs => rw [← b.sum_repr e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]; ring
  rw [dotProduct, hs, he]; ring

theorem norm_eq_mul_norm_idem_corner : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (ψ : A →ₐ[K] K) (e : A), ψ e = 1 → (∀ a, e * a = algebraMap K A (ψ a) * e) → ∀ a : A, Algebra.norm K a = ψ a * Algebra.norm K (e + (1 - e) * a) := by
  intro K A _ _ _ _ ψ e he hea a
  have hee : e * e = e := by rw [hea e, he, map_one, one_mul]
  have hid : a = (e + (1 - e) * a) * (algebraMap K A (ψ a) * e + (1 - e)) := by
    have h1 := hea a
    linear_combination (-(algebraMap K A (ψ a) - algebraMap K A (ψ a) * a + a - 1)) * hee + h1
  conv_lhs => rw [hid]
  rw [map_mul, norm_scale_idem_add_compl ψ e he hea, mul_comm]

end GlobalTheory
end

