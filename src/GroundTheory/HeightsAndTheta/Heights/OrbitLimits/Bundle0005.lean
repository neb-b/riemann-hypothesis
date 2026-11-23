module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GraphIdeal
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)

variable {n : ℕ}

def graphHom (p : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) ℂ) p : Fin (n + 1) → MvPolynomial (Fin n) ℂ)

def graphIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
  J.comap (graphHom p)

def graphPt (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.snoc x (eval x p)

theorem graphHom_X_castSucc (p : MvPolynomial (Fin n) ℂ) (i : Fin n) :
    graphHom p (X (Fin.castSucc i)) = X i := by
  simp [graphHom]

theorem graphHom_X_last (p : MvPolynomial (Fin n) ℂ) : graphHom p (X (Fin.last n)) = p := by
  simp [graphHom]

theorem graphHom_rename (p q : MvPolynomial (Fin n) ℂ) : graphHom p (rename Fin.castSucc q) = q := by
  rw [graphHom, aeval_rename]
  have : (Fin.snoc (X : Fin n → MvPolynomial (Fin n) ℂ) p : Fin (n + 1) → MvPolynomial (Fin n) ℂ) ∘ Fin.castSucc = X :=
    funext fun i => by simp
  rw [this, aeval_X_left_apply]

theorem graphHom_surjective (p : MvPolynomial (Fin n) ℂ) : Function.Surjective (graphHom p) :=
  fun q => ⟨rename Fin.castSucc q, graphHom_rename p q⟩

theorem eval_graphPt (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (q : MvPolynomial (Fin (n + 1)) ℂ) :
    eval (graphPt p x) q = eval x (graphHom p q) := by
  have h : (eval (graphPt p x) : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ) =
      (eval x).comp (graphHom p).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [graphPt, graphHom]
      · simp [graphPt, graphHom]
  exact congrArg (fun φ : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ => φ q) h

theorem graphPt_init (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin.init (graphPt p x) = x := by
  simp [graphPt]

theorem graphPt_last (p : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : graphPt p x (Fin.last n) = eval x p := by
  simp [graphPt]

theorem graphIdeal_isPrime {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime) (p : MvPolynomial (Fin n) ℂ) :
    (graphIdeal J p).IsPrime :=
  Ideal.comap_isPrime _ _

theorem graphPt_mem_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) {x : Fin n → ℂ}
    (hx : x ∈ zeroSet J) : graphPt p x ∈ zeroSet (graphIdeal J p) := by
  intro q hq
  rw [eval_graphPt]
  exact hx _ hq

theorem init_mem_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : Fin.init x ∈ zeroSet J := by
  intro q hq
  have h := hx (rename Fin.castSucc q) (by rw [graphIdeal, Ideal.mem_comap, graphHom_rename]; exact hq)
  rw [eval_rename] at h
  exact h

theorem graphPt_init_of_mem_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {x : Fin (n + 1) → ℂ} (hx : x ∈ zeroSet (graphIdeal J p)) : graphPt p (Fin.init x) = x := by
  have h := hx (X (Fin.last n) - rename Fin.castSucc p)
    (by rw [graphIdeal, Ideal.mem_comap, map_sub, graphHom_X_last, graphHom_rename, sub_self]; exact J.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  rw [graphPt]
  conv_rhs => rw [← Fin.snoc_init_self x]
  rw [h]
  rfl

theorem ringKrullDim_graphIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J p) = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := by
  let g : MvPolynomial (Fin (n + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J :=
    (Ideal.Quotient.mk J).comp (graphHom p).toRingHom
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp (graphHom_surjective p)
  have hker : RingHom.ker g = graphIdeal J p := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hg))

theorem X_last_not_mem_graphIdeal {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : MvPolynomial (Fin n) ℂ} (hp : p ∉ J) :
    X (Fin.last n) ∉ graphIdeal J p := by
  rw [graphIdeal, Ideal.mem_comap, graphHom_X_last]
  exact hp

theorem graphIdeal_sup_span (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    graphIdeal J p ⊔ Ideal.span {X (Fin.last n)} = graphIdeal (J ⊔ Ideal.span {p}) p := by
  have hs := graphHom_surjective p
  have hmap : (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).map (graphHom p) = J ⊔ Ideal.span {p} := by
    rw [Ideal.map_sup, graphIdeal, Ideal.map_comap_of_surjective _ hs, Ideal.map_span, Set.image_singleton,
      graphHom_X_last]
  rw [← hmap]
  show _ = Ideal.comap (graphHom p) (Ideal.map (graphHom p) _)
  rw [Ideal.comap_map_of_surjective _ hs]
  refine (sup_eq_left.mpr ?_).symm
  exact le_sup_of_le_left (Ideal.comap_mono bot_le)

theorem minimalPrimes_graphIdeal_sup (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) :
    (graphIdeal J p ⊔ Ideal.span {X (Fin.last n)}).minimalPrimes =
      (fun W => graphIdeal W p) '' (J ⊔ Ideal.span {p}).minimalPrimes := by
  rw [graphIdeal_sup_span, graphIdeal]
  exact Ideal.comap_minimalPrimes_eq_of_surjective (graphHom_surjective p) _

theorem graphIdeal_injective (p : MvPolynomial (Fin n) ℂ) : Function.Injective (fun W => graphIdeal W p) :=
  Ideal.comap_injective_of_surjective _ (graphHom_surjective p)

theorem graphIdeal_mono {J W : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ) (h : J ≤ W) :
    graphIdeal J p ≤ graphIdeal W p :=
  Ideal.comap_mono h

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PInvertibleIndexCharP
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

theorem InvertibleIndexCharP.finite_subring {Ω : Type} [Field Ω] (B : Subring Ω) (hp : ringChar Ω ≠ 0)
    (hB : Module.Finite ℤ B) : Finite B := by
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(ringChar Ω : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp)⟩, ?_⟩
  rw [Submonoid.smul_def]
  ext
  simp [zsmul_eq_mul]

theorem InvertibleIndexCharP.proof : InvertibleIndexCharP.Statement := by
  intro Ω _ B X η _ f hp hB hX hf hloc
  have hfin : Finite B := InvertibleIndexCharP.finite_subring B hp hB
  have hfield : IsField B := Finite.isField_of_domain B
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨i, ⟨b₀, hb₀m, hb₀X⟩, hgen⟩ := hloc m hm

  have hunit : ∀ b : B, b ∉ m → ∃ b' : B, (b' : Ω) * b = 1 := by
    intro b hb
    have hb0 : b ≠ 0 := fun h => hb (h ▸ m.zero_mem)
    obtain ⟨b', hb'⟩ := hfield.mul_inv_cancel hb0
    refine ⟨b', ?_⟩
    have := congrArg Subtype.val hb'
    simpa [mul_comm] using this

  have hXeq : (X : Set Ω) = (fun y => f i * y) '' (B : Set Ω) := by
    ext z
    constructor
    · intro hz
      obtain ⟨b, c, hbm, hbc⟩ := hgen z hz
      obtain ⟨b', hb'⟩ := hunit b hbm
      refine ⟨((b' * c : B) : Ω), (b' * c).2, ?_⟩
      calc f i * ((b' * c : B) : Ω) = b' * (c * f i) := by push_cast; ring
        _ = b' * (b * z) := by rw [hbc]
        _ = z := by rw [← mul_assoc, hb', one_mul]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨b', hb'⟩ := hunit b₀ hb₀m
      have hfX : f i ∈ X := by
        have := hX b' b'.2 _ hb₀X
        rwa [← mul_assoc, hb', one_mul] at this
      have := hX y hy _ hfX
      rw [mul_comm] at this
      exact this
  set A := B.toAddSubgroup with hA
  have hAfin : Finite A := hfin
  have hXfin' : (X : Set Ω).Finite := by
    rw [hXeq]; exact (Set.toFinite (B : Set Ω)).image _
  have hXfin : Finite X := hXfin'.to_subtype

  have hcard : Nat.card X = Nat.card A := by
    have h := Nat.card_image_of_injective (mul_right_injective₀ (hf i)) (B : Set Ω)
    rw [← hXeq] at h
    exact h
  have hc : Nat.card (A.addSubgroupOf X) = Nat.card (X.addSubgroupOf A) :=
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩,
          AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩
        invFun := fun x => ⟨⟨x.1.1, AddSubgroup.mem_addSubgroupOf.1 x.2⟩,
          AddSubgroup.mem_addSubgroupOf.2 x.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have k1 : Nat.card (A.addSubgroupOf X) * A.relIndex X = Nat.card X :=
    (A.addSubgroupOf X).card_mul_index
  have k2 : Nat.card (X.addSubgroupOf A) * X.relIndex A = Nat.card A :=
    (X.addSubgroupOf A).card_mul_index
  have hpos : 0 < Nat.card (A.addSubgroupOf X) := Nat.card_pos
  have hApos : 0 < Nat.card A := Nat.card_pos
  have heq : A.relIndex X = X.relIndex A := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [k1, hc, k2, hcard]
  have hne : X.relIndex A ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at k2
    omega
  unfold genIndex
  rw [heq]
  exact div_self (by exact_mod_cast hne)

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PInvertibleProductRep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem InvertibleProductRep.mem_of_local {Ω : Type} [Field Ω] (B : Subring Ω) (Y : AddSubgroup Ω)
    (hY : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y) (z : Ω)
    (hz : ∀ m : Ideal B, m.IsMaximal → ∃ b : B, b ∉ m ∧ (b : Ω) * z ∈ Y) : z ∈ Y := by
  let A : Ideal B :=
    { carrier := {a : B | (a : Ω) * z ∈ Y}
      add_mem' := by
        intro a c ha hc
        show ((a + c : B) : Ω) * z ∈ Y
        push_cast
        rw [add_mul]
        exact Y.add_mem ha hc
      zero_mem' := by
        show ((0 : B) : Ω) * z ∈ Y
        simp
      smul_mem' := by
        intro c a ha
        show ((c * a : B) : Ω) * z ∈ Y
        push_cast
        rw [mul_assoc]
        exact hY c c.2 _ ha }
  by_cases hA : A = ⊤
  · have h1 : (1 : B) ∈ A := hA ▸ Submodule.mem_top
    have h2 : ((1 : B) : Ω) * z ∈ Y := h1
    simpa using h2
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal A hA
    obtain ⟨b, hb, hbz⟩ := hz m hm
    exact absurd (hle (show b ∈ A from hbz)) hb

theorem InvertibleProductRep.proof : InvertibleProductRep.Statement := by
  intro Ω _ B M N P η _ g h β δ β' δ' I J hβ hδ hβ' hδ' hM hN hP hloc x
  have hβΩ : (β : Ω) ≠ 0 := fun h0 => hβ (Subtype.ext (by rw [h0]; rfl))
  have hβ'Ω : (β' : Ω) ≠ 0 := fun h0 => hβ' (Subtype.ext (by rw [h0]; rfl))
  have hne : ((β * β' : B) : Ω) ≠ 0 := by push_cast; exact mul_ne_zero hβΩ hβ'Ω
  have notin : ∀ (m : Ideal B), m.IsMaximal → ∀ a b c : B, a ∉ m → b ∉ m → c ∉ m → a * b * c ∉ m := by
    intro m hm a b c ha hb hc h0
    rcases hm.isPrime.mem_or_mem h0 with h1 | h1
    · rcases hm.isPrime.mem_or_mem h1 with h2 | h2
      · exact ha h2
      · exact hb h2
    · exact hc h1
  constructor
  · intro hx
    let Y : AddSubgroup Ω :=
      { carrier := {w | ∃ y ∈ I * J, ((β * β' : B) : Ω) * w = ((δ * δ' : B) : Ω) * (y : Ω)}
        add_mem' := by
          rintro a c ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
          refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
          push_cast at e₁ e₂ ⊢
          linear_combination e₁ + e₂
        zero_mem' := ⟨0, zero_mem _, by simp⟩
        neg_mem' := by
          rintro a ⟨y, hy, e⟩
          refine ⟨-y, neg_mem hy, ?_⟩
          push_cast at e ⊢
          linear_combination -e }
    have hYst : ∀ b ∈ B, ∀ z ∈ Y, b * z ∈ Y := by
      rintro b hb z ⟨y, hy, e⟩
      refine ⟨⟨b, hb⟩ * y, (I * J).mul_mem_left _ hy, ?_⟩
      push_cast at e ⊢
      linear_combination b * e
    have key : x ∈ Y := by
      refine InvertibleProductRep.mem_of_local B Y hYst x fun m hm => ?_
      obtain ⟨i, ⟨⟨b₁, hb₁, hgM⟩, -⟩, ⟨⟨b₂, hb₂, hhN⟩, -⟩, ⟨-, hPz⟩⟩ := hloc m hm
      obtain ⟨b, c, hb, e⟩ := hPz x hx
      obtain ⟨u, hu, eu⟩ := (hM _).1 hgM
      obtain ⟨v, hv, ev⟩ := (hN _).1 hhN
      refine ⟨b₁ * b₂ * b, notin m hm _ _ _ hb₁ hb₂ hb, c * (u * v),
        (I * J).mul_mem_left _ (Ideal.mul_mem_mul hu hv), ?_⟩
      push_cast at e eu ev ⊢
      linear_combination ((β : Ω) * β' * b₁ * b₂) * e + ((c : Ω) * β' * b₂ * h i) * eu +
        ((c : Ω) * δ * u) * ev
    obtain ⟨y, hy, e⟩ := key
    exact ⟨y, hy, by push_cast at e ⊢; linear_combination e⟩
  · rintro ⟨y, hy, e⟩
    have claim : ∀ r ∈ I * J, ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P := by
      intro r hr
      refine Submodule.mul_induction_on
        (C := fun r : B => ((δ * δ' : B) : Ω) * (r : Ω) / ((β * β' : B) : Ω) ∈ P) hr ?_ ?_
      · intro u hu v hv
        have hp : (δ : Ω) * u / β ∈ M := (hM _).2 ⟨u, hu, by field_simp⟩
        have hq : (δ' : Ω) * v / β' ∈ N := (hN _).2 ⟨v, hv, by field_simp⟩
        have hpq : ((δ : Ω) * u / β) * ((δ' : Ω) * v / β') ∈ P := by
          refine InvertibleProductRep.mem_of_local B P hP _ fun m hm => ?_
          obtain ⟨i, ⟨-, hMz⟩, ⟨-, hNz⟩, ⟨⟨b'', hb'', hgh⟩, -⟩⟩ := hloc m hm
          obtain ⟨b, c, hb, e₁⟩ := hMz _ hp
          obtain ⟨b', c', hb', e₂⟩ := hNz _ hq
          refine ⟨b * b' * b'', notin m hm _ _ _ hb hb' hb'', ?_⟩
          have eq : ((b * b' * b'' : B) : Ω) * (((δ : Ω) * u / β) * ((δ' : Ω) * v / β')) =
              ((c * c' : B) : Ω) * ((b'' : Ω) * (g i * h i)) := by
            push_cast
            linear_combination ((b' : Ω) * b'' * ((δ' : Ω) * v / β')) * e₁ + ((c : Ω) * b'' * g i) * e₂
          rw [eq]
          exact hP _ (c * c').2 _ hgh
        have : ((δ * δ' : B) : Ω) * ((u * v : B) : Ω) / ((β * β' : B) : Ω) =
            ((δ : Ω) * u / β) * ((δ' : Ω) * v / β') := by
          push_cast
          field_simp
        rw [this]
        exact hpq
      · intro a c ha hc
        have : ((δ * δ' : B) : Ω) * ((a + c : B) : Ω) / ((β * β' : B) : Ω) =
            ((δ * δ' : B) : Ω) * (a : Ω) / ((β * β' : B) : Ω) +
              ((δ * δ' : B) : Ω) * (c : Ω) / ((β * β' : B) : Ω) := by
          push_cast
          ring
        rw [this]
        exact P.add_mem ha hc
    have hx : x = ((δ * δ' : B) : Ω) * (y : Ω) / ((β * β' : B) : Ω) := by
      rw [eq_div_iff hne]
      push_cast at e ⊢
      linear_combination e
    rw [hx]
    exact claim y hy

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLocalGenFamily
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem LocalGenFamily.proof : LocalGenFamily.Statement := by
  intro Ω _ B X η _ f hfin hX hf0 hc hloc
  have : Module.Finite ℤ B := hfin
  have : IsNoetherianRing B := IsNoetherianRing.of_finite ℤ B

  let K : η → Ideal B := fun i =>
    { carrier := {t : B | (t : Ω) * f i ∈ X}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subring.coe_add, add_mul] at ha hb ⊢
        exact X.add_mem ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]; exact X.zero_mem
      smul_mem' := fun c t ht => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at ht ⊢
        exact hX _ c.2 _ ht }
  have hK : ∀ i, ∀ t : B, t ∈ K i ↔ (t : Ω) * f i ∈ X := fun _ _ => Iff.rfl
  have hfg : ∀ i, ∃ T : Finset B, Ideal.span (T : Set B) = K i := fun i => IsNoetherian.noetherian (K i)
  choose T hT using hfg
  refine ⟨?_, Σ i : η, {t : B // t ∈ T i}, inferInstance, fun j => (j.2.1 : Ω) * f j.1, ?_, ?_, ?_⟩
  ·
    obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    obtain ⟨i, ⟨b, hbm, hbX⟩, -⟩ := hloc m hm
    have hb : (b : Ω) ≠ 0 := by
      intro h
      exact hbm (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)
    intro hbot
    rw [hbot, AddSubgroup.mem_bot] at hbX
    exact mul_ne_zero hb (hf0 i) hbX
  · rintro ⟨i, t, ht⟩
    rw [← hK, ← hT i]
    exact Ideal.subset_span ht
  · rintro ⟨i, t, -⟩
    obtain ⟨c, hcB, hc0, hcf⟩ := hc i
    refine ⟨c, hcB, hc0, ?_⟩
    rw [mul_left_comm]
    exact B.mul_mem t.2 hcf
  · intro m hm
    obtain ⟨i, ⟨b, hbm, hbX⟩, hall⟩ := hloc m hm
    have : ∃ t ∈ T i, t ∉ m := by
      by_contra hno
      push Not at hno
      have hle : K i ≤ m := by
        rw [← hT i, Ideal.span_le]
        exact fun t ht => hno t ht
      exact hbm (hle ((hK i b).2 hbX))
    obtain ⟨t, htT, htm⟩ := this
    refine ⟨⟨i, t, htT⟩, fun z hz => ?_⟩
    obtain ⟨b', c', hb'm, hbz⟩ := hall z hz
    refine ⟨t * b', c', fun h => ?_, ?_⟩
    · rcases hm.isPrime.mem_or_mem h with h | h
      · exact htm h
      · exact hb'm h
    · simp only [Subring.coe_mul]
      calc (t : Ω) * b' * z = t * (b' * z) := by ring
        _ = t * (c' * f i) := by rw [hbz]
        _ = c' * (t * f i) := by ring

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDehomogPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ChartDehomogPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime W → linForm t ∉ W → (W ⊔ Ideal.span {linForm t - 1}).IsPrime

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StLocalMultComap
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights (localMult)

def LocalMultComap.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (I W : Ideal S),
    Function.Surjective σ → W.IsPrime → localMult (I.comap σ) (W.comap σ) = localMult I W

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsBlockTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
    (L : Type) [Field L] [Algebra ℚ L] (φ : MRing ι' →+* L),
    IsBlockMap κ v → IsMultiProjPrime P' → RingHom.ker φ = P' →
      Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p)))) +
          ((Fintype.card K' - Fintype.card K : ℕ) : Cardinal) ≤
        Algebra.trdeg ℚ (Algebra.adjoin ℚ (Set.range fun q : Σ k', ι' k' ↦ φ (X q)))

section Examples

end Examples

end GroundTheory.Heights₂.Heights
end
end

