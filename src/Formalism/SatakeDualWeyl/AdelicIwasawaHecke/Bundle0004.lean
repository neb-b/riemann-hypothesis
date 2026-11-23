module

public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitA
section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

namespace Formalism.UG.P
open Formalism.UG

section Adele
variable {F : Type} [Field F] [NumberField F]

theorem afsplit_add_apply (a b : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) : (a + b) w = a w + b w := rfl
theorem afsplit_mul_apply (a b : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) : (a * b) w = a w * b w := rfl
theorem afsplit_sub_apply (a b : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := rfl
theorem afsplit_one_apply (w : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸ᶠ[F]) w = 1 := rfl
theorem afsplit_zero_apply (w : HeightOneSpectrum (𝓞 F)) : (0 : 𝔸ᶠ[F]) w = 0 := rfl
theorem afsplit_smul_apply (c : F) (a : 𝔸ᶠ[F]) (w : HeightOneSpectrum (𝓞 F)) :
    (c • a) w = c • a w := by
  rw [Algebra.smul_def, afsplit_mul_apply, Algebra.smul_def]; rfl

def afsplitF (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : 𝔸ᶠ[F] := by
  classical
  exact ⟨Pi.single v x, by
    filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) ∈ Filter.cofinite by simp] with w hw
    rw [Set.mem_compl_singleton_iff] at hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _⟩

theorem afsplitF_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : afsplitF v x v = x := by
  classical
  show Pi.single v x v = x
  convert Pi.single_eq_same v x

theorem afsplitF_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) :
    afsplitF v x w = 0 := by
  classical
  show Pi.single v x w = 0
  convert Pi.single_eq_of_ne h x

def afsplitI (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →ₗ[F] 𝔸ᶠ[F] where
  toFun := afsplitF v
  map_add' x y := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_add_apply, afsplitF_self]
    · simp only [afsplit_add_apply, afsplitF_ne v w h, add_zero]
  map_smul' c x := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_smul_apply, afsplitF_self, RingHom.id_apply]
    · simp only [afsplit_smul_apply, afsplitF_ne v w h, smul_zero, RingHom.id_apply]

theorem afsplitI_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : afsplitI v x v = x :=
  afsplitF_self v x

theorem afsplitI_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) :
    afsplitI v x w = 0 := afsplitF_ne v w h x

theorem afsplitI_mul (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F) :
    afsplitI v (x * y) = afsplitI v x * afsplitI v y := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, mul_zero]

theorem afsplitI_eval (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸ᶠ[F]) :
    afsplitI v (a v) = afsplitI v 1 * a := by
  ext w
  by_cases h : w = v
  · subst h; simp only [afsplit_mul_apply, afsplitI_self, one_mul]
  · simp only [afsplit_mul_apply, afsplitI_ne v w h, zero_mul]

theorem afsplitI_mem_intAd (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : afsplitI v x ∈ intAd F := by
  intro w
  by_cases h : w = v
  · subst h; rw [afsplitI_self]; exact hx
  · rw [afsplitI_ne v w h]; exact zero_mem _

end Adele
end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA
section
open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem fSatake_nontriv {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) :
    (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial := by
  obtain ⟨-, -, -, hv, -⟩ := hU
  refine ⟨ϖ, ?_, ?_⟩
  · rw [hv]; exact WithZero.coe_ne_zero
  · rw [hv]
    intro h1
    have := WithZero.coe_injective (h1.trans WithZero.coe_one.symm)
    exact absurd (Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)) (by norm_num)

theorem isCommensurated_integral_unitary_of_unramified {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    IsCommensurated (KU σ n) := by
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    fSatake_nontriv hU
  obtain ⟨-, -, -, hvϖ, -, hq2, hq⟩ := hU
  set A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring with hA
  haveI : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
    isCyclic_of_surjective (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).symm.toMonoidHom
      (MulEquiv.surjective _)
  haveI hD : IsDiscreteValuationRing ↥A.toSubring := Valuation.valuationSubring_isDiscreteValuationRing _
  have hRes : Finite (IsLocalRing.ResidueField ↥A.toSubring) := by
    apply Nat.finite_of_card_ne_zero
    rw [show Nat.card (IsLocalRing.ResidueField ↥A.toSubring) = q ^ 2 from hq]
    exact pow_ne_zero 2 (by omega)
  intro g
  obtain ⟨c, hc0, hg1, hg2⟩ := Formalism.UG.P.glint_exists_denom A (g : GL (Fin n) L)
  haveI : Finite (↥A.toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hRes _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact mul_ne_zero hc0 hc0)
  have hO : intL L = A.toSubring := rfl
  unfold KU
  rw [hO]
  have hK : intPts A.toSubring.subtype (GU σ n) = GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range := rfl
  rw [hK]
  have hmap : ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).subgroupOf (GU σ n)).map (MulAut.conj g).toMonoidHom =
      ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom).subgroupOf (GU σ n) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy.1⟩, hy, Subtype.ext (by simpa using hyx)⟩
  rw [hmap, Subgroup.relIndex_subgroupOf inf_le_left]
  have hPB := glint_princ_relIndex_ne_zero (n := Fin n) A.toSubring (Ideal.span {c * c})
  have h1 : (princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n).relIndex
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range) ≠ 0 := by
    rw [inf_comm (GU σ n) (bc (n := Fin n) A.toSubring.subtype).range]
    exact Subgroup.relIndex_inter_ne_zero hPB (GU σ n)
  have hle : princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n ≤
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom := by
    rintro h ⟨hP, hHh⟩
    obtain ⟨b, hb, hbh⟩ := glint_princ_le_map_conj A.toSubring (g : GL (Fin n) L) c hg1 hg2 hP
    refine ⟨b, ⟨?_, hb⟩, hbh⟩
    have hbe : b = (g : GL (Fin n) L)⁻¹ * h * g := by
      rw [← hbh]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hbe]
    exact (GU σ n).mul_mem ((GU σ n).mul_mem ((GU σ n).inv_mem g.2) hHh) g.2
  exact fun hz => h1 (Subgroup.relIndex_eq_zero_of_le_left hle hz)

theorem fSatake_v_eq {x : L} (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  unfold ordL
  rw [dite_eq_right h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

private lemma ordL_eq_of_valuation_eq {x : L} (hx : x ≠ 0) {k : ℤ}
    (h : Valued.v x = ((Multiplicative.ofAdd (-k) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ordL x = k := by
  rw [fSatake_v_eq hx] at h
  have h2 := WithZero.coe_injective h
  have h3 := Multiplicative.ofAdd.injective h2
  linarith

theorem fSatake_ord_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  apply ordL_eq_of_valuation_eq (mul_ne_zero hx hy)
  rw [map_mul, fSatake_v_eq hx, fSatake_v_eq hy, ← WithZero.coe_mul, ← ofAdd_add, neg_add]

theorem fSatake_ord_one : ordL (1 : L) = 0 := by
  apply ordL_eq_of_valuation_eq one_ne_zero
  simp

theorem fSatake_ord_of_v {x y : L} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

theorem fSatake_ord_zpow {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (k : ℤ) : ordL (ϖ ^ k) = k := by
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  apply ordL_eq_of_valuation_eq (zpow_ne_zero k h0)
  rw [map_zpow₀, hϖ, ← WithZero.coe_zpow, ← ofAdd_zsmul]
  congr 2
  simp

theorem fSatake_ord_nonneg {x : L} (hx : x ≠ 0) (hO : x ∈ intL L) : 0 ≤ ordL x := by
  have h1 : Valued.v x ≤ 1 := hO
  rw [fSatake_v_eq hx, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_le] at h1
  linarith

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeAssoc
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G] (K : Subgroup G)

theorem out_smul_out (h : G) (z : G ⧸ K) : ∃ c : K, (h • z : G ⧸ K).out = h * z.out * c := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (h * z.out)
  refine ⟨c, ?_⟩
  have e : (h • z : G ⧸ K) = ((h * z.out : G) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' z]
    rfl
  rw [e, hc]

theorem conv_assoc (hK : IsCommensurated K) {k : Type} [CommRing k] (f₁ f₂ f₃ : G → k)
    (h₁ : FinDosetSupp K f₁) (h₂ : IsBiInv K f₂) (h₃ : IsBiInv K f₃) (h₃' : FinDosetSupp K f₃) :
    conv K (conv K f₁ f₂) f₃ = conv K f₁ (conv K f₂ f₃) := by
  classical
  funext g
  have hA := finite_supp_translate (K := K) hK f₁ h₁ 1
  have hB := finite_supp_inv (K := K) hK f₃ h₃' g
  have sA : ∀ x : G ⧸ K, x ∉ hA.toFinset → f₁ x.out = 0 := by
    intro x hx
    simpa using hx
  have sB : ∀ y : G ⧸ K, y ∉ hB.toFinset → f₃ (y.out⁻¹ * g) = 0 := by
    intro y hy
    simpa using hy
  generalize hA.toFinset = A at sA
  generalize hB.toFinset = B at sB

  have key : ∀ x z : G ⧸ K, f₂ z.out * f₃ (z.out⁻¹ * (x.out⁻¹ * g)) =
      f₂ (x.out⁻¹ * (x.out • z).out) * f₃ ((x.out • z).out⁻¹ * g) := by
    intro x z
    obtain ⟨c, hc⟩ := out_smul_out K x.out z
    rw [hc]
    have e2 : x.out⁻¹ * (x.out * z.out * c) = ((1 : K) : G) * z.out * c := by
      simp [mul_assoc]
    have e3 : (x.out * z.out * c)⁻¹ * g =
        ((c⁻¹ : K) : G) * (z.out⁻¹ * (x.out⁻¹ * g)) * ((1 : K) : G) := by
      simp [mul_assoc]
    rw [e2, e3, h₂, h₃]
  have inner : ∀ x : G ⧸ K, conv K f₂ f₃ (x.out⁻¹ * g) =
      ∑ y ∈ B, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    intro x
    calc conv K f₂ f₃ (x.out⁻¹ * g)
        = ∑ᶠ z : G ⧸ K, f₂ z.out * f₃ (z.out⁻¹ * (x.out⁻¹ * g)) := rfl
      _ = ∑ᶠ z : G ⧸ K, (fun y : G ⧸ K => f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g))
            (MulAction.toPerm x.out z) := finsum_congr (fun z => key x z)
      _ = ∑ᶠ y : G ⧸ K, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) :=
            finsum_comp_equiv (MulAction.toPerm x.out : G ⧸ K ≃ G ⧸ K)
              (f := fun y : G ⧸ K => f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g))
      _ = ∑ y ∈ B, f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
        apply finsum_eq_sum_of_support_subset
        intro y hy
        by_contra h
        exact (Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])
  have L : conv K (conv K f₁ f₂) f₃ g =
      ∑ y ∈ B, ∑ x ∈ A, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    rw [show conv K (conv K f₁ f₂) f₃ g =
      ∑ᶠ y : G ⧸ K, (∑ᶠ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * y.out)) * f₃ (y.out⁻¹ * g) from rfl]
    rw [finsum_eq_sum_of_support_subset _ (s := B) ?_]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [finsum_eq_sum_of_support_subset _ (s := A) ?_, Finset.sum_mul]
      intro x hx
      by_contra h
      exact (Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])
    · intro y hy
      by_contra h
      exact (Function.mem_support.mp hy) (by rw [sB y (by simpa using h), mul_zero])
  have R : conv K f₁ (conv K f₂ f₃) g =
      ∑ x ∈ A, ∑ y ∈ B, f₁ x.out * f₂ (x.out⁻¹ * y.out) * f₃ (y.out⁻¹ * g) := by
    rw [show conv K f₁ (conv K f₂ f₃) g = ∑ᶠ x : G ⧸ K, f₁ x.out * conv K f₂ f₃ (x.out⁻¹ * g) from rfl]
    rw [finsum_eq_sum_of_support_subset _ (s := A) ?_]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [inner x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    · intro x hx
      by_contra h
      exact (Function.mem_support.mp hx) (by rw [sA x (by simpa using h), zero_mul])
  rw [L, R, Finset.sum_comm]

theorem hecke_assoc : Formalism.UG.HeckeAssoc := by
  intro G _ K k _ hK f₁ hf₁ f₂ hf₂ f₃ hf₃
  exact conv_assoc K hK f₁ f₂ f₃ hf₁.2 hf₂.1 hf₃.1 hf₃.2

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds
section
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem conv_mul_right {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₂ : IsBiInv K f₂) (g : G) (b : K) : conv K f₁ f₂ (g * b) = conv K f₁ f₂ g := by
  unfold conv
  congr 1
  funext x
  have h := hf₂ 1 b (x.out⁻¹ * g)
  simp only [OneMemClass.coe_one, one_mul] at h
  rw [← mul_assoc, h]

theorem conv_mul_left {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) (a : K) (g : G) :
    conv K f₁ f₂ ((a : G) * g) = conv K f₁ f₂ g := by
  have key : ∀ y : G ⧸ K, ∃ c : K, ((a : G) • y).out = (a : G) * y.out * c := by
    intro y
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * y.out)
    refine ⟨c, ?_⟩
    have e : (a : G) • y = (QuotientGroup.mk ((a : G) * y.out) : G ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [e, hc]
  unfold conv
  refine (finsum_comp_equiv (MulAction.toPerm (a : G) : Equiv.Perm (G ⧸ K))).symm.trans ?_
  congr 1
  funext y
  obtain ⟨c, hc⟩ := key y
  simp only [MulAction.toPerm_apply]
  rw [hc, hf₁ a c y.out]
  have e2 : ((a : G) * y.out * c)⁻¹ * ((a : G) * g) = ((c⁻¹ : K) : G) * (y.out⁻¹ * g) * ((1 : K) : G) := by
    simp only [InvMemClass.coe_inv, OneMemClass.coe_one, mul_one]
    group
  rw [e2, hf₂]

theorem conv_biInv {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : IsBiInv K (conv K f₁ f₂) := by
  intro a b g
  rw [conv_mul_right K f₁ f₂ hf₂ ((a : G) * g) b, conv_mul_left K f₁ f₂ hf₁ hf₂ a g]

theorem conv_finDosetSupp {k : Type} [CommRing k] {K : Subgroup G} (hK : IsCommensurated K)
    (f₁ f₂ : G → k) (hs₁ : FinDosetSupp K f₁) (hs₂ : FinDosetSupp K f₂) :
    FinDosetSupp K (conv K f₁ f₂) := by
  classical
  have hX := finite_support_cosets hK hs₁
  obtain ⟨S₂, hS₂⟩ := hs₂
  set T : Set G := ⋃ t ∈ (S₂ : Set G), ⋃ x ∈ {x : G ⧸ K | f₁ x.out ≠ 0},
    ⋃ y ∈ {y : G ⧸ K | ∃ a b : K, y.out = (a : G) * t * b}, {x.out * y.out} with hTdef
  have hT : T.Finite :=
    S₂.finite_toSet.biUnion fun t _ => hX.biUnion fun x _ =>
      (finite_cosets_in_doset hK t).biUnion fun y _ => Set.finite_singleton _
  refine ⟨hT.toFinset, fun g hg => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg (finsum_eq_zero_of_forall_eq_zero h)
  have h1 : f₁ x.out ≠ 0 := left_ne_zero_of_mul hx
  have h2 : f₂ (x.out⁻¹ * g) ≠ 0 := right_ne_zero_of_mul hx
  obtain ⟨t, ht, a, b, hab⟩ := hS₂ _ h2
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * t)
  refine ⟨x.out * (QuotientGroup.mk ((a : G) * t) : G ⧸ K).out, ?_, 1, c⁻¹ * b, ?_⟩
  · rw [Set.Finite.mem_toFinset, hTdef]
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨t, ht, x, h1, _, ⟨a, c, hc⟩, rfl⟩
  · rw [hc]
    have e : g = x.out * (x.out⁻¹ * g) := by group
    rw [e, hab]
    simp only [OneMemClass.coe_one, one_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
    group

theorem hecke_convolution_mem_holds : Formalism.UG.HeckeConvMem := by
  intro G _ K k _ hK f₁ hf₁ f₂ hf₂
  have h1 : IsBiInv K f₁ ∧ FinDosetSupp K f₁ := hf₁
  have h2 : IsBiInv K f₂ ∧ FinDosetSupp K f₂ := hf₂
  show IsBiInv K (conv K f₁ f₂) ∧ FinDosetSupp K (conv K f₁ f₂)
  exact ⟨conv_biInv K f₁ f₂ h1.1 h2.1, conv_finDosetSupp hK f₁ f₂ h1.2 h2.2⟩

theorem convolution_count_holds : Formalism.UG.ConvCount := by
  classical
  intro G _ K k _ hK a b g
  set S : Set (G ⧸ K) := {x : G ⧸ K | x.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ∧
    x.out⁻¹ * g ∈ DoubleCoset.doubleCoset b (K : Set G) K} with hSdef
  have hfin : S.Finite := by
    refine (finite_cosets_in_doset hK a).subset fun x hx => ?_
    obtain ⟨h, hh, c, hc, e⟩ := DoubleCoset.mem_doubleCoset.1 hx.1
    exact ⟨⟨h, hh⟩, ⟨c, hc⟩, e⟩
  have hterm : ∀ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) =
      if x ∈ S then 1 else 0 := by
    intro x
    simp only [dosetInd, Set.indicator_apply, Pi.one_apply, hSdef, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  show ∑ᶠ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) = _
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [Finset.sum_congr rfl (fun x hx => if_pos (hfin.mem_toFinset.1 hx))]
    simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hx (if_neg h)

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LevelSubgroupFiniteAdelicStandard
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Lattice

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E] {n : Type} [Fintype n]
  [DecidableEq n] (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)

theorem easyc_inclE_mem (e : E) (he : e ∈ intOE E) :
    inclE (F := F) R e ∈ tensInt (F := F) R (intOE E) S₂ := by
  apply Subring.subset_closure
  left
  exact ⟨⟨e, he⟩, rfl⟩

theorem easyc_single_mem (i : n) :
    (Pi.single i (1 : E) : n → E) ∈ stdLat (n := n) (A := E) (𝓞 E) := by
  rw [mem_stdLat_iff']
  intro k
  by_cases hk : k = i
  · subst hk; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [hk]⟩

theorem easyc_latS_std :
    latS (F := F) R (tensInt (F := F) R (intOE E) S₂) (stdLat (n := n) (A := E) (𝓞 E)) =
      stdLat (n := n) (A := E ⊗[F] R) ↥(tensInt (F := F) R (intOE E) S₂) := by
  apply le_antisymm
  · rw [latS, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_stdLat_iff']
    intro i
    have hxi := (mem_stdLat_iff' (R := 𝓞 E) x).1 hx i
    have hm : x i ∈ intOE E := by
      obtain ⟨y, hy⟩ := hxi
      exact ⟨y, hy⟩
    exact ⟨⟨_, easyc_inclE_mem R S₂ (x i) hm⟩, rfl⟩
  · intro x hx
    rw [mem_stdLat_iff'] at hx
    choose s hs using hx
    have hx : x = ∑ i, s i • (fun j => inclE (F := F) R ((Pi.single i (1 : E) : n → E) j)) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single j]
      · simp [← hs j, Algebra.smul_def]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hx]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨_, easyc_single_mem i, rfl⟩

end Lattice

theorem level_subgroup_finite_adelic_standard : Formalism.UG.LevelAfLStd := by
  intro F E _ _ _ _ _ n _ _ σ J
  unfold levelAfL levelAf
  rw [easyc_latS_std]

end Formalism.UG.P
end
end

