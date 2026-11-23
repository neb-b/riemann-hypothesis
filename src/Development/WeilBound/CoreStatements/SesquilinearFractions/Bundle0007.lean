module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.RestrictDiagCompInclFst
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DOkBasis
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.CurveZNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem curve_z_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (Z : Curve0 H ρ), Z.z ≠ 0 := by
  intro E _ _ _ H ρ Z hz
  obtain ⟨Hm, χ, Ef, -, -, hT2, -⟩ := Z.theta
  have hd : Z.u.IsDiff 0 Z.C'.v := by
    have h := Z.diff
    rw [hz, mul_zero] at h
    exact h
  have ht : IsTangent Z.C'.v := Z.C'.basis.1 0
  have h1 : IsTangent (1 : epsR ℂ ⟶ Z.C'.P.A) := (ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).1 ReciprocityTheory.ChartRestriction.G.Chart.isTan_one
  have hd1 : Z.u.IsDiff 0 (1 : epsR ℂ ⟶ Z.C'.P.A) := GlobalTheory.UnifDifferential.isDiff_one Z.u
  have e : Z.C'.v = 1 := (hT2 0).unique ⟨ht, hd⟩ ⟨h1, hd1⟩
  have hb := Z.C'.basis.2 Z.C'.v ht
  have c0 : IsLieComb ![(0 : ℂ)] ![Z.C'.v] Z.C'.v := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff, ReciprocityTheory.ChartRestriction.G.Chart.prodPts, e]
    simp
  have c1 : IsLieComb ![(1 : ℂ)] ![Z.C'.v] Z.C'.v := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff, ReciprocityTheory.ChartRestriction.G.Chart.prodPts]
    simp only [Matrix.cons_val_fin_one, ReciprocityTheory.ChartRestriction.G.Chart.scaleD_one, ReciprocityTheory.ChartRestriction.G.Chart.spMap_id,
      Category.id_comp, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
    exact (_root_.mul_one _).symm
  have h01 := congrFun (hb.unique c0 c1) 0
  simp at h01

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.DLocBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  intro E _ _ M _ _ _ _ I _ ℓ hℓ hcard
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order.locBasis' (𝓞 E) ℓ (M := M) hℓ
  let e : I ≃ Fin (Module.finrank (𝓞 E) M) := Fintype.equivFinOfCardEq hcard
  refine ⟨b ∘ e, hb.1.comp e e.injective, ?_⟩
  obtain ⟨n, hn, hsp⟩ := hb.2
  refine ⟨n, hn, fun y => ?_⟩
  have : Set.range (b ∘ e) = Set.range b := e.surjective.range_comp b
  rw [this]
  exact hsp y

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GOntoA
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.OntoKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
  {P : D.La →+ (Fin g → ℂ)}

theorem ty_eq_of_rt {i j : Fin g} (h : ty i (H.rt : E) = ty j (H.rt : E)) (α : OK H) :
    ty i ((α : 𝓞 E) : E) = ty j ((α : 𝓞 E) : E) := by
  have hw : ty i ((H.w0 : 𝓞 E) : E) = ty j ((H.w0 : 𝓞 E) : E) := by
    have e : (2 : E) * ((H.w0 : 𝓞 E) : E) = 1 + ((H.rt : 𝓞 E) : E) := by
      have e0 := congrArg (fun z : 𝓞 E => (z : E)) H.two_weight_eq_one_add_root
      push_cast at e0
      exact e0
    have hi := congrArg (ty i) e
    have hj := congrArg (ty j) e
    simp only [map_mul, map_add (f := _), map_one, map_ofNat] at hi hj
    have h2 : (2 : ℂ) * ty i ((H.w0 : 𝓞 E) : E) = 2 * ty j ((H.w0 : 𝓞 E) : E) := by
      rw [hi, hj, h]
    exact mul_left_cancel₀ two_ne_zero h2
  suffices hs : ∀ β ∈ OK H, ty i ((β : 𝓞 E) : E) = ty j ((β : 𝓞 E) : E) from hs _ α.2
  intro β hβ
  induction hβ using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx]
    exact hw
  | algebraMap r => simp
  | add x y _ _ hx hy =>
    push_cast
    rw [map_add (f := _), map_add (f := _), hx, hy]
  | mul x y _ _ hx hy =>
    push_cast
    rw [map_mul, map_mul, hx, hy]


open Classical in
def kap (ty : Fin g → (E →+* ℂ)) (H : Host E) (b : Bool) (α : OK H) : ℂ :=
  if h : ∃ i, ty i (H.rt : E) = sgnRt H b then ty h.choose ((α : 𝓞 E) : E) else 0

theorem P_smul (hP : IsPeriod D ty P) {b : Bool} (a : PureType.lat hP (sgnRt H b)) (α : OK H) :
    P ((α : 𝓞 E) • (a : D.La)) = kap ty H b α • P a := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul, hP.1]
  by_cases hi : ty i (H.rt : E) = sgnRt H b
  · have hex : ∃ i, ty i (H.rt : E) = sgnRt H b := ⟨i, hi⟩
    rw [kap, dite_eq_left hex, ty_eq_of_rt (hi.trans hex.choose_spec.symm) α]
  · have h0 : P (a : D.La) i = 0 := a.2 i hi
    rw [h0, mul_zero, mul_zero]

theorem span_top (hP : IsPeriod D ty P) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (N : ℕ)
    (hN0 : 0 < N) (hN : ∀ y : D.La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : D.La))) :
    Submodule.span ℂ (Set.range fun k => P (a k)) = ⊤ := by
  set W := Submodule.span ℂ (Set.range fun k => P (a k)) with hW
  have hmem : ∀ y, P y ∈ W := by
    intro y
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (OK H)).1 (hN y)
    have h1 : P (N • y) ∈ W := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc, map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [Subalgebra.smul_def, P_smul hP (a k) (c k)]
      exact W.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ] at h1
    have h2 := W.smul_mem ((N : ℂ)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN0.ne'), one_smul] at h2
  have hR : Submodule.span ℝ (Set.range P) ≤ W.restrictScalars ℝ :=
    Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hmem y)
  rw [eq_top_iff]
  intro z _
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by
    rw [hP.2.2.2.1]
    trivial
  exact hR hz

theorem exists_coeffs (hP : IsPeriod D ty P) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (N : ℕ)
    (hN0 : 0 < N) (hN : ∀ y : D.La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : D.La))) (z : Fin g → ℂ) :
    ∃ c : Fin g → ℂ, z = ∑ k, c k • P (a k) := by
  have hz : z ∈ Submodule.span ℂ (Set.range fun k => P (a k)) := by rw [span_top hP b a N hN0 hN]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hz
  exact ⟨c, hc.symm⟩

theorem linIndep (hP : IsPeriod D ty P) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (N : ℕ)
    (hN0 : 0 < N) (hN : ∀ y : D.La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : D.La))) :
    LinearIndependent ℂ fun k => P (a k) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [span_top hP b a N hN0 hN]
  · simp

theorem coeff_of_period (hP : IsPeriod D ty P) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (N : ℕ)
    (hN0 : 0 < N) (hN : ∀ y : D.La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : D.La)))
    (s : Fin g → ℂ) (y : D.La) (hs : ∑ k, s k • P (a k) = P y) :
    ∃ α : Fin g → OK H, ∀ k, (N : ℂ) * s k = kap ty H (b k) (α k) := by
  have hli := linIndep hP b a N hN0 hN
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (OK H)).1 (hN y)
  refine ⟨c, fun k => ?_⟩
  have e1 : ∑ k, ((N : ℂ) * s k) • P (a k) = (N : ℂ) • P y := by
    simp only [mul_smul, ← Finset.smul_sum, hs]
  have e2 : ∑ k, kap ty H (b k) (c k) • P (a k) = (N : ℂ) • P y := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ← hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Subalgebra.smul_def, P_smul hP (a k) (c k)]
  have hsum : ∑ k, ((N : ℂ) * s k - kap ty H (b k) (c k)) • P (a k) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, e1, e2, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ hsum k)

end PositivityTheory.Xgf.OntoKer

end
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GPartBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

open Module Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def pure_type_projection {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun := tyPart ty σ
  map_add' a b := by
    funext k
    simp only [tyPart, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c a := by
    funext k
    simp only [tyPart, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem typeProjection_apply {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (w : Fin g → ℂ) (k : Fin g) :
    pure_type_projection ty σ w k = if ty k = σ then w k else 0 := by
  simp [pure_type_projection, tyPart]

def typeSupportedVectors {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) : Submodule ℂ (Fin g → ℂ) where
  carrier := {w | ∀ k, ty k ≠ σ → w k = 0}
  add_mem' {a b} ha hb k hk := by simp [ha k hk, hb k hk]
  zero_mem' k _ := rfl
  smul_mem' c a ha k hk := by simp [ha k hk]

theorem mem_typeSupportedVectors_iff {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) (w : Fin g → ℂ) :
    w ∈ typeSupportedVectors ty σ ↔ tyPart ty σ w = w := by
  constructor
  · intro h
    funext k
    simp only [tyPart]
    split_ifs with hk
    · rfl
    · exact (h k hk).symm
  · intro h k hk
    rw [← h]
    simp [tyPart, hk]

def typeSupportedEquiv {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) :
    typeSupportedVectors ty σ ≃ₗ[ℂ] ({k // ty k = σ} → ℂ) where
  toFun v k := v.1 k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨fun k => if h : ty k = σ then f ⟨k, h⟩ else 0, fun k hk => by simp [hk]⟩
  left_inv v := by
    apply Subtype.ext
    funext k
    by_cases h : ty k = σ
    · simp [h]
    · simp only [h, dite_false]
      exact (v.2 k h).symm
  right_inv f := by
    funext k
    simp [k.2]

theorem finrank_typeSupportedVectors {g : ℕ} (ty : Fin g → (E →+* ℂ)) (σ : E →+* ℂ) :
    finrank ℂ (typeSupportedVectors ty σ) = Nat.card {k // ty k = σ} := by
  rw [(typeSupportedEquiv ty σ).finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem type_part_linear_independent (H : Host E) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ))
    (hP : IsPeriod D ty P) {k k' : ℕ} (y : Fin k → D.La) (z : Fin k' → D.La) (σ : E →+* ℂ)
    (hz : ∀ b, tyPart ty σ (P (z b)) = 0) (hcount : Nat.card {i // ty i = σ} = k)
    (hrk : k + k' = finrank (𝓞 E) D.La) (hli : LinearIndependent (𝓞 E) (Sum.elim y z)) :
    LinearIndependent ℂ (fun a => tyPart ty σ (P (y a))) ∧
      ∀ w : Fin g → ℂ, w ∈ Submodule.span ℂ (Set.range fun a => tyPart ty σ (P (y a))) ↔ tyPart ty σ w = w := by
  haveI := D.fin
  set T := pure_type_projection ty σ
  set S := Submodule.span ℂ (Set.range fun a => tyPart ty σ (P (y a)))
  have hT : ∀ w, T w = tyPart ty σ w := fun _ => rfl

  have hsmul : ∀ (s : 𝓞 E) (v : D.La), T (P (s • v)) = σ (s : E) • T (P v) := by
    intro s v
    funext i
    rw [typeProjection_apply, Pi.smul_apply, typeProjection_apply, smul_eq_mul]
    split_ifs with h
    · rw [hP.1, h]
    · simp

  have hmult : ∀ v : D.La, ∃ a : 𝓞 E, a ≠ 0 ∧ a • v ∈ Submodule.span (𝓞 E) (Set.range (Sum.elim y z)) := by
    intro v
    by_contra hne
    push_neg at hne
    have hli2 : LinearIndependent (𝓞 E) (fun o : Option (Fin k ⊕ Fin k') => o.elim v (Sum.elim y z)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      rw [Fintype.sum_option] at hc
      simp only [Option.elim] at hc
      have hcn : c none = 0 := by
        by_contra h0
        apply hne (c none) h0
        have : c none • v = -∑ i, c (some i) • Sum.elim y z i := eq_neg_of_add_eq_zero_left hc
        rw [this]
        exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
      rw [hcn, zero_smul, zero_add] at hc
      have := Fintype.linearIndependent_iff.mp hli (fun i => c (some i)) hc
      intro o
      cases o with
      | none => exact hcn
      | some i => exact this i
    have hc := hli2.fintype_card_le_finrank
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin] at hc
    omega

  have hspan : ∀ v ∈ Submodule.span (𝓞 E) (Set.range (Sum.elim y z)), T (P v) ∈ S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      cases i with
      | inl a => exact Submodule.subset_span ⟨a, rfl⟩
      | inr b =>
        simp only [Sum.elim_inr]
        rw [hT, hz b]
        exact S.zero_mem
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact S.add_mem hx hy
    | smul s x _ hx => rw [hsmul]; exact S.smul_mem _ hx
  have hall : ∀ v : D.La, T (P v) ∈ S := by
    intro v
    obtain ⟨a, ha, hav⟩ := hmult v
    have h1 := hspan _ hav
    rw [hsmul] at h1
    have hσ : σ (a : E) ≠ 0 := by
      rw [map_ne_zero]
      exact_mod_cast ha
    have := S.smul_mem (σ (a : E))⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hσ, one_smul] at this

  have hallC : ∀ w : Fin g → ℂ, T w ∈ S := by
    intro w
    have hw : w ∈ Submodule.span ℝ (Set.range P) := by rw [hP.2.2.2.1]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx => obtain ⟨v, rfl⟩ := hx; exact hall v
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
    | smul r x _ hx =>
      have : T (r • x) = (r : ℂ) • T x := by
        rw [← map_smul]
        congr 1
      rw [this]
      exact S.smul_mem _ hx
  have hSV : S = typeSupportedVectors ty σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, mem_typeSupportedVectors_iff]
      funext i
      simp only [tyPart]
      split_ifs <;> rfl
    · intro w hw
      rw [mem_typeSupportedVectors_iff] at hw
      rw [← hw]
      exact hallC w
  refine ⟨?_, fun w => by rw [hSV, mem_typeSupportedVectors_iff]⟩
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  change k = finrank ℂ S
  rw [hSV, finrank_typeSupportedVectors, hcount]

theorem Host_rt0_conj_eq_neg (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  apply Complex.ext
  · have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.natCast_re, Complex.neg_im,
      Complex.natCast_im, neg_zero] at h1 h2
    have hb : H.rt0.im ≠ 0 := by
      intro hb
      rw [hb] at h1
      nlinarith [sq_nonneg H.rt0.re]
    have ha : H.rt0.re = 0 := by
      have : 2 * H.rt0.re * H.rt0.im = 0 := by linarith
      rcases mul_eq_zero.mp this with h3 | h3
      · linarith
      · exact absurd h3 hb
    simp [ha]
  · simp

theorem Host_rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h1 := H.sqrt_neg_disc_sq
  rw [h] at h1
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  apply hd
  have h2 : -(H.d : ℂ) = 0 := by rw [← h1]; ring
  simpa using h2

theorem pure_type_projection_independent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (p q : ℕ) (x : Fin p ⊕ Fin q → D.La) (τ : E →+* ℂ), IsTypeFn H p q ty → p + q = D.p + D.q → τ (H.rt : E) = H.rt0 → IsPure hP x → LinearIndependent (𝓞 E) x → (LinearIndependent ℂ (fun a => tyPart ty τ (P (x (.inl a)))) ∧ ∀ w : Fin g → ℂ, w ∈ Submodule.span ℂ (Set.range fun a => tyPart ty τ (P (x (.inl a)))) ↔ tyPart ty τ w = w) ∧ LinearIndependent ℂ (fun a => tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr a)))) ∧ ∀ w : Fin g → ℂ, w ∈ Submodule.span ℂ (Set.range fun a => tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr a)))) ↔ tyPart ty (ComplexEmbedding.conjugate τ) w = w := by
  intro E _ _ _ H D g ty P hP p q x τ hty hpq hτ hpure hli
  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    apply Host_rt0_ne_zero H
    have : (2 : ℂ) * H.rt0 = 0 := by linear_combination h
    simpa using this
  have hcτ : (ComplexEmbedding.conjugate τ) (H.rt : E) = -H.rt0 := by
    rw [ComplexEmbedding.conjugate_coe_eq, hτ, Host_rt0_conj_eq_neg]
  have hrk : p + q = finrank (𝓞 E) D.La := by rw [hpq, D.rank]
  constructor
  · refine type_part_linear_independent H D ty P hP (fun a => x (.inl a)) (fun b => x (.inr b)) τ ?_ ((hty τ).1 hτ) hrk ?_
    · intro b
      funext i
      simp only [tyPart, Pi.zero_apply]
      split_ifs with h
      · apply hpure.2 b i
        rw [h, hτ]
        simp only [sgnRt, Bool.false_eq_true, if_false]
        exact hne
      · rfl
    · convert hli using 1
      funext o
      cases o <;> rfl
  · have hq : Nat.card {i // ty i = ComplexEmbedding.conjugate τ} = q := by
      apply ((hty _).2)
      rw [hcτ]
      exact hne.symm
    refine type_part_linear_independent H D ty P hP (fun b => x (.inr b)) (fun a => x (.inl a)) _ ?_ hq (by rw [← hrk, add_comm]) ?_
    · intro a
      funext i
      simp only [tyPart, Pi.zero_apply]
      split_ifs with h
      · apply hpure.1 a i
        rw [h, hcτ]
        simp only [sgnRt, if_true]
        exact hne.symm
      · rfl
    · have := hli.comp (Equiv.sumComm (Fin q) (Fin p)) (Equiv.injective _)
      convert this using 1
      funext o
      cases o <;> rfl

end PositivityTheory.Xgf

end
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.Models
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.cm_lie_model_action

open PositivityTheory.Xgf.isogeny_decomposition_product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}

theorem models (X : CMPack Z c FU i hP) :
    ∃ (M : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K)) (ρ : 𝓞 E →+* Module.End X.K (Fin g → X.K)),
      M.IsActOf Xo.univ.t.act.act ρ ∧
      ∃ (M1 : LieModel X.t.G (𝟙 (Sp X.K)) (Fin g → X.K))
        (M2 : LieModel X.B.t.G (𝟙 (Sp X.K) ≫ spMap (algebraMap (𝓞 X.K) X.K)) (Fin g → X.K)),
        (∀ e, (M1.pt e).left ≫ X.m.φ = (M.pt e).left) ∧ (∀ e, (M1.pt e).left ≫ X.m'.φ = (M2.pt e).left) := by
  obtain ⟨n, M, ρ, hρ, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Ggeo.lieModel_coordinates_baseChange E H Xo.X Xo.univ.t X.K (under X.y)
  have h1 : under X.y = 𝟙 (Sp X.K) ≫ under X.y := by simp
  obtain ⟨M1, hM1⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback Xo.X (Sp X.K) Xo.univ.t.G X.t.G (under X.y) X.m.φ X.m.cart X.K (𝟙 _)
    (Fin n → X.K)).1 (castM h1 M)
  obtain ⟨M2, hM2⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback (Sp (𝓞 X.K)) (Sp X.K) X.B.t.G X.t.G (spMap (algebraMap (𝓞 X.K) X.K)) X.m'.φ
    X.m'.cart X.K (𝟙 _) (Fin n → X.K)).2 M1
  obtain ⟨bas⟩ := _root_.PositivityTheory.UnitarySelfGeneration.lie_free (Sp (𝓞 X.K)) X.B.t.G g (by have hd := X.B.dim; rwa [X.dim] at hd) X.K
    (𝟙 (Sp X.K) ≫ spMap (algebraMap (𝓞 X.K) X.K)) (Fin n → X.K) M2
  have hn : n = g := by
    have := Module.finrank_eq_card_basis bas
    simpa using this
  subst hn
  exact ⟨M, ρ, hρ, M1, M2, fun e => (hM1 e).trans (castM_left h1 M e), hM2⟩

end PositivityTheory.Xgf.cm_lie_model_action

end
end

