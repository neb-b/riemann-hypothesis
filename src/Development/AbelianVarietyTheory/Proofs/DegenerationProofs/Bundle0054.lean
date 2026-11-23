module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuadraticMapNonnegOfTendstoCofinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

theorem quadraticMap_nonneg_of_tendsto_cofinite {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (q : QuadraticMap ℤ X ℝ) (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (x : X) : 0 ≤ q x := by
  by_contra hneg
  push_neg at hneg
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hneg
  have hinj : Function.Injective (fun n : ℤ => n • x) := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨n, hn⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul, Int.cast_mul] at hn
  nlinarith [mul_self_nonneg (n : ℝ)]

namespace RatModel
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem dotProduct_div_mem_O {J : Type} [Fintype J] {a₀ : M.Z} {v e : J → Ω} {t : Ω}
    (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) : (v ⬝ᵥ e) / t ∈ M.O a₀ := by
  rw [div_eq_mul_inv]
  exact mul_mem (sum_mem fun j _ => mul_mem (hv j) (he j)) ht

theorem val_dotProduct_div {K : Type} [Field K] {y : Sp K ⟶ M.Z} {a₀ : M.Z} (h : ∀ w, y w ⤳ a₀)
    {J : Type} [Fintype J] {v e : J → Ω} {t : Ω} (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀)
    (ht0 : t ≠ 0) (ht' : t ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) :
    M.val y ((v ⬝ᵥ e) / t) = (∑ j, M.val y (v j) * M.val y (e j)) / M.val y t := by
  have h1 : M.val y t * M.val y t⁻¹ = 1 := by
    rw [← val_mul h ht' ht, mul_inv_cancel₀ ht0, val_one]
  have h2 : ∀ s : Finset J, M.val y (∑ j ∈ s, v j * e j) = ∑ j ∈ s, M.val y (v j) * M.val y (e j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [val_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        val_add h (mul_mem (hv a) (he a)) (sum_mem fun j _ => mul_mem (hv j) (he j)),
        val_mul h (hv a) (he a), ih]
  rw [div_eq_mul_inv, div_eq_mul_inv, dotProduct,
    val_mul h (sum_mem fun j _ => mul_mem (hv j) (he j)) ht, h2, eq_inv_of_mul_eq_one_right h1]

end RatModel

namespace ThetaSys
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem Test.norm_pair_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {h : S.Gam} (hh : h ∈ τ.yy.ker) {u : S.J → PadicAlgCl p} (hu : u ∈ τ.E) :
    ‖∑ j, u j * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, l, i, hα, hl, rfl⟩ := hu
    have h1 := τ.le α hα h hh i
    simp only [_root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ Real.exp (τ.q α / S.N) * (τ.δ * Real.exp (-(τ.q α / S.N))) :=
          mul_le_mul hl h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = τ.δ := by rw [Real.exp_neg]; field_simp
  | zero => simpa using τ.δ_pos.le
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  | smul c a _ ha =>
    have hc : ‖(c : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 c.2
    have : ∀ j, (c • a) j = (c : PadicAlgCl p) * a j := fun j => rfl
    simp only [this, _root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ 1 * τ.δ := mul_le_mul hc ha (norm_nonneg _) zero_le_one
      _ = τ.δ := _root_.one_mul _

theorem Test.norm_proj_zero_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) (i : S.J) :
    ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  subst hT
  have := τ.le 0 (fun v0 => by
    rw [map_zero]; exact quadraticMap_nonneg_of_tendsto_cofinite τ.q τ.pos _) h hh i
  simpa only [map_zero, zero_div, neg_zero, Real.exp_zero, _root_.mul_one] using this

theorem Test.exists_norm_proj_zero_eq {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) :
    ∃ i, ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ = τ.δ := by
  subst hT
  have := τ.unit0 h hh
  simpa only [map_zero] using this

theorem val_pair_div {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {U : Set M.Z}
    (hU : U ⊆ U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U z y)
    {y₀ : S.R →+* PadicAlgCl p} (hat : S.At M y y₀) {v : S.J → Ω} (hv : ∀ j, v j ∈ M.ringOn U)
    (h : S.Gam) {x₀ : S.Gam} (hx : S.th x₀ ≠ 0) :
    M.val (gPt p ≫ y) ((v ⬝ᵥ S.ev h) / S.th x₀) =
      (∑ j, M.val (gPt p ≫ y) (v j) * y₀ ⟨S.ev h j, S.ev_mem h j⟩) / M.val (gPt p ≫ y) (S.th x₀) := by
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hζ : (gPt p ≫ y) w ∈ U := hc.2 ⟨w, rfl⟩
  have hs := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (gPt p ≫ y) w)
  rw [RatModel.val_dotProduct_div hs (fun j => RatModel.ringOn_le_O hζ (hv j))
    (fun j => RatModel.ringOn_le_O (hU hζ) (hO.le (S.ev_mem h j))) hx
    (RatModel.ringOn_le_O (hU hζ) (hO.le (S.th_mem x₀)))
    (RatModel.ringOn_le_O (hU hζ) (hO.th_unit x₀ hx))]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hat]

end ThetaSys

theorem coord_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → S.IsEE M U₀ EE → ∀ ξ : M.Z, ∀ x₀ ∈ S.supI M ξ, ∀ h ∈ S.HH M ξ, (∀ v ∈ EE.E ξ, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O ξ) ∧ ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧ S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O ξ := by
  intro o Ω _ _ _ _ S M U₀ EE hO hLL hT hsup hstr hEE
  have closed : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ x₀ ∈ S.supI M z, ∀ h ∈ S.HH M z,
      (∀ v ∈ EE.E z, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z) ∧
      ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧
        S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O z := by
    intro z hz x₀ hx₀ h hh
    have hx : S.th x₀ ≠ 0 := hx₀.1
    refine ⟨fun v hv => ?_, ?_⟩
    · let V : M.Z.Opens := ⟨⋂ j, {a | v j ∈ M.O a}, isOpen_iInter_of_finite fun j => M.isOpen_setOf_mem_O _⟩
      have hV : (V : Set M.Z).Nonempty := ⟨genericPoint M.Z, Set.mem_iInter.2 fun j => by
        simp only [Set.mem_setOf_eq, M.O_genericPoint]; trivial⟩
      have hvV : ∀ j, v j ∈ M.ringOn ((U₀ ⊓ V : M.Z.Opens) : Set M.Z) := fun j =>
        RatModel.mem_ringOn.2 fun a ha => Set.mem_iInter.1 ha.2 j
      refine (hLL.1 (U₀ ⊓ V) inf_le_left (M.nonempty_inf hO.ne hV) z hz).2 _ ?_ ?_
      · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
          (fun j => RatModel.ringOn_le_O ha (hvV j))
          (fun j => RatModel.ringOn_le_O ha.1 (hO.le (S.ev_mem h j)))
          (RatModel.ringOn_le_O ha.1 (hO.th_unit x₀ hx))
      · intro p _ y hc
        have hc0 : M.Cen U₀ z y := ⟨hc.1, fun a ha => (hc.2 ha).1⟩
        obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc0
        obtain ⟨h1, h2⟩ := hsup z p y y₀ τ hc0 hat
        rw [ThetaSys.val_pair_div hO (fun (a : M.Z) (ha : a ∈ (U₀ ⊓ V : M.Z.Opens)) => ha.1) hc hat hvV h hx, norm_div, (h1 x₀).1 hx₀,
          div_le_one τ.δ_pos]
        refine τ.norm_pair_le (h2 ▸ hh) (u := fun j => M.val (gPt p ≫ y) (v j)) ?_
        rw [← hEE.2 z p y y₀ τ hc0 hat]
        exact Submodule.subset_span ⟨v, hv, rfl⟩
    · have hw : ∀ i j, algebraMap o Ω (S.proj (S.TT M z) 0 j i) ∈ M.ringOn (U₀ : Set M.Z) :=
        fun i j => Subalgebra.algebraMap_mem _ _
      have hval : ∀ i (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p)
          (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ →
          ‖M.val (gPt p ≫ y) (((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀)‖ =
            ‖∑ j, y₀ (algebraMap o S.R (S.proj (S.TT M z) 0 j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ / τ.δ := by
        intro i p _ y y₀ τ hc hat
        rw [ThetaSys.val_pair_div hO subset_rfl hc hat (hw i) h hx, norm_div,
          ((hsup z p y y₀ τ hc hat).1 x₀).1 hx₀]
        congr 2
        exact Finset.sum_congr rfl fun j _ => by rw [hat (algebraMap o S.R _)]; rfl
      have hmem : ∀ i, ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z := by
        intro i
        refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ ?_
        · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
            (fun j => RatModel.ringOn_le_O ha (hw i j))
            (fun j => RatModel.ringOn_le_O ha (hO.le (S.ev_mem h j)))
            (RatModel.ringOn_le_O ha (hO.th_unit x₀ hx))
        · intro p _ y hc
          obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
          have h2 := (hsup z p y y₀ τ hc hat).2
          rw [hval i p y y₀ τ hc hat, div_le_one τ.δ_pos]
          exact τ.norm_proj_zero_le (by rw [← h2]; rfl) (h2 ▸ hh) i
      obtain ⟨p, _, y, hc⟩ := (hLL.1 U₀ le_rfl hO.ne z hz).1
      obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
      have h2 := (hsup z p y y₀ τ hc hat).2
      obtain ⟨i, hi⟩ := τ.exists_norm_proj_zero_eq (T := S.TT M z) (by rw [← h2]; rfl) (h2 ▸ hh)
      have h3 := hval i p y y₀ τ hc hat
      rw [hi, div_self τ.δ_pos.ne', RatModel.norm_val_eq_one_iff hc.1 (hmem i), RatModel.isUnit_O_iff] at h3
      refine ⟨i, fun h0 => h3.1 (by simp only [h0, zero_div]), ?_⟩
      simpa only [inv_div] using h3.2
  intro ξ x₀ hx₀ h hh
  obtain ⟨U, b, hξU, -, hb⟩ := EE.loc ξ
  obtain ⟨x, hxU, hxc, hsp, hI⟩ := hstr.2.2.2 ξ U hξU
  have hH : S.HH M x = S.HH M ξ := by simp only [ThetaSys.HH, hI]
  have hTT : S.TT M x = S.TT M ξ := by simp only [ThetaSys.TT, hH]
  obtain ⟨c1, c2⟩ := closed x hxc x₀ (hI ▸ hx₀) h (hH ▸ hh)
  have hle := RatModel.O_le_of_specializes hsp
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [hb ξ hξU] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hle (c1 v (by rw [hb x hxU]; exact Submodule.subset_span hv))
    | zero => simp
    | add a c _ _ ha hc => rw [add_dotProduct, add_div]; exact add_mem ha hc
    | smul c a _ ha =>
      have : c • a = (c : Ω) • a := rfl
      rw [this, smul_dotProduct, smul_eq_mul, mul_div_assoc]
      exact mul_mem c.2 ha
  · rw [hTT] at c2
    obtain ⟨i, h1, h2⟩ := c2
    exact ⟨i, h1, hle h2⟩

end GlobalTheory.ZH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableOfPotentialSemiAbelianModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem semistable_of_potModel_semiAbelian : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G)) → SemistableReductionZero ∧ SemistableCompleteSplit := by
  intro h
  refine ⟨?_, ?_⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      _root_.GlobalTheory.SS.exists_semiAbelian_model_torusExtension_of_potModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i8, i9, i10, h1, h2, h3, G, i11,
      hG.comm, hG.smooth, hG.separated, hG.quasiCompact, he, GlobalTheory.SplitExtTorus.nonempty_torusExt_of_split _ _ hT⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      _root_.GlobalTheory.SS.exists_semiAbelian_model_torusExtension_of_potModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, inferInstance, h3, G, i11, hG, he, hT⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ThetaProj

theorem eStd_swap (g n : ℕ) (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n a b = -eStd g n b a := by
  simp only [eStd]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_eStd_eq (g n : ℕ) (f : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n) :
    ∃ b, ∀ y, eStd g n b y = f y := by
  refine ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)),
    fun y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, f (Pi.single j (y j)) = y j * f (Pi.single j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h, h]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

theorem exists_retraction {n d : ℕ} [NeZero n] {Γ : Type} [AddCommGroup Γ] [Module (ZMod n) Γ]
    (T : AddSubgroup Γ) (e : T ≃+ (Fin d → ZMod n)) : ∃ p : Γ →+ T, ∀ t : T, p t = t := by
  let T' : Submodule (ZMod n) Γ := AddSubgroup.toZModSubmodule n T
  let e' : T' →+ (Fin d → ZMod n) :=
    { toFun := fun x => e ⟨x.1, x.2⟩
      map_zero' := map_zero e
      map_add' := fun x y => map_add e ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ }
  obtain ⟨f, hf⟩ := (ZModPerp.baer_of_free (n := n) (Fin d → ZMod n)).extension_property
    T'.subtype T'.subtype_injective (e'.toZModLinearMap n)
  refine ⟨e.symm.toAddMonoidHom.comp f.toAddMonoidHom, fun t => ?_⟩
  have : f t = e t := LinearMap.congr_fun hf ⟨t.1, t.2⟩
  simp [this]

theorem nsmul_eq_zero_of_forall_char {r N : ℕ} [NeZero (r * N)] {Γ : Type} [AddCommGroup Γ]
    [Module (ZMod (r * N)) Γ] (u : Γ) (h : ∀ ψ : Γ →+ ZMod N, ψ u = 0) : r • u = 0 := by
  by_contra hu
  obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := r * N) hu
  apply hf
  have h1 := h ((ZMod.castHom (dvd_mul_left N r) (ZMod N)).toAddMonoidHom.comp f.toAddMonoidHom)
  have h2 : ZMod.castHom (dvd_mul_left N r) (ZMod N) (f u) = 0 := h1
  rw [← ZMod.natCast_zmod_val (f u), map_natCast, ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨k, hk⟩ := h2
  rw [map_nsmul, ← ZMod.natCast_zmod_val (f u), hk, nsmul_eq_mul, ← Nat.cast_mul, ← _root_.mul_assoc,
    Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem sum_char_smul {o M U : Type} [CommRing o] [IsDomain o] [AddCommGroup M] [Module o M]
    [AddCommGroup U] [Fintype U] {N : ℕ} [NeZero N] [Fintype (U →+ ZMod N)]
    (χ : AddChar (ZMod N) o) (hχ : ∀ a, χ a = 1 → a = 0) (ρ : U → M)
    (hρ : ∀ u, (∀ ψ : U →+ ZMod N, ψ u = 0) → ρ u = ρ 0) :
    ∑ ψ : U →+ ZMod N, ∑ u, χ (-ψ u) • ρ u = (Fintype.card U : o) • ρ 0 := by
  have h1 : ∀ u, (∑ ψ : U →+ ZMod N, χ (-ψ u)) • ρ u
      = (∑ ψ : U →+ ZMod N, χ (-ψ u)) • ρ 0 := fun u => by
    by_cases hu : ∀ ψ : U →+ ZMod N, ψ u = 0
    · rw [hρ u hu]
    · obtain ⟨ψ, hψ⟩ := not_forall.mp hu
      have : χ.compAddMonoidHom (-(AddMonoidHom.eval u : (U →+ ZMod N) →+ ZMod N)) ≠ 1 := by
        intro h
        have := DFunLike.congr_fun h ψ
        exact hψ (neg_eq_zero.mp (hχ _ this))
      have h0 : ∑ ψ : U →+ ZMod N, χ (-ψ u) = 0 := AddChar.sum_eq_zero_of_ne_one this
      rw [h0, zero_smul, zero_smul]
  have h2 : ∀ ψ : U →+ ZMod N, ψ ≠ 0 → ∑ u, χ (-ψ u) = 0 := fun ψ hψ => by
    have : χ.compAddMonoidHom (-ψ) ≠ 1 := by
      intro h
      apply hψ
      ext u
      have := DFunLike.congr_fun h u
      exact neg_eq_zero.mp (hχ _ this)
    exact AddChar.sum_eq_zero_of_ne_one this
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h1]
  rw [← Finset.sum_smul, Finset.sum_comm,
    Finset.sum_eq_single (0 : U →+ ZMod N) (fun ψ _ => h2 ψ) (by simp)]
  simp

theorem sum_ext_char_smul {o M A T : Type} [CommRing o] [IsDomain o] [AddCommGroup M] [Module o M]
    [AddCommGroup A] [AddCommGroup T] [Finite A] [Finite T] {N : ℕ} [NeZero N]
    (i : A →+ T) (p : T →+ A) (hp : ∀ a, p (i a) = a)
    (χ : AddChar (ZMod N) o) (hχ : ∀ a, χ a = 1 → a = 0) (ρ : T → M)
    (hρ : ∀ a u, (∀ ψ : T →+ ZMod N, ψ u = 0) → ρ (i a + u) = ρ (i a)) (c' : A →+ ZMod N) :
    Nat.card T = Nat.card A * Nat.card p.ker ∧
    ∑ᶠ c ∈ {c : T →+ ZMod N | c.comp i = c'}, ∑ᶠ t, χ (-c t) • ρ t
      = (Nat.card p.ker : o) • ∑ᶠ a, χ (-c' a) • ρ (i a) := by
  let q : T →+ p.ker := (AddMonoidHom.id T - i.comp p).codRestrict p.ker fun t => by
    simp [AddMonoidHom.mem_ker, hp]
  have hq : ∀ t, (q t : T) = t - i (p t) := fun t => rfl
  have hqu : ∀ u : p.ker, q u = u := fun u => Subtype.ext (by
    rw [hq, (AddMonoidHom.mem_ker).mp u.2, map_zero, sub_zero])
  have hqi : ∀ a, q (i a) = 0 := fun a => Subtype.ext (by rw [hq, hp, sub_self]; rfl)
  let e : A × p.ker ≃ T :=
    { toFun := fun x => i x.1 + x.2
      invFun := fun t => (p t, q t)
      left_inv := fun x => by
        simp [hp, hqu, hqi, (AddMonoidHom.mem_ker).mp x.2.2]
      right_inv := fun t => by simp [hq] }
  have he : ∀ a (u : p.ker), e (a, u) = i a + u := fun _ _ => rfl
  refine ⟨by rw [← Nat.card_prod, Nat.card_congr e], ?_⟩
  have := Fintype.ofFinite A
  have := Fintype.ofFinite T
  have := Fintype.ofFinite p.ker
  have : Finite (p.ker →+ ZMod N) := DFunLike.finite _
  have := Fintype.ofFinite (p.ker →+ ZMod N)
  have hinj : Function.Injective fun ψ : p.ker →+ ZMod N => c'.comp p + ψ.comp q := by
    intro ψ ψ' h
    ext u
    have := DFunLike.congr_fun (add_left_cancel h) (u : T)
    simpa [hqu] using this
  have hs : {c : T →+ ZMod N | c.comp i = c'}
      = Set.range fun ψ : p.ker →+ ZMod N => c'.comp p + ψ.comp q := by
    ext c
    constructor
    · rintro rfl
      refine ⟨c.comp p.ker.subtype, ?_⟩
      ext t
      simp [hq]
    · rintro ⟨ψ, rfl⟩
      ext a
      simp [hp, hqi]
  rw [hs, finsum_mem_range hinj]
  simp_rw [finsum_eq_sum_of_fintype, ← e.sum_comp, Fintype.sum_prod_type, he]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := sum_char_smul χ hχ (fun u : p.ker => ρ (i a + u)) fun u hu => by
    have := hρ a u fun ψ => hu (ψ.comp p.ker.subtype)
    simpa using this
  simp only [ZeroMemClass.coe_zero, add_zero] at this
  rw [smul_comm, Nat.card_eq_fintype_card, ← this, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_smul, ← AddChar.map_add_eq_mul]
  simp [hp, hqu, hqi, (AddMonoidHom.mem_ker).mp u.2, add_comm]

end GlobalTheory.ThetaProj

namespace GlobalTheory

open ThetaProj

theorem thetaSys_FF_mem_finite_perp_proj :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω),
      (∀ T c k, S.FF T c k ∈ S.R) ∧ Set.Finite {x : Ω | ∃ T c k, x = S.FF T c k} ∧
      (∀ H, S.perp (S.perp H) = H) ∧
      ∀ (T T' : AddSubgroup S.Gam) (h : T' ≤ T), S.IsoFree T → S.IsoFree T' →
        ∀ (c' : T' →+ ZMod S.N), S.proj T' c' =
          ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'}, S.proj T c := by
  intro o Ω _ _ _ hA S
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have : IsDomain o := hA.inj.isDomain _
  refine ⟨fun T c k => ?_, ?_, fun H => ?_, fun T T' h hT hT' c' => ?_⟩
  · have := Fintype.ofFinite T
    rw [ThetaSys.FF, finsum_eq_sum_of_fintype]
    exact S.R.sum_mem fun t _ => S.R.mul_mem (S.R.algebraMap_mem _)
      (S.R.sum_mem fun j _ => S.R.mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))
  · have : Finite (AddSubgroup S.Gam) := Finite.of_injective _ SetLike.coe_injective
    have : ∀ T : AddSubgroup S.Gam, Finite (T →+ ZMod S.N) := fun T => DFunLike.finite _
    refine (Set.finite_range fun x : Σ T : AddSubgroup S.Gam,
      (T →+ ZMod S.N) × (S.J × (T → ZMod ((S.r * S.N) ^ 2))) => S.FF x.1 x.2.1 x.2.2).subset ?_
    rintro x ⟨T, c, k, rfl⟩
    exact ⟨⟨T, c, k⟩, rfl⟩
  · refine le_antisymm (fun x hx => ?_) fun x hx y hy => ?_
    · by_contra hxH
      let H' : Submodule (ZMod (S.r * S.N)) S.Gam := AddSubgroup.toZModSubmodule _ H
      obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := S.r * S.N) (q := H'.mkQ x)
        (fun h0 => hxH ((Submodule.Quotient.mk_eq_zero H').mp h0))
      obtain ⟨b, hb⟩ := exists_eStd_eq _ _ (f ∘ₗ H'.mkQ)
      have hb' : b ∈ S.perp H := fun y hy => by
        rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero H').mpr hy, map_zero]
      have h1 : eStd S.g _ x b = 0 := hx b hb'
      rw [eStd_swap, neg_eq_zero, hb] at h1
      exact hf h1
    · rw [eStd_swap, hy x hx, neg_zero]
  · obtain ⟨d, ⟨e⟩⟩ := hT.2
    obtain ⟨d', ⟨e'⟩⟩ := hT'.2
    obtain ⟨p, hp⟩ := exists_retraction T' e'
    have hζ : IsPrimitiveRoot S.ζN S.N :=
      S.prim.pow (NeZero.pos _) (by ring)
    let χ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hζ.pow_eq_one
    have hχ : ∀ a, χ a = 1 → a = 0 := fun a ha =>
      ((AddChar.zmodChar_primitive_of_primitive_root S.N hζ).zmod_char_eq_one_iff S.N a).mp ha
    let _ : Module (ZMod (S.r * S.N)) T := AddCommGroup.zmodModule fun x => Subtype.ext (by
      rw [AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self,
        zero_smul]
      rfl)
    obtain ⟨h1, h2⟩ := sum_ext_char_smul (AddSubgroup.inclusion h) (p.comp T.subtype)
      (fun a => hp a) χ hχ (fun t : T => S.ρ t) (fun a u hu => by
        have hu' : S.r • (u : S.Gam) = 0 :=
          congrArg Subtype.val (nsmul_eq_zero_of_forall_char (r := S.r) u hu)
        rw [AddSubgroup.coe_add, ← S.ρ_add _ _ (by
          rw [hT.1 (AddSubgroup.inclusion h a).2 u u.2, smul_zero]), S.ρ_one _ hu', _root_.mul_one]) c'
    have hu : IsUnit (Nat.card T : o) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
      exact S.unit.pow _
    have hfin : Finite (T →+ ZMod S.N) := DFunLike.finite _
    have h3 : ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'}, S.proj T c
        = Ring.inverse (Nat.card T : o) •
          ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'},
            ∑ᶠ t : T, χ (-c t) • S.ρ t := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
        finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.smul_sum]
      rfl
    rw [h3, h2, smul_smul]
    rw [h1, Nat.cast_mul] at hu ⊢
    rw [Ring.mul_inverse_rev' (Commute.all _ _), mul_right_comm,
      Ring.inverse_mul_cancel _ (isUnit_of_mul_isUnit_right hu), _root_.one_mul]
    rfl

end GlobalTheory
end

