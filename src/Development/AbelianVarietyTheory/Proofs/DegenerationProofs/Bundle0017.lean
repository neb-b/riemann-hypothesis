module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.CrdCalc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def valHom (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valR_eq (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = valHom x U h f := by
  unfold valR
  rw [dite_eq_left h]
  rfl

theorem valR_mul (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]

theorem valR_res (x : Sp R ⟶ X) {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_eq x V h, valR_eq x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]
  rfl

theorem valR_spMap {R' : Type} [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U ∧ ∀ f, valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun y _ => h (Set.mem_univ ((spMap φ) y))
  refine ⟨h', fun f => ?_⟩
  rw [valR_eq _ U h', valR_eq x U h]
  have e : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change ((spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom).hom f =
    (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ).hom f
  rw [e, Category.assoc, n]

theorem isUnit_valR_iff (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    IsUnit (valR x U f) ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen f := by
  rw [valR_eq x U h]
  have e : IsUnit (valHom x U h f) ↔ IsUnit ((x.appLE U ⊤ h).hom f) :=
    isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv _
  rw [e]
  have b := Scheme.basicOpen_appLE x ⊤ U h f
  constructor
  · intro hu
    rw [Scheme.basicOpen_of_isUnit _ hu] at b
    exact b.le.trans inf_le_right
  · intro hu
    rw [inf_eq_left.2 hu] at b
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => ?_
    exact (Scheme.mem_basicOpen _ _ y hy).1 (b.ge hy)

theorem top_le_iff [IsLocalRing R] (x : Sp R ⟶ X) (U : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint R) ∈ U :=
  ⟨fun h => h (Set.mem_univ _), fun h =>
    ((IsLocalRing.closed_point_mem_iff (R := R) (U := x ⁻¹ᵁ U)).1 h).ge⟩

theorem exists_unit_charts (H : LB X) (x : Sp R ⟶ X) (l l' : H.ι) (h : ⊤ ≤ x ⁻¹ᵁ H.U l)
    (h' : ⊤ ≤ x ⁻¹ᵁ H.U l') :
    ∃ c : Rˣ, ∀ s : H.Sec, valR x (H.U l) (s.f l) = c * valR x (H.U l') (s.f l') := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (H.U l ⊓ H.U l') := fun y hy => ⟨h hy, h' hy⟩
  refine ⟨Units.map (valHom x _ hh).toMonoidHom (H.g l l'), fun s => ?_⟩
  rw [← valR_res x (inf_le_left : H.U l ⊓ H.U l' ≤ H.U l) hh,
    ← valR_res x (inf_le_right : H.U l ⊓ H.U l' ≤ H.U l') hh]
  have := s.compat l l'
  change valR x _ ((X.presheaf.map _).hom _) = _
  rw [this, valR_mul x _ hh, valR_eq x _ hh]
  rfl

variable {H : LB X} {J : Type} {s : J → H.Sec}

theorem crd_exists [IsLocalRing R] (hH : H.IsLB) (s : J → H.Sec) (x : Sp R ⟶ X) : ∃ v, Crd H s x v := by
  have : x (IsLocalRing.closedPoint R) ∈ ⨆ i, H.U i := by rw [hH.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨_, l, 1, (top_le_iff x _).2 hl, fun _ => rfl⟩

theorem crd_unique {x : Sp R ⟶ X} {v v' : J → R} (h : Crd H s x v) (h' : Crd H s x v') :
    ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨l', c', hl', hv'⟩ := h'
  obtain ⟨u, hu⟩ := exists_unit_charts H x l' l hl' hl
  refine ⟨c' * u * c⁻¹, fun j => ?_⟩
  rw [hv, hv', hu, Units.val_mul, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, _root_.mul_assoc]

theorem crd_isUnit_iff [IsLocalRing R] {x : Sp R ⟶ X} {v : J → R} (j : J) (h : Crd H s x v) :
    IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j) := by
  obtain ⟨l, c, hl, hv⟩ := h
  rw [hv, Units.isUnit_units_mul]
  constructor
  · intro hu
    exact ((isUnit_valR_iff x _ hl _).1 hu).trans
      (x.preimage_mono (le_iSup (fun k => X.basicOpen ((s j).f k)) l))
  · intro hu
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_iff x _).1 hu)
    have hk' := (top_le_iff x _).2 hk
    have hU : ⊤ ≤ x ⁻¹ᵁ H.U k := hk'.trans (x.preimage_mono (X.basicOpen_le _))
    obtain ⟨u, hu⟩ := exists_unit_charts H x l k hl hU
    rw [hu, Units.isUnit_units_mul]
    exact (isUnit_valR_iff x _ hU _).2 hk'

theorem crd_map {R' : Type} [CommRing R'] (φ : R →+* R') {x : Sp R ⟶ X} {v : J → R} (h : Crd H s x v) :
    Crd H s (spMap φ ≫ x) (fun j => φ (v j)) := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨h₁, h₂⟩ := valR_spMap φ x _ hl
  refine ⟨l, Units.map φ.toMonoidHom c, h₁, fun j => ?_⟩
  beta_reduce
  rw [h₂, hv, map_mul]
  rfl

theorem crd_smul {x : Sp R ⟶ X} {v : J → R} (c : Rˣ) (h : Crd H s x v) :
    Crd H s x (fun j => (c : R) * v j) := by
  obtain ⟨l, c', hl, hv⟩ := h
  exact ⟨l, c * c', hl, fun j => by beta_reduce; rw [hv, Units.val_mul, _root_.mul_assoc]⟩

theorem crd_ratio {x : Sp R ⟶ X} {v : J → R} {i j : J} {W : X.Opens} {r : Γ(X, W)} (h : Crd H s x v)
    (hr : IsRatio (s j) (s i) W r) (hW : ⊤ ≤ x ⁻¹ᵁ W) : v j = valR x W r * v i := by
  obtain ⟨l, c, hl, hv⟩ := h
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ H.U l) := fun y hy => ⟨hW hy, hl hy⟩
  have := congrArg (valR x (W ⊓ H.U l)) (hr l)
  rw [valR_mul x _ hh, valR_res x _ hh, valR_res x _ hh, valR_res x _ hh] at this
  rw [hv, hv, this, mul_left_comm]

theorem crd_calculus : (∀ (X : Scheme.{0}) (H : LB X) (J : Type) (s : J → H.Sec), H.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), (∃ v, Crd H s x v) ∧ (∀ v v', Crd H s x v → Crd H s x v' → ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j) ∧ ∀ v j, Crd H s x v → (IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j))) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (v : J → R), Crd H s x v → Crd H s (spMap φ ≫ x) (fun j => φ (v j))) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (c : Rˣ), Crd H s x v → Crd H s x (fun j => (c : R) * v j)) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (i j : J) (W : X.Opens) (r : Γ(X, W)), Crd H s x v → IsRatio (s j) (s i) W r → ⊤ ≤ x ⁻¹ᵁ W → v j = valR x W r * v i) :=
  fun _ _ _ s hH =>
    ⟨fun _ _ _ x => ⟨crd_exists hH s x, fun _ _ => crd_unique, fun _ j => crd_isUnit_iff j⟩,
      fun _ _ _ _ φ _ _ => crd_map φ, fun _ _ _ _ c => crd_smul c, fun _ _ _ _ _ _ _ _ => crd_ratio⟩

end GlobalTheory.ZH.CrdCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HilbEqFinrankQuotPiece
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem hilb_eq_finrank_quotPiece {k J : Type} [Field k] [Finite J] (C : Set (J → k)) (d : ℕ) :
    hilb C d = Module.finrank k (quotPiece (MvPolynomial.vanishingIdeal k C) (d : ℤ)) := by
  rw [quotPiece_natCast]
  let ev : MvPolynomial J k →ₐ[k] (C → k) :=
    AlgHom.pi fun v : C => MvPolynomial.aeval v.1
  have hker : ∀ a ∈ MvPolynomial.vanishingIdeal k C, ev a = 0 := fun a ha =>
    funext fun v => ha v.1 v.2
  let φ := Ideal.Quotient.liftₐ (MvPolynomial.vanishingIdeal k C) ev hker
  have hφ : Function.Injective φ.toLinearMap := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.2 fun v hv => congrFun (show ev x = 0 from hx) ⟨v, hv⟩
  rw [(Submodule.equivMapOfInjective _ hφ _).finrank_eq, ← Submodule.map_comp]
  rfl

theorem eval_eq_zero_of_hilb_le : (∀ (k : Type) [Field k] [IsAlgClosed k] (J : Type) [Fintype J] (C : Set (J → k)) (g N : ℕ), (MvPolynomial.vanishingIdeal k C).IsPrime → (MvPolynomial.vanishingIdeal k C).IsHomogeneous (MvPolynomial.homogeneousSubmodule J k) → (∃ i, MvPolynomial.X i ∉ MvPolynomial.vanishingIdeal k C) → ringKrullDim (MvPolynomial J k ⧸ MvPolynomial.vanishingIdeal k C) = (g + 1 : ℕ) → (∀ d, 1 ≤ d → hilb C d ≤ (N * d) ^ g) → ∀ v : J → k, (∀ (d : ℕ) (Pf : MvPolynomial J k), d ≤ N ^ g * g.factorial → Pf.IsHomogeneous d → Pf ∈ MvPolynomial.vanishingIdeal k C → MvPolynomial.eval v Pf = 0) → ∀ Pf ∈ MvPolynomial.vanishingIdeal k C, MvPolynomial.eval v Pf = 0) := by
  intro k _ _ J _ C g N hP hPh hne hdim hb v hv Pf hPf
  by_contra h0
  obtain ⟨d, hd, f, hf, hfd, hfv⟩ :=
    exists_form_degree_le_hilbertDegree_eval_ne_zero hPh hne v ⟨Pf, hPf, h0⟩
  refine hfv (hv d f (hd.trans ?_) hfd hf)
  have hH := isHilbertPoly_idealHilbertPoly hPh
  have hg : (idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).natDegree = g := by
    rw [ProjCut.ringKrullDim_eq_natDegree_idealHilbertPoly hPh hne] at hdim
    have := Nat.cast_injective hdim
    omega
  have h1 : 0 ≤ (Polynomial.C ((N : ℚ) ^ g) * Polynomial.X ^ g -
      idealHilbertPoly (MvPolynomial.vanishingIdeal k C)).coeff g := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le (Polynomial.degree_C_mul_X_pow_le _ _) ?_)
      exact Polynomial.degree_le_of_natDegree_le hg.le
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        Filter.eventually_ge_atTop 1] with n hn h1n
      have := hb n h1n
      rw [hilb_eq_finrank_quotPiece, mul_pow] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
        ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, _root_.mul_one,
    sub_nonneg] at h1
  have h2 := cast_hilbertDegree hPh
  rw [Polynomial.leadingCoeff, hg] at h2
  have h3 : (hilbertDegree (MvPolynomial.vanishingIdeal k C) : ℚ) ≤ (N : ℚ) ^ g * g.factorial := by
    rw [h2, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
  exact_mod_cast h3

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.WtPart

section Alg
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))

def cf (χ : X) (s : R) : A := ((Equiv.ofBijective _ hb).symm s).coeff χ

theorem cf_apply (χ : X) (a : AddMonoidAlgebra A X) :
    cf hb χ (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _) a) = a.coeff χ :=
  congrArg (fun a : AddMonoidAlgebra A X => a.coeff χ) ((Equiv.ofBijective _ hb).symm_apply_apply a)

theorem cf_zero (χ : X) : cf hb χ 0 = 0 := by
  have := cf_apply hb χ 0
  rwa [map_zero] at this

theorem cf_add (χ : X) (s t : R) : cf hb χ (s + t) = cf hb χ s + cf hb χ t := by
  obtain ⟨a, rfl⟩ := hb.2 s
  obtain ⟨b, rfl⟩ := hb.2 t
  rw [← map_add (f := _), cf_apply, cf_apply, cf_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem cf_sum {K : Type} (χ : X) (T : Finset K) (s : K → R) :
    cf hb χ (∑ i ∈ T, s i) = ∑ i ∈ T, cf hb χ (s i) :=
  map_sum (AddMonoidHom.mk' (cf hb χ) (cf_add hb χ)) s T

open Classical in
theorem cf_mono (χ ψ : X) (b : A) :
    cf hb χ (f b * m (Multiplicative.ofAdd ψ)) = if ψ = χ then b else 0 := by
  rw [← AddMonoidAlgebra.liftNCRingHom_single f m (fun _ _ => Commute.all _ _), cf_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem cf_ext {s t : R} (h : ∀ χ, cf hb χ s = cf hb χ t) : s = t :=
  (Equiv.ofBijective _ hb).symm.injective (AddMonoidAlgebra.ext (Finsupp.ext h))

theorem cf_finite (s : R) : {χ | cf hb χ s ≠ 0}.Finite :=
  ((Equiv.ofBijective _ hb).symm s).coeff.support.finite_toSet.subset
    fun _ h => Finsupp.mem_support_iff.2 h

def part (χ : X) (s : R) : R := f (cf hb χ s) * m (Multiplicative.ofAdd χ)

theorem part_eq_zero {χ : X} {s : R} (h : cf hb χ s = 0) : part hb χ s = 0 := by
  rw [part, h, map_zero, zero_mul]

open Classical in
theorem part_mono (χ ψ : X) (b : A) :
    part hb χ (f b * m (Multiplicative.ofAdd ψ)) =
      if ψ = χ then f b * m (Multiplicative.ofAdd ψ) else 0 := by
  rw [part, cf_mono]
  split_ifs with h
  · rw [h]
  · rw [map_zero, zero_mul]

theorem part_map {A' R' : Type} [CommRing A'] [CommRing R'] {f' : A' →+* R'}
    {m' : Multiplicative X →* R'}
    (hb' : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f' m' (fun _ _ => Commute.all _ _)))
    (σ : R →+ R')
    (hσ : ∀ b ψ, ∃ b', σ (f b * m (Multiplicative.ofAdd ψ)) = f' b' * m' (Multiplicative.ofAdd ψ))
    (χ : X) (s : R) : σ (part hb χ s) = part hb' χ (σ s) := by
  obtain ⟨a, rfl⟩ := hb.2 s
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, part, cf_zero, zero_mul]
  | add x y hx hy =>
    simp only [part] at hx hy
    simp only [map_add (f := _), part, cf_add, add_mul, hx, hy]
  | single ψ b =>
    obtain ⟨b', e⟩ := hσ b ψ
    rw [AddMonoidAlgebra.liftNCRingHom_single, e, part_mono, part_mono]
    split_ifs
    · exact e
    · exact map_zero σ

theorem constr_rel {K M M' N : Type} [CommGroup M] [CommGroup M'] [CommGroup N]
    (b : Module.Basis K ℤ X) (u : K → M) (u' : K → M') (c : K → N) (σ : M →* M') (τ : N →* M')
    (h : ∀ k, σ (u k) = τ (c k) * u' k) (ψ : X) :
    σ (Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (u k)) ψ)) =
      τ (Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (c k)) ψ)) *
        Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (u' k)) ψ) := by
  simp only [Module.Basis.constr_apply, Finsupp.sum, toMul_sum, toMul_zsmul, toMul_ofMul, map_prod,
    map_zpow, h, mul_zpow, Finset.prod_mul_distrib]

end Alg

theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem rapp {X Y : Scheme.{0}} (q : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    resG Y (q.preimage_mono h) ((q.app U).hom a) = (q.app V).hom (resG X h a) := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    q.naturality]
  rfl

section Datum
variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G)

abbrev mono (j : E.ChartIdx) (V : E.B.left.Opens) (h : V ≤ E.chart j) :
    Multiplicative E.X →* Γ(G.left, D.q.left ⁻¹ᵁ V) :=
  (Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
    (E.basis.constr ℤ (fun k => Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k)))).toAddMonoidHom)

theorem res_mono {j j' : E.ChartIdx} {V W : E.B.left.Opens} (hV : V ≤ E.chart j')
    (hW : W ≤ E.chart j) (h : W ≤ V) (ψ : E.X) :
    ∃ c : Γ(E.B.left, W), resG _ (D.q.left.preimage_mono h) (mono D j' V hV (Multiplicative.ofAdd ψ)) =
      (D.q.left.app W).hom c * mono D j W hW (Multiplicative.ofAdd ψ) := by
  have hW' : W ≤ E.chart j ⊓ E.chart j' := le_inf hW (h.trans hV)
  refine ⟨_, congrArg Units.val (constr_rel E.basis
    (fun k => res (Scheme.Hom.preimage_mono D.q.left hV) (D.u j' k))
    (fun k => res (Scheme.Hom.preimage_mono D.q.left hW) (D.u j k))
    (fun k => res hW' (res (le_inf (inf_le_left.trans (E.chart_le j k))
      (inf_le_right.trans (E.chart_le j' k))) ((E.O (E.basis k)).L.g (j k) (j' k))))
    (res (D.q.left.preimage_mono h)) (pullU D.q.left W) (fun k => Units.ext ?_) ψ)⟩
  have e := congrArg (resG _ (D.q.left.preimage_mono hW')) (congrArg Units.val (D.trans j j' k))
  rw [Units.val_mul, map_mul] at e
  exact (rr _ _ _).trans ((rr _ _ _).symm.trans (e.trans (congrArg₂ (· * ·) (rapp _ _ _) (rr _ _ _))))

end Datum

variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}

def partSec (φ : (Φ.H d).Sec) (α : Φ.E.X) : (Φ.H d).Sec where
  f l := part (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α (φ.f l)
  compat l l' := by
    let q := Φ.D.q.left
    let I := {W : Φ.E.B.left.affineOpens // W.1 ≤ Φ.N₀.U l ⊓ Φ.N₀.U l'}
    refine Φ.G.left.sheaf.eq_of_locally_eq' (fun W : I => q ⁻¹ᵁ W.1.1) _
      (fun W => homOfLE (q.preimage_mono W.2)) (fun x hx => ?_) _ _ fun W => ?_
    · obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Φ.E.B.left) (x := q x)
        (U := Φ.N₀.U l ⊓ Φ.N₀.U l') hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hle⟩, hxW⟩
    have h₁ : W.1.1 ≤ Φ.N₀.U l := W.2.trans inf_le_left
    have h₂ : W.1.1 ≤ Φ.N₀.U l' := W.2.trans inf_le_right
    have hW : W.1.1 ≤ Φ.E.chart (Φ.ch l) := h₁.trans (Φ.le l)
    let w : Γ(Φ.E.B.left, W.1.1) := resG _ W.2 (Φ.N₀.g l l').1 ^ d
    have hw : resG _ (q.preimage_mono W.2) ((Φ.H d).g l l').1 = (q.app W.1.1).hom w := by
      change resG _ (q.preimage_mono W.2) (((pullU q _ (Φ.N₀.g l l')) ^ d).1) = _
      rw [Units.val_pow_eq_pow_val, map_pow, map_pow]
      exact congrArg (· ^ d) (rapp _ _ _)
    have e₁ := part_map (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l))
      (Φ.D.coord (Φ.ch l) W.1.1 W.1.2 hW) (resG _ (q.preimage_mono h₁)).toAddMonoidHom
      (fun b ψ => by
        obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l) hW h₁ ψ
        refine ⟨resG _ h₁ b * c, (map_mul (resG _ (q.preimage_mono h₁)) _ _).trans ?_⟩
        rw [hc, rapp, map_mul, _root_.mul_assoc]) α (φ.f l)
    have e₂ := part_map (Φ.D.coord (Φ.ch l') (Φ.N₀.U l') (Φ.aff l') (Φ.le l'))
      (Φ.D.coord (Φ.ch l) W.1.1 W.1.2 hW)
      ((AddMonoidHom.mulLeft ((q.app W.1.1).hom w)).comp (resG _ (q.preimage_mono h₂)).toAddMonoidHom)
      (fun b ψ => by
        obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l') hW h₂ ψ
        refine ⟨w * (resG _ h₂ b * c), (congrArg (_ * ·)
          (map_mul (resG _ (q.preimage_mono h₂)) _ _)).trans ?_⟩
        rw [hc, rapp, map_mul, map_mul, _root_.mul_assoc, _root_.mul_assoc]) α (φ.f l')
    have e₃ := congrArg (resG _ (q.preimage_mono W.2)) (φ.compat l l')
    have e₄ : resG _ (q.preimage_mono h₁) (φ.f l) =
        (q.app W.1.1).hom w * resG _ (q.preimage_mono h₂) (φ.f l') :=
      (rr _ _ _).symm.trans (e₃.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) hw (rr _ _ _))))
    refine (rr _ _ _).trans (e₁.trans ((congrArg _ e₄).trans (e₂.symm.trans ?_)))
    exact ((map_mul (resG _ (q.preimage_mono W.2)) _ _).trans (congrArg₂ (· * ·) hw (rr _ _ _))).symm

open Classical in
theorem wt_partSec (φ : (Φ.H d).Sec) (α β : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.wt (partSec Φ φ α) β l = if α = β then Φ.wt φ α l else 0 :=
  cf_mono (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β α _

theorem isPart_partSec (φ : (Φ.H d).Sec) (α : Φ.E.X) : Φ.IsPart α φ (partSec Φ φ α) := by
  refine ⟨?_, fun l => by rw [wt_partSec, if_pos rfl]⟩
  rintro β ⟨l, hl⟩
  by_contra h
  exact hl (by rw [wt_partSec, if_neg (fun e => h e.symm)])

theorem supp_finite (φ : (Φ.H d).Sec) : (Φ.supp φ).Finite := by
  have := Φ.E.isAbelian.proper
  have : CompactSpace Φ.E.B.left := QuasiCompact.compactSpace_of_compactSpace Φ.E.B.hom
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun l => (Φ.N₀.U l : Set Φ.E.B.left))
    (fun l => (Φ.N₀.U l).isOpen) (fun x _ => Set.mem_iUnion.2
      (TopologicalSpace.Opens.mem_iSup.1 (Φ.isLB.cover.ge (show x ∈ ⊤ from trivial))))
  refine (T.finite_toSet.biUnion fun l _ =>
    cf_finite (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) (φ.f l)).subset ?_
  rintro α ⟨l', hl'⟩
  by_contra hn
  have h0 : ∀ l ∈ T, (partSec Φ φ α).f l = 0 := fun l hl => by
    have : cf (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α (φ.f l) = 0 := by
      by_contra h
      exact hn (Set.mem_biUnion hl h)
    exact part_eq_zero _ this
  have h1 : (partSec Φ φ α).f l' = 0 := by
    refine Φ.G.left.sheaf.eq_of_locally_eq' (fun l : T => (Φ.H d).U l' ⊓ (Φ.H d).U l.1) _
      (fun l => homOfLE inf_le_left) (fun x hx => ?_) _ _ fun l => ?_
    · obtain ⟨l, hl, hx'⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ (Φ.D.q.left x)))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨l, hl⟩, hx, hx'⟩
    · refine ((partSec Φ φ α).compat l' l.1).trans ?_
      rw [h0 l.1 l.2, map_zero, mul_zero]
      exact (map_zero (resG _ _)).symm
  apply hl'
  rw [← (isPart_partSec Φ φ α).2 l', FibPre.wt, h1]
  exact cf_zero (Φ.D.coord (Φ.ch l') (Φ.N₀.U l') (Φ.aff l') (Φ.le l')) α

theorem sec_ext (φ ψ : (Φ.H d).Sec) (h : ∀ α l, Φ.wt φ α l = Φ.wt ψ α l) : φ = ψ := by
  have : φ.f = ψ.f := funext fun l =>
    cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun α => h α l
  cases φ
  cases ψ
  congr

theorem eq_sum_parts (φ : (Φ.H d).Sec) (A : Finset Φ.E.X) (ψ : Φ.E.X → (Φ.H d).Sec)
    (hA : Φ.supp φ ⊆ A) (hψ : ∀ α ∈ A, Φ.IsPart α φ (ψ α)) (l : Φ.N₀.ι) :
    φ.f l = ∑ α ∈ A, (ψ α).f l := by
  refine cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun β => Eq.symm ?_
  refine (cf_sum (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β A _).trans ?_
  change ∑ α ∈ A, Φ.wt (ψ α) β l = Φ.wt φ β l
  have h0 : ∀ α ∈ A, α ≠ β → Φ.wt (ψ α) β l = 0 := fun α hα hne => by
    by_contra h
    exact hne ((hψ α hα).1 ⟨l, h⟩).symm
  by_cases hβ : β ∈ A
  · rw [Finset.sum_eq_single_of_mem β hβ h0, (hψ β hβ).2 l]
  · rw [Finset.sum_eq_zero fun α hα => h0 α hα fun e => hβ (e ▸ hα)]
    by_contra h
    exact hβ (hA ⟨l, fun e => h e.symm⟩)

theorem weight_parts : (∀ (k : Type) [Field k] (Φ : FibPre k) (d : ℕ), (∀ (φ : (Φ.H d).Sec) (α : Φ.E.X), ∃ ψ, Φ.IsPart α φ ψ) ∧ (∀ φ : (Φ.H d).Sec, (Φ.supp φ).Finite) ∧ (∀ φ ψ : (Φ.H d).Sec, (∀ α l, Φ.wt φ α l = Φ.wt ψ α l) → φ = ψ) ∧ ∀ (φ : (Φ.H d).Sec) (A : Finset Φ.E.X) (ψ : Φ.E.X → (Φ.H d).Sec), Φ.supp φ ⊆ A → (∀ α ∈ A, Φ.IsPart α φ (ψ α)) → ∀ l, φ.f l = ∑ α ∈ A, (ψ α).f l) :=
  fun _ _ Φ _ => ⟨fun φ α => ⟨_, isPart_partSec Φ φ α⟩, supp_finite Φ, sec_ext Φ, eq_sum_parts Φ⟩

end GlobalTheory.ZH.WtPart
end
end

