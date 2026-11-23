module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TensorContentEqPolyContentScalarCoeffs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffMapDomainMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

section
variable {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)}

theorem exists_addGauss (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] :
    ∃ w : AddValuation (AddMonoidAlgebra F X) (WithTop ℚ),
      ∀ (f : AddMonoidAlgebra F X) (g : WithTop ℚ), g ≤ w f ↔ ∀ m, g ≤ v (f.coeff m) := by
  haveI : UniqueSums X :=
    (AddEquiv.uniqueSums_iff (Module.Free.chooseBasis ℤ X).repr.toAddEquiv).mpr inferInstance
  exact ⟨AddValuation.ofValuation (GlobalTheory.gaussValAlg (G := X) (AddValuation.toValuation v)),
    fun f g => GlobalTheory.gaussValAlg_le_iff (G := X) (AddValuation.toValuation v) (f := f)⟩

theorem NullV.exists_lower {X : Type} {A : X → F} (hA : NullV v A) :
    ∃ M : ℚ, ∀ M' : ℚ, M' ≤ M → ∀ χ, (M' : WithTop ℚ) ≤ v (A χ) := by
  obtain ⟨M, hM⟩ := ((hA 0).image (fun χ => (v (A χ)).untopD 0)).bddBelow
  refine ⟨min M 0, fun M' hM' χ => ?_⟩
  by_cases hχ : v (A χ) < ((0 : ℚ) : WithTop ℚ)
  · have h1 : M ≤ (v (A χ)).untopD 0 := hM ⟨χ, hχ, rfl⟩
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hχ.ne_top
    rw [← hr] at h1 ⊢
    rw [WithTop.untopD_coe] at h1
    exact WithTop.coe_le_coe.mpr (hM'.trans ((min_le_left _ _).trans h1))
  · exact (WithTop.coe_le_coe.mpr (hM'.trans (min_le_right _ _))).trans (not_lt.mp hχ)

theorem NullV.exists_trunc {X : Type} {A : X → F} (hA : NullV v A) (N : ℚ) :
    ∃ a : AddMonoidAlgebra F X, (∀ χ, (N : WithTop ℚ) ≤ v (A χ - a.coeff χ)) ∧
      (∀ χ, v (A χ) ≤ v (a.coeff χ)) ∧ ∀ χ, v (A χ) < (N : WithTop ℚ) → a.coeff χ = A χ := by
  classical
  refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (hA N).toFinset
    (fun χ => if v (A χ) < (N : WithTop ℚ) then A χ else 0) (fun χ hχ => ?_)), fun χ => ?_, fun χ => ?_,
    fun χ hχ => ?_⟩
  · rw [Set.Finite.mem_toFinset]
    by_contra hn
    exact hχ (if_neg hn)
  · simp only [Finsupp.onFinset_apply]
    split_ifs with hχ
    · simp
    · simpa using hχ
  · simp only [Finsupp.onFinset_apply]
    split_ifs with hχ
    · exact le_rfl
    · simp
  · simp only [Finsupp.onFinset_apply, if_pos hχ]

theorem coeff_mapDomain_mul {X : Type} [AddCommGroup X] (h : X →+ X) (a c : AddMonoidAlgebra F X)
    (T : Finset X) (hT : a.coeff.support ⊆ T) (α : X) :
    (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α = ∑ χ ∈ T, a.coeff χ * c.coeff (α - h χ) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain, Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_mul]),
    Finsupp.sum_of_support_subset _ hT _ (by simp)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [neg_add_eq_sub]

theorem val_mul_sub_mul {x y x' y' : F} {M N : ℚ} (hx : (N : WithTop ℚ) ≤ v (x - x'))
    (hy : (N : WithTop ℚ) ≤ v (y - y')) (hy0 : (M : WithTop ℚ) ≤ v y) (hx0 : (M : WithTop ℚ) ≤ v x') :
    ((N + M : ℚ) : WithTop ℚ) ≤ v (x * y - x' * y') := by
  have e : x * y - x' * y' = (x - x') * y + (y - y') * x' := by ring
  rw [e, WithTop.coe_add]
  refine v.map_le_add ?_ ?_ <;> rw [v.map_mul]
  · exact add_le_add hx hy0
  · exact add_le_add hy hx0

theorem SumV.fibre {X : Type} [AddCommGroup X] (h : X →+ X) (α : X) (f : X → X → F) {s : F}
    (H : SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => f p.1.1 p.1.2) s) :
    SumV v (fun χ => f χ (α - h χ)) s := by
  classical
  let e : X ≃ {p : X × X // h p.1 + p.2 = α} :=
    { toFun := fun χ => ⟨(χ, α - h χ), by simp⟩
      invFun := fun p => p.1.1
      left_inv := fun χ => rfl
      right_inv := fun p => Subtype.ext (Prod.ext rfl (sub_eq_of_eq_add' p.2.symm)) }
  intro q
  obtain ⟨S, hS⟩ := H q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) (fun p hp => by
    rw [Finset.mem_map_equiv]
    exact hT (Finset.mem_map_of_mem _ hp))
  rw [Finset.sum_map] at this
  exact this

theorem val_sum_sub_coeff {X : Type} [AddCommGroup X] (h : X →+ X) {A C : X → F}
    {a c : AddMonoidAlgebra F X} {M N : ℚ}
    (hA : ∀ χ, (M : WithTop ℚ) ≤ v (A χ)) (hC : ∀ χ, (M : WithTop ℚ) ≤ v (C χ))
    (ha : ∀ χ, (N : WithTop ℚ) ≤ v (A χ - a.coeff χ)) (ha' : ∀ χ, v (A χ) ≤ v (a.coeff χ))
    (hc : ∀ χ, (N : WithTop ℚ) ≤ v (C χ - c.coeff χ))
    (T : Finset X) (hT : a.coeff.support ⊆ T) (α : X) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v (∑ χ ∈ T, A χ * C (α - h χ) -
      (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α) := by
  rw [coeff_mapDomain_mul h a c T hT, ← Finset.sum_sub_distrib]
  exact v.map_le_sum fun χ _ => val_mul_sub_mul (ha _) (hc _) (hC _) ((hA _).trans (ha' _))

theorem val_coeff_of_sumV {X : Type} [AddCommGroup X] (h : X →+ X) {A₁ A₂ C₁ C₂ : X → F}
    {a₁ a₂ c₁ c₂ : AddMonoidAlgebra F X} {M N : ℚ}
    (hA₁ : ∀ χ, (M : WithTop ℚ) ≤ v (A₁ χ)) (hA₂ : ∀ χ, (M : WithTop ℚ) ≤ v (A₂ χ))
    (hC₁ : ∀ χ, (M : WithTop ℚ) ≤ v (C₁ χ)) (hC₂ : ∀ χ, (M : WithTop ℚ) ≤ v (C₂ χ))
    (ha₁ : ∀ χ, (N : WithTop ℚ) ≤ v (A₁ χ - a₁.coeff χ)) (ha₁' : ∀ χ, v (A₁ χ) ≤ v (a₁.coeff χ))
    (ha₂ : ∀ χ, (N : WithTop ℚ) ≤ v (A₂ χ - a₂.coeff χ)) (ha₂' : ∀ χ, v (A₂ χ) ≤ v (a₂.coeff χ))
    (hc₁ : ∀ χ, (N : WithTop ℚ) ≤ v (C₁ χ - c₁.coeff χ))
    (hc₂ : ∀ χ, (N : WithTop ℚ) ≤ v (C₂ χ - c₂.coeff χ)) (α : X)
    (H : SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v ((AddMonoidAlgebra.mapDomainRingHom F h a₁ * c₂ -
      AddMonoidAlgebra.mapDomainRingHom F h a₂ * c₁).coeff α) := by
  classical
  obtain ⟨S, hS⟩ := SumV.fibre h α (fun x y => A₁ x * C₂ y - A₂ x * C₁ y) H (N + M)
  have h0 := hS (S ∪ (a₁.coeff.support ∪ a₂.coeff.support)) Finset.subset_union_left
  have h1 := val_sum_sub_coeff h hA₁ hC₂ ha₁ ha₁' hc₂ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_left.trans Finset.subset_union_right) α
  have h2 := val_sum_sub_coeff h hA₂ hC₁ ha₂ ha₂' hc₁ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_right.trans Finset.subset_union_right) α
  have h3 := v.map_le_sub (v.map_le_sub h2 h1) h0
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring
end

theorem sumV_cancel : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X →+ X), Function.Injective h → ∀ A₁ A₂ B₁ B₂ C₁ C₂ : X → F, NullV v A₁ → NullV v A₂ → NullV v B₁ → NullV v B₂ → NullV v C₁ → NullV v C₂ → (∀ α, SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) → (∀ α, SumV v (fun p : {p : X × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0) → C₂ ≠ 0 → ∀ α, SumV v (fun χ : X => B₁ χ * A₂ (α - χ) - B₂ χ * A₁ (α - χ)) 0 := by
  classical
  intro F _ v X _ _ _ h hinj A₁ A₂ B₁ B₂ C₁ C₂ nA₁ nA₂ nB₁ nB₂ nC₁ nC₂ HA HB hC α q
  obtain ⟨w, hw⟩ := exists_addGauss v X
  obtain ⟨χ₀, hχ₀⟩ := Function.ne_iff.mp hC
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (fun e => hχ₀ (v.top_iff.mp e) : v (C₂ χ₀) ≠ ⊤)
  obtain ⟨M₁, hM₁⟩ := nA₁.exists_lower
  obtain ⟨M₂, hM₂⟩ := nA₂.exists_lower
  obtain ⟨M₃, hM₃⟩ := nB₁.exists_lower
  obtain ⟨M₄, hM₄⟩ := nB₂.exists_lower
  obtain ⟨M₅, hM₅⟩ := nC₁.exists_lower
  obtain ⟨M₆, hM₆⟩ := nC₂.exists_lower
  obtain ⟨M, l1, l2, l3, l4, l5, l6⟩ : ∃ M : ℚ, M ≤ M₁ ∧ M ≤ M₂ ∧ M ≤ M₃ ∧ M ≤ M₄ ∧ M ≤ M₅ ∧ M ≤ M₆ :=
    ⟨min M₁ (min M₂ (min M₃ (min M₄ (min M₅ M₆)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  replace hM₁ := hM₁ M l1
  replace hM₂ := hM₂ M l2
  replace hM₃ := hM₃ M l3
  replace hM₄ := hM₄ M l4
  replace hM₅ := hM₅ M l5
  replace hM₆ := hM₆ M l6
  obtain ⟨N, n1, n2, n3⟩ : ∃ N : ℚ, m < N ∧ q + m ≤ M + (N + M) ∧ q ≤ N + M := by
    refine ⟨max (m + 1) (max (q + m - M - M) (q - M)), ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · have := (le_max_left (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
    · have := (le_max_right (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
  obtain ⟨a₁, ha₁, ha₁', -⟩ := nA₁.exists_trunc N
  obtain ⟨a₂, ha₂, ha₂', -⟩ := nA₂.exists_trunc N
  obtain ⟨b₁, hb₁, hb₁', -⟩ := nB₁.exists_trunc N
  obtain ⟨b₂, hb₂, hb₂', -⟩ := nB₂.exists_trunc N
  obtain ⟨c₁, hc₁, -, -⟩ := nC₁.exists_trunc N
  obtain ⟨c₂, hc₂, -, hc₂'⟩ := nC₂.exists_trunc N
  have EA := (hw _ _).mpr fun β =>
    val_coeff_of_sumV h hM₁ hM₂ hM₅ hM₆ ha₁ ha₁' ha₂ ha₂' hc₁ hc₂ β (HA β)
  have EB := (hw _ _).mpr fun β =>
    val_coeff_of_sumV h hM₃ hM₄ hM₅ hM₆ hb₁ hb₁' hb₂ hb₂' hc₁ hc₂ β (HB β)
  have push : ∀ (d : AddMonoidAlgebra F X) (g : WithTop ℚ),
      g ≤ w (AddMonoidAlgebra.mapDomainRingHom F h d) ↔ ∀ χ, g ≤ v (d.coeff χ) := by
    intro d g
    rw [hw, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
    refine ⟨fun H χ => ?_, fun H β => ?_⟩
    · have := H (h χ)
      rwa [Finsupp.mapDomain_apply_of_injective hinj] at this
    · by_cases hβ : β ∈ Set.range h
      · obtain ⟨χ, rfl⟩ := hβ
        rw [Finsupp.mapDomain_apply_of_injective hinj]
        exact H χ
      · rw [Finsupp.mapDomain_of_notMem_range _ _ hβ, v.map_zero]
        exact le_top
  set P := AddMonoidAlgebra.mapDomainRingHom F h with hP
  have key : ((q + m : ℚ) : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) + w c₂ := by
    have e : P (b₁ * a₂ - b₂ * a₁) * c₂ =
        P a₂ * (P b₁ * c₂ - P b₂ * c₁) - P b₂ * (P a₁ * c₂ - P a₂ * c₁) := by
      rw [map_sub, map_mul, map_mul]; ring
    rw [← w.map_mul, e]
    refine (WithTop.coe_le_coe.mpr n2).trans ?_
    rw [WithTop.coe_add]
    refine w.map_le_sub ?_ ?_ <;> rw [w.map_mul]
    · exact add_le_add ((push _ _).mpr fun χ => (hM₂ χ).trans (ha₂' χ)) EB
    · exact add_le_add ((push _ _).mpr fun χ => (hM₄ χ).trans (hb₂' χ)) EA
  have hc : w c₂ ≤ (m : WithTop ℚ) := by
    have := (hw c₂ _).mp le_rfl χ₀
    rwa [hc₂' χ₀ (by rw [← hm]; exact WithTop.coe_lt_coe.mpr n1), ← hm] at this
  have key2 : (q : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) := by
    have := key.trans (add_le_add le_rfl hc)
    rw [WithTop.coe_add] at this
    exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp this
  have key3 := (push _ _).mp key2 α
  refine ⟨b₁.coeff.support ∪ b₂.coeff.support, fun T hT => ?_⟩
  have h1 := val_sum_sub_coeff (AddMonoidHom.id X) hM₃ hM₂ hb₁ hb₁' ha₂ T
    (Finset.subset_union_left.trans hT) α
  have h2 := val_sum_sub_coeff (AddMonoidHom.id X) hM₄ hM₁ hb₂ hb₂' ha₁ T
    (Finset.subset_union_right.trans hT) α
  rw [AddMonoidAlgebra.mapDomainRingHom_id] at h1 h2
  simp only [RingHom.id_apply, AddMonoidHom.id_apply] at h1 h2
  have h3 := v.map_le_sub (v.map_le_sub ((WithTop.coe_le_coe.mpr n3).trans h2)
    ((WithTop.coe_le_coe.mpr n3).trans h1)) key3
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffMemOfPoints
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.UU.RingPoint

noncomputable section
namespace GlobalTheory.UU.UnitCob

section Alg
variable {B C : Type} [CommRing B] [CommRing C] {M N : Type} [AddCommGroup M] [AddCommGroup N]

def ev (κ : B →+* C) (c : Multiplicative M →* Cˣ) : AddMonoidAlgebra B M →+* C :=
  AddMonoidAlgebra.liftNCRingHom κ ((Units.coeHom C).comp c) fun _ _ => Commute.all _ _

theorem ev_single (κ : B →+* C) (c : Multiplicative M →* Cˣ) (m : M) (b : B) :
    ev κ c (AddMonoidAlgebra.single m b) = κ b * (c (Multiplicative.ofAdd m)).val := by
  simp [ev, AddMonoidAlgebra.liftNCRingHom]

def pair (c : Multiplicative M →* Cˣ) (c' : Multiplicative N →* Cˣ) : Multiplicative (M × N) →* Cˣ :=
  MonoidHom.mk' (fun p => c (Multiplicative.ofAdd p.toAdd.1) * c' (Multiplicative.ofAdd p.toAdd.2)) fun p q => by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul]
    exact _root_.mul_mul_mul_comm _ _ _ _

theorem map_mapDomain (s : M → N) (F : AddMonoidAlgebra B N →+* C) (G : AddMonoidAlgebra B M →+* C)
    (h : ∀ m b, F (AddMonoidAlgebra.single (s m) b) = G (AddMonoidAlgebra.single m b)) (a : AddMonoidAlgebra B M) :
    F (AddMonoidAlgebra.mapDomain s a) = G a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [AddMonoidAlgebra.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
  | single m b => rw [AddMonoidAlgebra.mapDomain_single, h]

theorem hom_eq (F G : AddMonoidAlgebra B M →+* C)
    (h : ∀ m b, F (AddMonoidAlgebra.single m b) = G (AddMonoidAlgebra.single m b)) (a : AddMonoidAlgebra B M) :
    F a = G a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | single m b => exact h m b

theorem ev_eq_zero (κ : B →+* C) (c : Multiplicative M →* Cˣ) (a : AddMonoidAlgebra B M)
    (h : ∀ m, κ (a.coeff m) = 0) : ev κ c a = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← AddMonoidAlgebra.sum_coeff_single a, Finsupp.sum, map_sum]
  exact Finset.sum_eq_zero fun m _ => by rw [ev_single, h, zero_mul]

theorem coeff_mem (I : Ideal B) (G : AddMonoidAlgebra B M →+* AddMonoidAlgebra (B ⧸ I) M)
    (hG : ∀ m b, G (AddMonoidAlgebra.single m b) = AddMonoidAlgebra.single m (Ideal.Quotient.mk I b))
    (a : AddMonoidAlgebra B M) (h : G a = 1) (p : M) : (a - 1).coeff p ∈ I := by
  have k : AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk I) a = G a :=
    hom_eq _ G (fun m b => by rw [hG]; simp) a
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← AddMonoidAlgebra.coeff_mapRingHom, map_sub, k, h, map_one, sub_self]
  rfl

def mon (B : Type) [CommRing B] (s : M →+ N) : Multiplicative M →* (AddMonoidAlgebra B N)ˣ :=
  ((AddMonoidAlgebra.of B N).comp (AddMonoidHom.toMultiplicative s)).toHomUnits

theorem mon_val (s : M →+ N) (m : M) :
    (mon B s (Multiplicative.ofAdd m)).val = AddMonoidAlgebra.single (s m) 1 := rfl

end Alg

section Geo
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

def ev₁ {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) : AddMonoidAlgebra Γ(Y.left, ⊤) X →+* Γ(Z.left, ⊤) :=
  ev y.left.appTop.hom (splitTorusPointsEquiv S X Z t)

def ev₂ {Z : Over S} (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) :
    AddMonoidAlgebra Γ(Y.left, ⊤) (X × X) →+* Γ(Z.left, ⊤) :=
  ev y.left.appTop.hom (pair (splitTorusPointsEquiv S X Z t) (splitTorusPointsEquiv S X Z t'))

theorem ev₁_single {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (m : X) (b) :
    ev₁ t y (AddMonoidAlgebra.single m b) = y.left.appTop.hom b * (chV t m).val := ev_single _ _ _ _

theorem ev₂_single {Z : Over S} (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (m : X × X) (b) :
    ev₂ t t' y (AddMonoidAlgebra.single m b) = y.left.appTop.hom b * ((chV t m.1).val * (chV t' m.2).val) :=
  ev_single _ _ _ _

theorem chV_comp {Z Z' : Over S} (σ : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (σ ≫ t) χ).val = σ.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem chV_ext {Z : Over S} {t t' : Z ⟶ splitTorus S X} (h : ∀ χ, (chV t χ).val = (chV t' χ).val) : t = t' :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))

theorem exists_point {U : Over S} {D : Type} [CommRing D] (e : Γ(U.left, ⊤) ≃+* D) (c : Multiplicative X →* Dˣ) :
    ∃ t : U ⟶ splitTorus S X, ∀ χ, e (chV t χ).val = (c (Multiplicative.ofAdd χ)).val :=
  ⟨(splitTorusPointsEquiv S X U).symm ((Units.map e.symm.toMonoidHom).comp c), fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; exact e.apply_symm_apply _⟩

theorem exists_coeffs [IsAffine Y.left] (f : Γ((splitTorus S X ⊗ splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X), ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift t (lift t' y)).left.appTop.hom f = ev₂ t t' y φ := by
  obtain ⟨U, y₀, e, -, he, hU⟩ := exists_ringPoint Y (AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, h₀⟩ := exists_point (S := S) e (mon _ (AddMonoidHom.inl X X))
  obtain ⟨t₁, h₁⟩ := exists_point (S := S) e (mon _ (AddMonoidHom.inr X X))
  refine ⟨e ((lift t₀ (lift t₁ y₀)).left.appTop.hom f), fun Z t t' y => ?_⟩
  obtain ⟨σ, hσ, Hσ⟩ := hU Z y (ev₂ t t' y) fun b => (ev₂_single t t' y 0 b).trans (by simp [chV_zero])
  have a₀ : σ ≫ t₀ = t := chV_ext fun χ => by
    rw [chV_comp, Hσ, h₀, mon_val, ev₂_single]; simp [chV_zero]
  have a₁ : σ ≫ t₁ = t' := chV_ext fun χ => by
    rw [chV_comp, Hσ, h₁, mon_val, ev₂_single]; simp [chV_zero]
  rw [← Hσ, Rosenlicht.over_appTop_comp, comp_lift, comp_lift, a₀, a₁, hσ]

theorem appTop_ev₁ {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (a : AddMonoidAlgebra Γ(Y.left, ⊤) X) :
    (lift t y).left.appTop.hom (ev₁ (fst (splitTorus S X) Y) (snd _ _) a) = ev₁ t y a :=
  hom_eq ((lift t y).left.appTop.hom.comp (ev₁ (fst (splitTorus S X) Y) (snd _ _))) _ (fun m b => by
    rw [RingHom.comp_apply, ev₁_single, ev₁_single, map_mul, ← chV_comp, Rosenlicht.over_appTop_comp, lift_fst,
      lift_snd]) a

abbrev pl {Z W : Scheme.{0}} (r : Z ⟶ W) (u : Γ(W, ⊤)ˣ) : Γ(Z, ⊤)ˣ := Units.map r.appTop.hom.toMonoidHom u

theorem gm_mul_iff {Z W W' W'' : Scheme.{0}} (r₁ : Z ⟶ W) (r₂ : Z ⟶ W') (r₃ : Z ⟶ W'') (r₄ : Z ⟶ W'')
    (u : Γ(W, ⊤)ˣ) (v : Γ(W', ⊤)ˣ) (w : Γ(W'', ⊤)ˣ) :
    (∀ z, gm r₁ z ⊤ u * gm r₂ z ⊤ v = gm r₃ z ⊤ w * gm r₄ z ⊤ w) ↔
      r₁.appTop.hom u.val * r₂.appTop.hom v.val = r₃.appTop.hom w.val * r₄.appTop.hom w.val := by
  have e : ∀ z, (gm r₁ z ⊤ u * gm r₂ z ⊤ v = gm r₃ z ⊤ w * gm r₄ z ⊤ w) =
      (gm (𝟙 Z) z ⊤ (pl r₁ u * pl r₂ v) = gm (𝟙 Z) z ⊤ (pl r₃ w * pl r₄ w)) := fun z => by
    rw [map_mul, map_mul, gm_top r₁, gm_top r₂, gm_top r₃, gm_top r₄]
  simp only [e]
  exact ⟨fun h => congrArg Units.val (unit_ext fun z _ => h z), fun h z => congrArg _ (Units.ext h)⟩

theorem gm_one_iff {Z W : Scheme.{0}} (r : Z ⟶ W) (u : Γ(W, ⊤)ˣ) :
    (∀ z, gm r z ⊤ u = 1) ↔ r.appTop.hom u.val = 1 := by
  have e : ∀ z, (gm r z ⊤ u = 1) = (gm (𝟙 Z) z ⊤ (pl r u) = gm (𝟙 Z) z ⊤ 1) := fun z => by
    rw [map_one, gm_top r]
  simp only [e]
  exact ⟨fun h => congrArg Units.val (unit_ext fun z _ => h z), fun h z => congrArg _ (Units.ext h)⟩

theorem cocycle_of_points [IsAffine Y.left] (φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    (h : ∀ (Z : Over S) (t t' t'' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      ev₂ (t * t') t'' y φ * ev₂ t t' y φ = ev₂ t (t' * t'') y φ * ev₂ t' t'' y φ) :
    AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) φ *
        AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) φ =
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) φ *
        AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) φ := by
  obtain ⟨U, y₀, e, -, he, -⟩ := exists_ringPoint Y (AddMonoidAlgebra Γ(Y.left, ⊤) (X × X × X))
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, h₀⟩ := exists_point (S := S) e (mon _ (AddMonoidHom.inl X (X × X)))
  obtain ⟨t₁, h₁⟩ := exists_point (S := S) e (mon _ ((AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inl X X)))
  obtain ⟨t₂, h₂⟩ := exists_point (S := S) e (mon _ ((AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inr X X)))
  have key : ∀ (s : X × X → X × X × X) (t t' : U ⟶ splitTorus S X),
      (∀ m : X × X, e (chV t m.1).val * e (chV t' m.2).val = AddMonoidAlgebra.single (s m) 1) →
      AddMonoidAlgebra.mapDomain s φ = e (ev₂ t t' y₀ φ) := fun s t t' H =>
    map_mapDomain s (RingHom.id _) (e.toRingHom.comp (ev₂ t t' y₀)) (fun m b => by
      change _ = e (ev₂ t t' y₀ _)
      rw [ev₂_single, map_mul, map_mul, H, he]
      simp [AddMonoidAlgebra.single_mul_single]) φ
  rw [key _ (t₀ * t₁) t₂, key _ t₀ t₁, key _ t₀ (t₁ * t₂), key _ t₁ t₂, ← map_mul, ← map_mul, h]
  all_goals
    intro m
    simp [chV_mul, h₀, h₁, h₂, mon_val, AddMonoidAlgebra.single_mul_single]

end Geo

section Red
variable {A : Type} [CommRing A] (J : Ideal A) {X : Type} [AddCommGroup X] {Y : Over (Spec (CommRingCat.of A))}

theorem coeff_mem_of_points [IsAffine Y.left] (φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    (h : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) →
      ∀ (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), ev₂ t t' y φ = 1) (p : X × X) :
    (φ - 1).coeff p ∈ J.map (strMap Y) := by
  obtain ⟨I, hI⟩ : ∃ I, I = J.map (strMap Y) := ⟨_, rfl⟩
  rw [← hI]
  obtain ⟨U, y₀, e, -, he, -⟩ := exists_ringPoint Y (AddMonoidAlgebra (Γ(Y.left, ⊤) ⧸ I) (X × X))
    (AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk I))
  obtain ⟨t₀, h₀⟩ := exists_point e (mon _ (AddMonoidHom.inl X X))
  obtain ⟨t₁, h₁⟩ := exists_point e (mon _ (AddMonoidHom.inr X X))
  have hU : ∃ s, s ≫ red J = U.hom := (exists_comp_red_iff J U).2 fun a ha => e.injective (by
    have : Ideal.Quotient.mk I (strMap Y a) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hI ▸ Ideal.mem_map_of_mem _ ha)
    rw [← appTop_strMap y₀, he, RingHom.comp_apply, this, map_zero, map_zero])
  refine coeff_mem I (e.toRingHom.comp (ev₂ t₀ t₁ y₀)) (fun m b => ?_) φ
    ((congrArg e (h U hU t₀ t₁ y₀)).trans (map_one e)) p
  change e (ev₂ t₀ t₁ y₀ _) = _
  rw [ev₂_single, map_mul, map_mul, he, h₀, h₁, mon_val, mon_val]
  simp [AddMonoidAlgebra.single_mul_single]

end Red

theorem exists_coboundary : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (Y : Over (Spec (CommRingCat.of A))) [IsAffine Y.left] (f : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ), (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' t'' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift (t * t') (lift t'' y)).left z ⊤ f * gm (lift t (lift t' y)).left z ⊤ f = gm (lift t (lift (t' * t'') y)).left z ⊤ f * gm (lift t' (lift t'' y)).left z ⊤ f) → (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t (lift t' y)).left z ⊤ f = 1) → ∃ g : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ, (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t (lift t' y)).left z ⊤ f * gm (lift (t * t') y).left z ⊤ g = gm (lift t y).left z ⊤ g * gm (lift t' y).left z ⊤ g) ∧ (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t y).left z ⊤ g = 1) := by
  intro A _ J hJ X _ Y _ f hc h1
  obtain ⟨φ, hφ⟩ := exists_coeffs f.val
  have hI : IsNilpotent (J.map (strMap Y)) := by
    obtain ⟨n, hn⟩ := hJ
    exact ⟨n, by rw [← Ideal.map_pow, hn]; exact Ideal.map_bot⟩
  obtain ⟨u, hu, Hu⟩ := GlobalTheory.T.exists_unit_coboundary_of_cocycle_addMonoidAlgebra _ _ hI X φ
    (coeff_mem_of_points J φ fun Z hZ t t' y => (hφ Z t t' y).symm.trans ((gm_one_iff _ _).1 (h1 Z hZ t t' y)))
    (cocycle_of_points φ fun Z t t' t'' y => by
      rw [← hφ, ← hφ, ← hφ, ← hφ]
      exact (gm_mul_iff _ _ _ _ _ _ _).1 (hc Z t t' t'' y))
  refine ⟨Units.map (ev₁ (fst _ Y) (snd _ _)).toMonoidHom u, fun Z t t' y => (gm_mul_iff _ _ _ _ _ _ _).2 ?_,
    fun Z hZ t y => (gm_one_iff _ _).2 ?_⟩
  · have e := congrArg (ev₂ t t' y) Hu
    rw [map_mul, map_mul, map_mapDomain _ _ (ev₁ (t * t') y), map_mapDomain _ _ (ev₁ t y),
      map_mapDomain _ _ (ev₁ t' y), ← hφ, ← appTop_ev₁ (t * t'), ← appTop_ev₁ t, ← appTop_ev₁ t'] at e
    · exact e
    all_goals
      intro m b
      simp [ev₁_single, ev₂_single, chV_mul, chV_zero]
  · refine (appTop_ev₁ t y u.val).trans ?_
    have hle : J.map (strMap Y) ≤ RingHom.ker y.left.appTop.hom := Ideal.map_le_iff_le_comap.2 fun a ha =>
      (appTop_strMap y a).trans ((exists_comp_red_iff J Z).1 hZ a ha)
    have e : ev₁ t y (u.val - 1) = 0 := ev_eq_zero _ _ _ fun m => hle (hu m)
    rwa [map_sub, map_one, sub_eq_zero] at e

end GlobalTheory.UU.UnitCob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expandsAt_translate_torsion_alt : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → gp.b ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∃ (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![eSec D.toPre.P.A, gp.b.left] (DegPre.lineε k))) (uL : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (𝟙 G * (toUnit G ≫ x)).left] ![(k : ℤ), -(k : ℤ)])) (uM : ∀ α, LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (D.toPre.famφB α) (fun i => (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k))), ν.IsGen ∧ uL.IsGen ∧ (∀ α, (uM α).IsGen ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (uM α) (eSec D.toPre.P.A)) (LB.mulGen D.toPre.P.L _ _ _ _ (gp.s α) ν)) ∧ ∀ (σ σ' : H0 U.LG.L k) (f f' : ∀ α, D.toPre.SecB k α), GeneratorPullback.SecRel U.LG.L _ _ σ' _ _ σ (𝟙 G * (toUnit G ≫ x)).left _ _ uL → (∀ α, GeneratorPullback.SecRel D.toPre.P.L _ _ (f' α) _ _ (f α) (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left _ _ (uM α)) → ∀ e, U.ExpandsAt e k σ f → U.ExpandsAt e k σ' f' := by
  first | exact @GlobalTheory.expandsAt_translate_torsion | exact GlobalTheory.expandsAt_translate_torsion | (intros; apply GlobalTheory.expandsAt_translate_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordEndRatioDescendsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gen_of_torusEnd_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G) (aB : D.P.A ⟶ D.P.A) (h : D.X → D.X) (t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X), IsMonHom a → TorusEndOf D.X h t → g.i ≫ a = t ≫ g.i → a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map aB → ∀ χ : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (fun k => pullback.fst D.P.A.hom (thick R I e) ≫ Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (Sum.elim Oε Oinvε)), u.IsGen ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J → val (g.t χ) (x ≫ a.left) z J = val (g.t (h χ)) x z J * val u (x ≫ g.q.left) z J := by
  first | exact @GlobalTheory.gtCoord_end_ratio_descends | exact GlobalTheory.gtCoord_end_ratio_descends | (intros; apply GlobalTheory.gtCoord_end_ratio_descends <;> assumption)
end

