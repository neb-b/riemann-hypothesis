module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueExtensionOfForallNormLeOne
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GoodCurvesPairingMemMaxIdeal
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0061
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterOnTorsionPointsEqSeries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem character_on_torsion_points_eq_series : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (k : ℕ) (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Killed F.F (p ^ k) φ → Killed F.F (p ^ k) φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, ∀ φ, Killed F.F (p ^ k) φ → algebraMap O C (φ u) = κ φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F hFH k κ hmul hone
  obtain ⟨inst, hsum, hzero, hkill⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  letI := inst
  obtain ⟨hfree, hfin, -⟩ := hFH k
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain (algebraMap O C)
  set J : Ideal (PS O 1 d) := Ideal.span (Set.range (mulF F.F (p ^ k))) with hJ
  let N : AddSubmonoid (PS O 1 d →ₐ[O] O) :=
    { carrier := {φ | (p ^ k) • φ = 0}
      zero_mem' := nsmul_zero _
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [nsmul_add, ha, hb, add_zero] }
  have hN : ∀ n : N, Killed F.F (p ^ k) n.1 := fun n => (hkill _ _).1 n.2
  have hNJ : ∀ n : N, ∀ u ∈ J, n.1 u = 0 := by
    intro n u hu
    have hle : J ≤ RingHom.ker n.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hN n j
    exact hle hu
  let L : N → (QF F.F (p ^ k) →ₐ[O] O) := fun n => Ideal.Quotient.liftₐ J n.1 (hNJ n)
  have hL : ∀ (n : N) (u : PS O 1 d), L n (Ideal.Quotient.mk J u) = n.1 u := fun n u => rfl
  have hLinj : Function.Injective L := by
    intro a b hab
    apply Subtype.ext
    apply AlgHom.ext
    intro u
    rw [← hL, ← hL, hab]
  haveI : Finite N := Finite.of_injective L hLinj
  let T : QF F.F (p ^ k) →ₗ[O] (N → C) :=
    LinearMap.pi fun n => (Algebra.linearMap O C).comp (L n).toLinearMap
  have hmem : ∀ f : N → C, f ∈ LinearMap.range T ↔
      ∃ u : PS O 1 d, ∀ n : N, algebraMap O C (n.1 u) = f n := by
    intro f
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact ⟨u, fun n => rfl⟩
    · rintro ⟨u, hu⟩
      exact ⟨Ideal.Quotient.mk J u, funext hu⟩
  have hfg : (LinearMap.range T).FG := Module.Finite.iff_fg.1 inferInstance
  have hspan : Submodule.span C ((LinearMap.range T : Submodule O (N → C)) : Set (N → C)) = ⊤ := by
    let e : N → (PS O 1 d →* C) := fun n =>
      ((algebraMap O C).comp (n.1 : PS O 1 d →+* O) : PS O 1 d →+* C).toMonoidHom
    have he : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      apply AlgHom.ext
      intro u
      exact hinj (DFunLike.congr_fun hab u)
    have hli : LinearIndependent C (fun n : N => (e n : PS O 1 d → C)) :=
      (linearIndependent_monoidHom (PS O 1 d) C).comp e he
    have htop := span_flip_eq_top_iff_linearIndependent.2 hli
    rw [eq_top_iff, ← htop]
    apply Submodule.span_mono
    rintro _ ⟨u, rfl⟩
    exact (hmem _).2 ⟨u, fun n => rfl⟩
  have key := GlobalTheory.character_mem_lattice_of_comul C v O hv N (LinearMap.range T) hfg hspan ?_ ?_
    (fun n => κ n.1) (hone _ hzero)
    (fun x y => hmul _ _ _ (hN x) (hN y) ((hsum _ _ _).2 rfl))
  · obtain ⟨u, hu⟩ := (hmem _).1 key
    exact ⟨u, fun φ hφ => hu ⟨φ, (hkill _ _).2 hφ⟩⟩
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    obtain ⟨m, g, h, hgh⟩ := GlobalTheory.T.exists_sum_mul_eval_two_points_of_free_finite_quotient p C v O hv d J hfree hfin (ev (n := 2) ![F.F] u)
    refine ⟨m, fun i n => algebraMap O C (n.1 (g i)), fun i n => algebraMap O C (n.1 (h i)),
      fun i => (hmem _).2 ⟨g i, fun n => rfl⟩, fun i => (hmem _).2 ⟨h i, fun n => rfl⟩, ?_⟩
    intro x y
    obtain ⟨Φ, h0, h1, h2⟩ := (hsum x.1 y.1 (x + y).1).2 rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hu, ← h2, hgh Φ x.1 y.1 h0 h1 (hNJ x) (hNJ y), map_sum]
    simp only [map_mul]
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    exact ⟨_, hu 0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSectionOfPow
section
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechRoot

theorem gen_res {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} [Nonempty V] [Nonempty W]
    (h : W ≤ V) (s : Γ(X, V)) :
    (X.germToFunctionField W).hom ((X.presheaf.map (homOfLE h).op).hom s) = (X.germToFunctionField V).hom s :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ s

theorem nonempty_inf {X : Scheme.{0}} [IsIntegral X] (V W : X.Opens) [hV : Nonempty V] [hW : Nonempty W] :
    Nonempty (V ⊓ W : X.Opens) := by
  obtain ⟨⟨v, hv⟩⟩ := hV
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen ⟨v, hv⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

theorem exists_section_of_pow {X : Scheme.{0}} [IsIntegral X] (hN : ∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b))
    {l : ℕ} (hl : 0 < l) (V : X.Opens) [Nonempty V] (f : Γ(X, V)) (t : X.functionField)
    (ht : t ^ l = (X.germToFunctionField V).hom f) : ∃ s : Γ(X, V), (X.germToFunctionField V).hom s = t := by
  refine IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  refine exists_germToFunctionField_eq_of_mem_range_stalk ?_ hx
  haveI := hN x
  refine IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow hl ?_)
  rw [ht, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx f]
  exact isIntegral_algebraMap

theorem charP_functionField {X : Scheme.{0}} [IsIntegral X] (l : ℕ) [Fact l.Prime] (h : (l : Γ(X, ⊤)) = 0) :
    CharP X.functionField l := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
  rw [← map_natCast (X.germToFunctionField ⊤).hom, h, map_zero]

theorem exists_root : ∀ (X : Scheme.{0}) [IsIntegral X], (∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b)) → ∀ (l : ℕ) [Fact l.Prime], (l : Γ(X, ⊤)) = 0 → ∀ (J : Type) (U : J → X.Opens) (f : ∀ j, Γ(X, U j)) (n : ∀ j j', Γ(X, U j ⊓ U j')), (∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (f j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (f j') = n j j' ^ l) → ∀ (i : J) (b : X) (hb : b ∈ U i) (h : FractionRing (X.presheaf.stalk b)), h ^ l = algebraMap (X.presheaf.stalk b) _ ((X.presheaf.germ (U i) b hb).hom (f i)) → ∃ H : ∀ j, Γ(X, U j), ∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (H j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (H j') = n j j' := by
  intro X _ hN l _ hl J U f n hf i b hb h hh
  haveI := charP_functionField l hl
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  haveI : Nonempty (U i) := ⟨⟨b, hb⟩⟩
  let e := FractionRing.algEquiv (X.presheaf.stalk b) X.functionField
  have he : e h ^ l = (X.germToFunctionField (U i)).hom (f i) := by
    rw [← map_pow, hh, AlgEquiv.commutes]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hb (f i)
  have hg : ∀ j j' [Nonempty (U j)] [Nonempty (U j')] [Nonempty (U j ⊓ U j' : X.Opens)],
      (X.germToFunctionField (U j)).hom (f j) - (X.germToFunctionField (U j')).hom (f j') =
        (X.germToFunctionField (U j ⊓ U j')).hom (n j j') ^ l := by
    intro j j' _ _ _
    rw [← map_pow, ← hf, map_sub, gen_res, gen_res]
  have ex : ∀ j, ∃ H : Γ(X, U j), ∀ [Nonempty (U j)],
      (X.germToFunctionField (U j)).hom H ^ l = (X.germToFunctionField (U j)).hom (f j) := by
    intro j
    by_cases hj : Nonempty (U j)
    · haveI := nonempty_inf (U j) (U i)
      have ht : (e h + (X.germToFunctionField (U j ⊓ U i)).hom (n j i)) ^ l =
          (X.germToFunctionField (U j)).hom (f j) := by
        rw [add_pow_char, he, ← hg, add_sub_cancel]
      obtain ⟨s, hs⟩ := exists_section_of_pow hN hl0 (U j) (f j) _ ht
      exact ⟨s, by intro _; rw [hs, ht]⟩
    · exact ⟨0, by intro h; exact absurd h hj⟩
  choose H hH using ex
  refine ⟨H, fun j j' => ?_⟩
  by_cases hj : Nonempty (U j ⊓ U j' : X.Opens)
  · obtain ⟨⟨z, hz⟩⟩ := id hj
    haveI : Nonempty (U j) := ⟨⟨z, hz.1⟩⟩
    haveI : Nonempty (U j') := ⟨⟨z, hz.2⟩⟩
    apply X.germToFunctionField_injective (U j ⊓ U j')
    apply frobenius_inj X.functionField l
    change (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l = (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l
    rw [map_sub, gen_res, gen_res, sub_pow_char, hH, hH, hg]
  · exact fn_ext (V := U j ⊓ U j') fun x hx => absurd ⟨⟨x, hx⟩⟩ hj

end GlobalTheory.CechRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecond
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowKernel

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_sum {ι : Type} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  V.v.map_lt_sum (by simp) h

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_int_mul hb ha

theorem mm_ge {a : C} (h : V.MM a) : V.Ge 0 a := le_of_lt h

theorem not_mm_one : ¬ V.MM (1 : C) := by simp [VF.MM]

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  have h' : (0 : WithTop ℝ) ≤ V.v (a ^ n) := h
  show (0 : WithTop ℝ) ≤ V.v a
  rw [V.v.map_pow] at h'
  by_contra hc
  exact absurd (nsmul_neg (not_le.mp hc) hn) (not_lt.mpr h')

theorem ge_div {a b : C} (hb : b ≠ 0) (h : V.v b ≤ V.v a) : V.Ge 0 (a / b) := by
  show (0 : WithTop ℝ) ≤ V.v (a / b)
  have e : V.v a = V.v (a / b) + V.v b := by rw [← V.v.map_mul, div_mul_cancel₀ a hb]
  have hb' : V.v b ≠ ⊤ := by simpa using hb
  rw [e] at h
  exact (WithTop.add_le_add_iff_right hb').mp (by simpa using h)

theorem card_add_le {σ : Type} [Fintype σ] (p : σ → Prop) [DecidablePred p] {N M : ℕ}
    (A : Fin N → σ → C) (B : Fin M → σ → C) (hA : IndepMod V A) (hAp : ∀ ν s, ¬ p s → A ν s = 0)
    (hB : IsSat V B) (hBp : ∀ μ s, ¬ p s → B μ s = 0) (hAB : ∀ ν μ, V.MM (∑ s, A ν s * B μ s)) :
    N + M ≤ (Finset.univ.filter p).card := by
  classical
  obtain ⟨-, W, hW, hBW⟩ := hB
  let F : Fin N ⊕ Fin M → {s // p s} → C := Sum.elim (fun ν s => A ν s.1) (fun μ s => W s.1 μ)
  have hF : LinearIndependent C F := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ s, p s → ∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ = 0 := by
      intro s hs
      have := congrFun hg ⟨s, hs⟩
      simpa [F, Fintype.sum_sum_type, Finset.sum_apply] using this
    have h2 : ∀ μ', g (Sum.inr μ') = -∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
      intro μ'
      have h3 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s + ∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = 0 :=
        Finset.sum_eq_zero fun s _ => by
          by_cases hs : p s
          · rw [h1 s hs, zero_mul]
          · rw [hBp μ' s hs, mul_zero]
      have h4 : ∑ s, (∑ μ, g (Sum.inr μ) * W s μ) * B μ' s = g (Sum.inr μ') := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        have : ∀ μ, ∑ s, g (Sum.inr μ) * W s μ * B μ' s = g (Sum.inr μ) * if μ' = μ then 1 else 0 := by
          intro μ
          rw [← hBW μ' μ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        simp [this]
      have h5 : ∑ s, (∑ ν, g (Sum.inl ν) * A ν s) * B μ' s = ∑ ν, g (Sum.inl ν) * ∑ s, A ν s * B μ' s := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun s _ => by ring
      simp only [add_mul, Finset.sum_add_distrib] at h3
      rw [h4, h5] at h3
      linear_combination h3
    have h6 : ∀ ν, g (Sum.inl ν) = 0 := by
      by_contra hc
      push_neg at hc
      obtain ⟨ν1, hν1⟩ := hc
      obtain ⟨ν0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun ν => V.v (g (Sum.inl ν)))
        ⟨ν1, Finset.mem_univ _⟩
      have h0 : g (Sum.inl ν0) ≠ 0 := by
        intro h0
        have := hmin ν1 (Finset.mem_univ _)
        rw [h0, V.v.map_zero, top_le_iff] at this
        exact hν1 (by simpa using this)
      have hint : ∀ ν, V.Ge 0 (g (Sum.inl ν) / g (Sum.inl ν0)) := fun ν =>
        ge_div h0 (hmin ν (Finset.mem_univ _))
      have key := hA (fun ν => g (Sum.inl ν) / g (Sum.inl ν0)) hint (fun s => by
        by_cases hs : p s
        · have e : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
              ∑ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) * W s μ := by
            have e1 : ∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * A ν s =
                (g (Sum.inl ν0))⁻¹ * ∑ ν, g (Sum.inl ν) * A ν s := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e2 : ∀ μ, (∑ ν, g (Sum.inl ν) / g (Sum.inl ν0) * ∑ s, A ν s * B μ s) =
                -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) := by
              intro μ
              rw [h2 μ, mul_neg, neg_neg, Finset.mul_sum]
              exact Finset.sum_congr rfl fun ν _ => by ring
            have e3 : ∑ μ, -((g (Sum.inl ν0))⁻¹ * g (Sum.inr μ)) * W s μ =
                -((g (Sum.inl ν0))⁻¹ * ∑ μ, g (Sum.inr μ) * W s μ) := by
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun ν _ => by ring
            simp only [e2]
            rw [e1, e3]
            linear_combination (g (Sum.inl ν0))⁻¹ * h1 s hs
          rw [e]
          exact mm_sum fun μ _ => mm_mul_int (mm_sum fun ν _ => mm_int_mul (hint ν) (hAB ν μ)) (hW s μ)
        · simp only [hAp _ s hs, mul_zero, Finset.sum_const_zero]
          exact mm_zero) ν0
      simp only [div_self h0] at key
      exact not_mm_one key
    intro i
    cases i with
    | inl ν => exact h6 ν
    | inr μ => rw [h2 μ]; simp [h6]
  have := hF.fintype_card_le_finrank
  simpa [Fintype.card_subtype] using this

theorem mm_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.MM a) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ]
  exact mm_int_mul ((mm_ge h).pow m) h

theorem independenceBoundCondition_of_rankMaximalCondition : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, RawChart.RankMaximalCondition H → RawChart.IndependenceBoundCondition H := by
  intro C _ V d _ I _ κ _ X hL hR H h2 hA g a ha N w x hgood hV hind
  classical
  haveI := hL.closed
  have hstep := CharacteristicFromRanks.alt_step X.big hR.big_compl hA
  have hb1 : X.big (1 - g) (a + 1) := (hR.big_compl g (a + 1)).2 fun h => (hstep g a).1 h ha
  have hb2 : ¬ X.big (1 - g) (a + 1 + 1) := fun h => (hstep (1 - g) (a + 1)).1 h hb1
  obtain ⟨M, w', x', hgood', hsupp, hsat, hcard⟩ :=
    _root_.GlobalTheory.GoodCorank.exists_good_sat C V d (I (1 - g)) (JJ I (1 - g)) (RawChart.cart (H (1 - g))) (a + 1)
  have c1 := hR.rk_big (1 - g) (a + 1) hb1
  have c2 := hR.rk_small (1 - g) (a + 1 + 1) hb2
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  have hind' : IndepMod V (fun ν => (RawChart.cart (H g)).c0' (x ν)) := by
    intro c hc hmm
    choose co hco using fun ν => IsAlgClosed.exists_pow_nat_eq (c ν) (Nat.pos_of_ne_zero hl)
    have hcoi : ∀ ν, V.Ge 0 (co ν) := fun ν => ge_of_pow hl (by rw [hco]; exact hc ν)
    have hG := Cart.Good.comb Finset.univ (fun ν _ => hcoi ν) (fun ν _ => hgood ν)
    have h3 := h2 hA g a ha _ _ hG (fun q => by
      rw [Cart.c0'_comb]
      simp only [hco]
      exact hmm q)
    have h4 := hind co hcoi (fun k => by simpa [Finset.sum_apply] using h3 k)
    intro ν
    rw [← hco ν]
    exact mm_pow hl (h4 ν)
  have key := card_add_le (V := V) (fun c : I (1 - g) => X.ty (1 - g) c = a + 1)
    (fun ν => (RawChart.cart (H g)).c0' (x ν)) w' hind'
    (fun ν s hs => by
      have := (hgood ν).1.2.2 1 (Sum.inr s) (by simpa [RawChart.cart, RawChart.tyC] using hs)
      simp [Cart.c0', this])
    hsat (fun μ s hs => hsupp μ s hs)
    (fun ν μ => _root_.GlobalTheory.RowLaw.good_pairing_mem_max C V d I κ X hL H g a (a + 1) (w ν) (x ν) (w' μ) (x' μ) (hgood ν) (hgood' μ) (hV ν))
  have hcard' : X.n + X.j ≤ M + X.j' := by
    rw [← c1, ← c2]
    convert hcard <;> rfl
  have key' : N + M ≤ X.n + X.j := by
    rw [← c1]
    convert key
  omega

end GlobalTheory.RowKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantValueCopiesEqZeroOfLowCoeff
section
set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.PowGerm

theorem nabValN_eq_zero_of_coeff_eq_zero :
    ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u f P hf
  classical
  unfold nabValN
  rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hdeg : a.degree ≤ P.totalDegree := by
    have := MvPolynomial.le_totalDegree ha
    rwa [Finsupp.degree_apply]
  rw [NabJet.constantCoeff_DmonN_congr _ cp u a _ 0 fun mo hmo => ?_,
    (NabJet.isLinearMap_DmonN (B.FK K) cp u a).map_zero, map_zero, mul_zero]
  rw [NabJet.coeff_mul_congr P.totalDegree f 0 _ (fun b hb => by rw [hf b hb, map_zero]) mo (hmo.trans hdeg), zero_mul]

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsLocalRingOfAug
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve

namespace GlobalTheory.StalkJet

variable {k : Type} [Field k]

theorem isLocalRing_of_aug {A : Type} [CommRing A] [Algebra k A] (aug : A →ₐ[k] k) {n : ℕ}
    (h : RingHom.ker aug ^ n = ⊥) : IsLocalRing A := by
  haveI : Nontrivial A := (aug : A →+* k).domain_nontrivial
  have nil : ∀ a : A, aug a = 0 → IsNilpotent a := fun a ha =>
    ⟨n, by rw [← Ideal.mem_bot, ← h]; exact Ideal.pow_mem_pow ha n⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : aug a = 0
  · exact Or.inr (nil a ha).isUnit_one_sub
  · left
    have h1 : IsNilpotent (a - algebraMap k A (aug a)) := nil _ (by simp)
    have h2 : IsUnit (algebraMap k A (aug a)) := (IsUnit.mk0 _ ha).map _
    have := h1.isUnit_add_right_of_commute h2 (Commute.all _ _)
    simpa using this

theorem exists_factor {B : Over (Sp k)} (b : B.left) [Algebra k (B.left.presheaf.stalk b)]
    (hb : B.left.fromSpecStalk b ≫ B.hom = spMap (algebraMap k (B.left.presheaf.stalk b)))
    {A : Type} [CommRing A] [Algebra k A] [IsLocalRing A] (y : algOver k A ⟶ B)
    (hy : y.left (closedPoint A) = b) :
    ∃ τ : B.left.presheaf.stalk b →ₐ[k] A, IsLocalHom τ ∧
      spMap (τ : B.left.presheaf.stalk b →+* A) ≫ B.left.fromSpecStalk b = y.left := by
  subst hy
  have e := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of A) y.left
  have w : y.left ≫ B.hom = spMap (algebraMap k A) := Over.w y
  have e2 : CommRingCat.ofHom (algebraMap k (B.left.presheaf.stalk (y.left (closedPoint A)))) ≫
      Scheme.stalkClosedPointTo (R := .of A) y.left = CommRingCat.ofHom (algebraMap k A) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ w
    exact (congrArg (Spec.map (Scheme.stalkClosedPointTo (R := .of A) y.left) ≫ ·) hb.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.hom) e))
  refine ⟨⟨(Scheme.stalkClosedPointTo (R := .of A) y.left).hom, fun c => ?_⟩, ?_, e⟩
  · exact congrArg (fun q => q.hom c) e2
  · exact ⟨(Scheme.isLocalHom_stalkClosedPointTo' (R := A) y.left).1⟩

end GlobalTheory.StalkJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicPlaceBasisOfIdempotentStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_place_basis_of_idempotent : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]) (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) → Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) → ∀ τ ∈ Emb (O := O) w.e, eigDim C (fun a : OE => (ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) ((algebraMap O C).comp τ) = h := by
  first | exact @GlobalTheory.ChF.eigDim_eq_of_basis | exact GlobalTheory.ChF.eigDim_eq_of_basis | (intros; apply GlobalTheory.ChF.eigDim_eq_of_basis <;> assumption)
end

