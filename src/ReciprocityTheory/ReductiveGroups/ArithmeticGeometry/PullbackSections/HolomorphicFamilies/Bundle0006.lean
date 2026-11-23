module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnGerm
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

section Pt

variable {K : Type} [Field K] {ι : Type} {m : ℕ}

end Pt

section PullSec

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A)
  (hh : h ≫ snd T A = snd T' A)

def anPullF (s : LB.Sec (LPow A L a T)) (j : Fin 1 → L.ι) : Γ((T' ⊗ A).left, (LPow A L a T').U j) :=
  ((T' ⊗ A).left.presheaf.map (homOfLE (chart_le_res A L h hh a j)).op).hom ((h.left.app _).hom (s.f j))

def pullSecLP (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') where
  f := anPullF A L a h hh s
  compat i j := fn_ext fun y hy => by
    have hi : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) i := chart_le_res A L h hh a i hy.1
    have hj : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) j := chart_le_res A L h hh a j hy.2
    have v : ∀ j', y ∈ (LPow A L a T').U j' → gs (𝟙 _) y _ (anPullF A L a h hh s j') =
        gs (𝟙 _ ≫ h.left) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j') (s.f j') := fun j' hj' =>
      (gs_res _ y _ hj' _).trans (gs_pull _ h.left y _ (chart_le_res A L h hh a j' hj') _)
    refine ((gs_res (𝟙 _) y _ hy _).trans ((v i hy.1).trans (sec_trans s (𝟙 _ ≫ h.left) y hi hj))).trans ?_
    refine Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm
    refine congrArg₂ (· * ·) ?_ ((v j hy.2).symm.trans (gs_res (𝟙 _) y _ hy _).symm)
    refine Eq.trans ?_ (gs_unit (𝟙 _) y _ hy _).symm
    refine congrArg Units.val (Eq.trans ?_
      (gm_linComb L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) (𝟙 _) y i j hy.1 hy.2).symm)
    simp only [trF, Category.assoc, ← Over.comp_left, hh]

theorem isPullSec_pullSecLP (s : LB.Sec (LPow A L a T)) : IsPullSec A L a h hh s (pullSecLP A L a h hh s) := fun _ => rfl

end PullSec

section Fam

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (L : LB G.left) {x0 : Sp ℂ ⟶ X} {g : ℕ}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (hol : IsHolFam e) (he : ∀ z, e z ≫ G.hom = x0)

def jB (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 :=
  Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m))) rfl

def xJ (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ G :=
  Over.homMk (jetPt e hol m) (jetPt_over e hol G.hom x0 he m)

def ePt (z : Fin g → ℂ) : Over.mk x0 ⟶ G := Over.homMk (e z) (he z)

def lftJ (z : Fin g → ℂ) : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left := (ptSecT G (ePt e he z)).left


end Fam

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetF
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

variable {Y : Scheme.{0}}


set_option backward.isDefEq.respectTransparency false in
theorem specMap_comp_appLE {A B : CommRingCat.{0}} (χ : A ⟶ B) (q : Spec A ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (Spec.map χ ≫ q) ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) :
    (Spec.map χ ≫ q).appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom =
      q.appLE U ⊤ hq ≫ (Scheme.ΓSpecIso A).hom ≫ χ := by
  have e0 : (Spec.map χ ≫ q).appLE U ⊤ h = q.app U ≫ (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h := by
    first
    | exact Scheme.Hom.comp_appLE _ _ _ _ _
    | (simp only [Scheme.Hom.appLE, Scheme.comp_app, Category.assoc]; rfl)
    | (simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc]; rfl)
    | (unfold Scheme.Hom.appLE; simp [Category.assoc])
  rw [e0]
  have e1 : (Spec.map χ).appLE (q ⁻¹ᵁ U) ⊤ h =
      (Spec A).presheaf.map (homOfLE hq).op ≫ (Spec.map χ).app ⊤ := by
    rw [Scheme.Hom.naturality]
    rfl
  rw [e1]
  simp only [Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact Scheme.ΓSpecIso_naturality χ

section Tan

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι]

theorem aeval_tan (ℓ : ι) (q : MvPolynomial ι K) :
    MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber K) else 0) q =
      TrivSqZeroExt.inl (MvPolynomial.constantCoeff q) +
        TrivSqZeroExt.inr (AddMonoidAlgebra.coeff q (Finsupp.single ℓ 1)) := by
  induction q using MvPolynomial.induction_on
  next a =>
    have hs : (0 : ι →₀ ℕ) ≠ Finsupp.single ℓ 1 := (Finsupp.single_ne_zero.2 one_ne_zero).symm
    ext <;> simp [MvPolynomial.coeff_C, hs, TrivSqZeroExt.algebraMap_eq_inl]
  next p q hp hq =>
    simp only [map_add (f := _), hp, hq, MvPolynomial.coeff_add, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  next p i hp =>
    rw [map_mul, hp, MvPolynomial.aeval_X]
    by_cases h : i = ℓ
    · subst h
      have hc : AddMonoidAlgebra.coeff (p * MvPolynomial.X i) (Finsupp.single i 1) =
          MvPolynomial.constantCoeff p := by
        have := MvPolynomial.coeff_mul_X (0 : ι →₀ ℕ) i p
        rw [zero_add] at this
        exact this
      rw [hc]
      ext <;> simp
    · have h' : ℓ ≠ i := Ne.symm h
      have hc : AddMonoidAlgebra.coeff (p * MvPolynomial.X i) (Finsupp.single ℓ 1) = 0 := by
        rw [MvPolynomial.coeff_mul_X']
        simp [Finsupp.single_apply, h', h]
      rw [hc]
      ext <;> simp [h]

end Tan

variable {g : ℕ}

private theorem coeff_psTrunc_lemma {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (f : MvPowerSeries ι ℂ) (n : ι →₀ ℕ) (hn : n ∈ degLE (ι := ι) m) :
    AddMonoidAlgebra.coeff (psTrunc m f) n = MvPowerSeries.coeff n f := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, hn]

private theorem mem_degLE_lemma_2 {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (n : ι →₀ ℕ)
    (hb : ∀ i, n i ≤ m) (hs : (n.sum fun _ k => k) ≤ m) : n ∈ degLE (ι := ι) m := by
  unfold degLE
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun i => ⟨n i, Nat.lt_succ_of_le (hb i)⟩,
    Finset.mem_univ _, ?_⟩, hs⟩
  ext i
  simp

theorem jetTan_jetOf (ℓ : Fin 1 × Fin g) (θ : (Fin g → ℂ) → ℂ) :
    (jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) θ) =
      TrivSqZeroExt.inl (θ 0) + TrivSqZeroExt.inr (fderiv ℂ θ 0 (Pi.single ℓ.2 1)) := by
  have h1 : (jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) θ) =
      MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0)
        (psTrunc (0 + 1) (tay θ 0)) := rfl
  have hc : ∀ n, MvPowerSeries.coeff n (tay θ 0) = mD θ 0 (dirs n + 0) / fct n := fun n => rfl
  have hb0 : ∀ i, (0 : Fin 1 × Fin g →₀ ℕ) i ≤ 0 + 1 := by simp
  have hs0 : ((0 : Fin 1 × Fin g →₀ ℕ).sum fun _ k => k) ≤ 0 + 1 := by simp
  have h0 : MvPolynomial.constantCoeff (psTrunc (0 + 1) (tay θ 0)) = θ 0 := by
    have hd0 : dirs (0 : Fin 1 × Fin g →₀ ℕ) = 0 := by simp [dirs]
    have hf0 : fct (0 : Fin 1 × Fin g →₀ ℕ) = 1 := by simp [fct]
    have hm0 : mD θ 0 (0 : Multiset (Fin g → ℂ)) = θ 0 := by
      unfold mD
      rw [Multiset.toList_zero]
      unfold lD
      exact iteratedFDeriv_zero_apply _
    rw [MvPolynomial.constantCoeff_eq,
      coeff_psTrunc_lemma (0 + 1) (tay θ 0) 0 (mem_degLE_lemma_2 (0 + 1) 0 hb0 hs0), hc,
      hd0, add_zero, hf0, div_one, hm0]
  have hb1 : ∀ i, (Finsupp.single ℓ 1 : Fin 1 × Fin g →₀ ℕ) i ≤ 0 + 1 := by
    intro i
    rw [Finsupp.single_apply]
    split_ifs <;> omega
  have hs1 : ((Finsupp.single ℓ 1 : Fin 1 × Fin g →₀ ℕ).sum fun _ k => k) ≤ 0 + 1 := by
    simp [Finsupp.sum_single_index]
  have hd : dirs (Finsupp.single ℓ 1) = {(Pi.single ℓ.2 1 : Fin g → ℂ)} := by
    simp [dirs, Finsupp.toMultiset_single]
  have hf : fct (Finsupp.single ℓ 1) = 1 := by
    unfold fct
    refine Finset.prod_eq_one fun p _ => ?_
    rw [Finsupp.single_apply]
    split_ifs <;> simp
  have hm : mD θ 0 {(Pi.single ℓ.2 1 : Fin g → ℂ)} = fderiv ℂ θ 0 (Pi.single ℓ.2 1) := by
    unfold mD
    rw [Multiset.toList_singleton]
    unfold lD
    show iteratedFDeriv ℂ 1 θ 0 (fun i => [(Pi.single ℓ.2 1 : Fin g → ℂ)].get i) = _
    rw [iteratedFDeriv_one_apply]
    rfl
  have hl : AddMonoidAlgebra.coeff (psTrunc (0 + 1) (tay θ 0)) (Finsupp.single ℓ 1) =
      fderiv ℂ θ 0 (Pi.single ℓ.2 1) := by
    rw [coeff_psTrunc_lemma (0 + 1) (tay θ 0) (Finsupp.single ℓ 1)
      (mem_degLE_lemma_2 (0 + 1) (Finsupp.single ℓ 1) hb1 hs1), hc, hd, add_zero, hf, div_one, hm]
  rw [h1, aeval_tan, h0, hl]

theorem appLE_congr_hom {A : CommRingCat.{0}} {q q' : Spec A ⟶ Y} (hq : q = q') (U : Y.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U)
    (h' : ⊤ ≤ q' ⁻¹ᵁ U) : q.appLE U ⊤ h = q'.appLE U ⊤ h' := by
  subst hq
  rfl

theorem isLocalHom_jetTan (ℓ : Fin 1 × Fin g) :
    IsLocalHom ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) := by
  constructor
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : IsUnit (MvPolynomial.aeval
      (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0) p) := hx
  rw [aeval_tan] at hx'
  have hc : MvPolynomial.constantCoeff p ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hx'
    have := congrArg TrivSqZeroExt.fst u.mul_inv
    rw [TrivSqZeroExt.fst_mul, hu] at this
    simp [h0] at this
  have hq : p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ orig ℂ (Fin 1 × Fin g) := by
    unfold orig
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.mem_support_iff] at hm
      apply hm
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl]
      exact sub_self _
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hm0 (Finsupp.ext hne)
    exact ⟨i, Set.mem_univ _, hi⟩
  have hnil : IsNilpotent (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1))
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p))) := by
    refine ⟨0 + 1 + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hq _
  have hu : IsUnit (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1))
      (MvPolynomial.C (MvPolynomial.constantCoeff p))) :=
    ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C).map _
  have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
  simpa using this


set_option backward.isDefEq.respectTransparency false in
theorem jetPt_tan (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (ℓ : Fin 1 × Fin g)
    (v : Sp (DualNumber ℂ) ⟶ Y) (hd : IsDerivAt0 e (Pi.single ℓ.2 1) v) :
    spMap ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) ≫ jetPt e hol (0 + 1) = v := by
  haveI := isLocalHom_jetTan (g := g) ℓ
  haveI hfl : IsLocalHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol (0 + 1) V hV ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) =
      jetψ e hol (0 + 1) U hU ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol (0 + 1) U hU ≫ CommRingCat.ofHom
        ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
          Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ)) f) → e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply] at hf
    exact jetψ_loc e hol _ U hU f ((isLocalHom_jetTan ℓ).map_nonunit _ hf)
  have hpt := nbhdPt_closedPoint _ hres hloc
  have hv : v (IsLocalRing.closedPoint _) = e 0 cpt := by
    rw [← hd.1, Scheme.Hom.comp_apply, spMap, Spec_closedPoint]
  refine hom_ext_of_local (hpt.trans hv.symm) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  rw [nbhdPt_appLE _ hres hloc U hU h₁, Iso.comp_inv_eq]
  have h0 : ⊤ ≤ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v) ⁻¹ᵁ U := by
    have := top_le_of_mem hU
    rwa [← hd.1] at this
  have hfst := specMap_comp_appLE (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) v U h0 h₂
  rw [appLE_congr_hom hd.1 U h0 (top_le_of_mem hU)] at hfst
  have hf1 : ∀ f, (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((e 0).appLE U ⊤ (top_le_of_mem hU) f) =
      TrivSqZeroExt.fst ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom (v.appLE U ⊤ h₂ f)) := fun f => by
    have := ConcreteCategory.congr_hom hfst f
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    exact this
  ext f
  · rw [CommRingCat.comp_apply, jetψ_apply]
    change ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).fst = _
    rw [jetTan_jetOf, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      valAt'_of _ _ (top_le_of_mem hU)]
    exact hf1 f
  · rw [CommRingCat.comp_apply, jetψ_apply]
    change ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) (jetOf (0 + 1) _)).snd = _
    rw [jetTan_jetOf, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
    exact (hd.2 U h₂ f).symm

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolPair
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem valAt'_eqToHom_lemma {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {U U' : Y.Opens} (h : U = U')
    (f : Γ(Y, U')) : valAt' x U (Y.presheaf.map (eqToHom h).op f) = valAt' x U' f := by
  subst h
  simp

theorem valAt'_fromSpec {Y : Scheme.{0}} {Vo : Y.Opens} (hV : IsAffineOpen Vo) (l : Sp ℂ ⟶ Spec Γ(Y, Vo))
    (a : Γ(Y, Vo)) : valAt' (l ≫ hV.fromSpec) Vo a = valAt' l ⊤ ((Scheme.ΓSpecIso Γ(Y, Vo)).inv a) := by
  rw [← valAt'_comp, IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply]
  exact valAt'_eqToHom_lemma l hV.fromSpec_preimage_self _

private theorem pt_lemma_2 (a b : PrimeSpectrum ℂ) : a = b := by
  have h : ∀ c : PrimeSpectrum ℂ, c.asIdeal = ⊥ := fun c =>
    (Ideal.eq_bot_or_top c.asIdeal).resolve_right c.2.ne_top
  exact PrimeSpectrum.ext (by rw [h a, h b])

private theorem top_le_lemma_3 {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (W : Y.Opens) (q : Sp ℂ)
    (h : x q ∈ W) : ⊤ ≤ x ⁻¹ᵁ W := by
  intro q' _
  have hq : q' = q := pt_lemma_2 q' q
  rw [hq]
  exact h

theorem holPair (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (n : ℕ) (B : Set (Fin n → ℂ))
    (e₁ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₂)) (he : ∀ b, e₁ b ≫ p₁ = e₂ b ≫ p₂) :
    IsOpen B → IsHolTo B e₁ → IsHolTo B e₂ → IsHolTo B (fun b => pullback.lift (e₁ b) (e₂ b) (he b)) := by
  classical
  intro _ h₁ h₂
  apply isHolTo_of_local
  intro U f b₀ hb₀ hU
  let q : Sp ℂ := IsLocalRing.closedPoint ℂ

  obtain ⟨W, hW, hxW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X))
    (show (e₁ b₀ ≫ p₁) q ∈ (⊤ : X.Opens) from trivial)
  have hxW₂ : (e₂ b₀ ≫ p₂) q ∈ W := by rw [← he b₀]; exact hxW
  rw [Scheme.Hom.comp_apply] at hxW hxW₂
  obtain ⟨W₁, hW₁, hx₁, hW₁le⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y₁))
    (show e₁ b₀ q ∈ p₁ ⁻¹ᵁ W from hxW)
  obtain ⟨W₂, hW₂, hx₂, hW₂le⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y₂))
    (show e₂ b₀ q ∈ p₂ ⁻¹ᵁ W from hxW₂)
  have hW' : IsAffineOpen W := hW
  have hW₁' : IsAffineOpen W₁ := hW₁
  have hW₂' : IsAffineOpen W₂ := hW₂
  let N : Set (Fin n → ℂ) := {b ∈ B | ⊤ ≤ e₁ b ⁻¹ᵁ W₁} ∩ {b ∈ B | ⊤ ≤ e₂ b ⁻¹ᵁ W₂}
  have hN : IsOpen N := (h₁ W₁ 0).1.inter (h₂ W₂ 0).1
  have hb₀N : b₀ ∈ N := ⟨⟨hb₀, top_le_lemma_3 _ _ q hx₁⟩, ⟨hb₀, top_le_lemma_3 _ _ q hx₂⟩⟩

  have hr₁ : ∀ b ∈ N, Set.range (e₁ b) ⊆ Set.range hW₁'.fromSpec := by
    intro b hb
    rw [hW₁'.range_fromSpec]
    rintro _ ⟨q', rfl⟩
    exact hb.1.2 (show q' ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hr₂ : ∀ b ∈ N, Set.range (e₂ b) ⊆ Set.range hW₂'.fromSpec := by
    intro b hb
    rw [hW₂'.range_fromSpec]
    rintro _ ⟨q', rfl⟩
    exact hb.2.2 (show q' ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  let l₁ : ∀ b ∈ N, Sp ℂ ⟶ Spec Γ(Y₁, W₁) := fun b hb => IsOpenImmersion.lift hW₁'.fromSpec (e₁ b) (hr₁ b hb)
  let l₂ : ∀ b ∈ N, Sp ℂ ⟶ Spec Γ(Y₂, W₂) := fun b hb => IsOpenImmersion.lift hW₂'.fromSpec (e₂ b) (hr₂ b hb)
  have hl₁ : ∀ b (hb : b ∈ N), l₁ b hb ≫ hW₁'.fromSpec = e₁ b := fun b hb => IsOpenImmersion.lift_fac _ _ _
  have hl₂ : ∀ b (hb : b ∈ N), l₂ b hb ≫ hW₂'.fromSpec = e₂ b := fun b hb => IsOpenImmersion.lift_fac _ _ _
  letI : Algebra Γ(X, W) Γ(Y₁, W₁) := (p₁.appLE W W₁ hW₁le).hom.toAlgebra
  letI : Algebra Γ(X, W) Γ(Y₂, W₂) := (p₂.appLE W W₂ hW₂le).hom.toAlgebra
  have c₁ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₁, W₁))) ≫ hW'.fromSpec = hW₁'.fromSpec ≫ p₁ :=
    IsAffineOpen.SpecMap_appLE_fromSpec p₁ hW' hW₁' hW₁le
  have c₂ : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₂, W₂))) ≫ hW'.fromSpec = hW₂'.fromSpec ≫ p₂ :=
    IsAffineOpen.SpecMap_appLE_fromSpec p₂ hW' hW₂' hW₂le
  have hc : ∀ b (hb : b ∈ N), l₁ b hb ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₁, W₁))) =
      l₂ b hb ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₂, W₂))) := by
    intro b hb
    rw [← cancel_mono hW'.fromSpec, Category.assoc, Category.assoc, c₁, c₂, ← Category.assoc, ← Category.assoc, hl₁ b hb, hl₂ b hb, he]
  let φ := pullback.map _ _ p₁ p₂ hW₁'.fromSpec hW₂'.fromSpec hW'.fromSpec c₁ c₂
  let wN : ∀ b ∈ N, Sp ℂ ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₁, W₁))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) Γ(Y₂, W₂)))) :=
    fun b hb => pullback.lift (l₁ b hb) (l₂ b hb) (hc b hb)
  let w := fun b => if hb : b ∈ N then wN b hb else wN b₀ hb₀N
  have hw : ∀ b (hb : b ∈ N), w b = wN b hb := fun b hb => dif_pos hb
  have hwφ : ∀ b ∈ N, w b ≫ φ = pullback.lift (e₁ b) (e₂ b) (he b) := by
    intro b hb
    rw [hw b hb]
    apply pullback.hom_ext
    · simp only [φ, wN, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
      exact hl₁ b hb
    · simp only [φ, wN, Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc]
      exact hl₂ b hb
  have hwhol : IsHolTo N w := by
    refine isHolTo_pullbackSpec hN w (fun a => ?_) (fun c => ?_)
    · refine ((h₁ W₁ a).2.mono (fun b (hb : b ∈ N) => hb.1)).congr (fun b hb => ?_)
      have h := valAt'_fromSpec hW₁' (l₁ b hb) a
      rw [hl₁ b hb] at h
      rw [hw b hb]
      simp only [wN, pullback.lift_fst]
      exact h.symm
    · refine ((h₂ W₂ c).2.mono (fun b (hb : b ∈ N) => hb.2)).congr (fun b hb => ?_)
      have h := valAt'_fromSpec hW₂' (l₂ b hb) c
      rw [hl₂ b hb] at h
      rw [hw b hb]
      simp only [wN, pullback.lift_snd]
      exact h.symm
  obtain ⟨ho, hdf⟩ := isHolTo_comp hwhol φ U f
  refine ⟨{b ∈ N | ⊤ ≤ (w b ≫ φ) ⁻¹ᵁ U}, ho.mem_nhds ⟨hb₀N, by show ⊤ ≤ (w b₀ ≫ φ) ⁻¹ᵁ U; rw [hwφ b₀ hb₀N]; exact hU⟩,
    fun b hb => ⟨hb.1.1.1, by rw [← hwφ b hb.1]; exact hb.2⟩, hdf.congr fun b hb => ?_⟩
  simp only [hwφ b hb.1]

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

