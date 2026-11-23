module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainHomotopyFiniteProjector
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open AlgebraicTopology AlgebraicTopology.DoldKan Simplicial

namespace GlobalTheory.CompanionTheory.NerveNorm

section Cos

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def cosMap {x y : SimplexCategory} (θ : x ⟶ y) : Cn F x.len →ₗ[R] Cn F y.len where
  toFun f c := mp F (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last x.len)))))
    (f (θ.toOrderHom.monotone.functor ⋙ c))
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ map_smul _ _ _

theorem cosMap_apply {x y : SimplexCategory} (θ : x ⟶ y) (f : Cn F x.len) (c : Fin (y.len + 1) ⥤ C) :
    cosMap F θ f c = mp F (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last x.len)))))
      (f (θ.toOrderHom.monotone.functor ⋙ c)) := rfl

def cosK : SimplexCategory ⥤ ModuleCat.{0} R where
  obj x := ModuleCat.of R (Cn F x.len)
  map θ := ModuleCat.ofHom (cosMap F θ)
  map_id x := by
    ext f c
    have h : c.map (homOfLE (Fin.le_last ((𝟙 x : x ⟶ x).toOrderHom (Fin.last x.len)))) = 𝟙 _ :=
      (congrArg c.map (Subsingleton.elim _ _)).trans (c.map_id _)
    exact (congrArg (fun φ ↦ mp F φ (f c)) h).trans (mp_id F _ _)
  map_comp {x y z} θ ψ := by
    ext f c
    have h : c.map (homOfLE (Fin.le_last ((θ ≫ ψ).toOrderHom (Fin.last x.len)))) =
        c.map (homOfLE (ψ.toOrderHom.monotone (Fin.le_last (θ.toOrderHom (Fin.last x.len))))) ≫
          c.map (homOfLE (Fin.le_last (ψ.toOrderHom (Fin.last y.len)))) :=
      (congrArg c.map (Subsingleton.elim _ _)).trans (c.map_comp _ _)
    exact (congrArg (fun φ ↦ mp F φ (f ((θ ≫ ψ).toOrderHom.monotone.functor ⋙ c))) h).trans
      (mp_comp F _ _ _)

theorem cosK_map_δ (n : ℕ) (i : Fin (n + 2)) :
    ((cosK F).map (SimplexCategory.δ i)).hom = cof F n i := rfl

end Cos

section Norm

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev simpX : SimplicialObject (ModuleCat.{0} R)ᵒᵖ := (cosK F).op

def eN (n : ℕ) : Cn F n →ₗ[R] Cn F n := ((PInfty (X := simpX F)).f n).unop.hom

def hN (n : ℕ) : Cn F (n + 1) →ₗ[R] Cn F n := ((homotopyPInftyToId (simpX F)).hom n (n + 1)).unop.hom

theorem d_unop (n : ℕ) :
    ((AlternatingFaceMapComplex.obj (simpX F)).d (n + 1) n).unop.hom = dn F n := by
  rw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [unop_sum, unop_zsmul, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  unfold dn
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul R]
  push_cast
  rw [← cosK_map_δ F n i]
  rfl

theorem eN_idem (n : ℕ) : eN F n ∘ₗ eN F n = eN F n := by
  exact congrArg (fun f => f.unop.hom) (PInfty_f_idem (X := simpX F) n)

theorem eN_comm (n : ℕ) : eN F (n + 1) ∘ₗ dn F n = dn F n ∘ₗ eN F n := by
  have h := congrArg (fun f => f.unop.hom) ((PInfty (X := simpX F)).comm (n + 1) n)
  rw [← d_unop]
  exact h

theorem eN_zero : eN F 0 = LinearMap.id + hN F 0 ∘ₗ dn F 0 := by
  have h := (homotopyPInftyToId (simpX F)).comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
  have key : eN F 0 = hN F 0 ∘ₗ dn F 0 + LinearMap.id := by
    rw [← d_unop]
    exact congrArg (fun f => f.unop.hom) h
  exact key.trans (add_comm _ _)

theorem eN_succ (n : ℕ) :
    eN F (n + 1) = LinearMap.id + dn F n ∘ₗ hN F n + hN F (n + 1) ∘ₗ dn F (n + 1) := by
  have h := (homotopyPInftyToId (simpX F)).comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have key : eN F (n + 1) = dn F n ∘ₗ hN F n + hN F (n + 1) ∘ₗ dn F (n + 1) + LinearMap.id := by
    rw [← d_unop, ← d_unop]
    exact congrArg (fun f => f.unop.hom) h
  rw [key]
  abel

theorem cosMap_σ_eN (n : ℕ) (i : Fin (n + 1)) :
    cosMap F (SimplexCategory.σ i) ∘ₗ eN F (n + 1) = 0 := by
  unfold eN
  change ((simpX F).σ i ≫ (PInfty (X := simpX F)).f (n + 1)).unop.hom = 0
  rw [σ_comp_PInfty]
  rfl

end Norm

section Vanish

variable {R : Type} [CommRing R] {P : Type} [PartialOrder P]

theorem exists_stutter [Finite P] (n : ℕ) (hn : Nat.card P < n + 1) (c : Fin (n + 2) ⥤ Pᵒᵖ) :
    ∃ i : Fin (n + 1), c.obj i.castSucc = c.obj i.succ := by
  by_contra hne
  simp only [not_exists] at hne
  have hanti : StrictAnti fun k : Fin (n + 2) => (c.obj k).unop := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have hle : (c.obj i.succ).unop ≤ (c.obj i.castSucc).unop :=
      leOfHom (c.map (homOfLE (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le)).unop
    exact lt_of_le_of_ne hle fun heq => hne i (Opposite.unop_injective heq).symm
  haveI := Fintype.ofFinite P
  have hcard := Fintype.card_le_of_injective _ hanti.injective
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at hcard
  omega

theorem zero_of_degenerate (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) {m : ℕ} (g : Cn F m) {c₁ c₂ : Fin (m + 1) ⥤ Pᵒᵖ}
    (h : c₁ = c₂) {T : Pᵒᵖ} (φ : c₁.obj (Fin.last m) ⟶ T) (hT : c₂.obj (Fin.last m) = T)
    (h0 : mp F φ (g c₁) = 0) : g c₂ = 0 := by
  subst h
  subst hT
  have hφ : φ = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hφ, mp_id] at h0
  exact h0

theorem eN_vanish [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (n : ℕ) (hn : Nat.card P < n + 1) :
    eN F (n + 1) = 0 := by
  refine LinearMap.ext fun f => funext fun c => ?_
  show eN F (n + 1) f c = 0
  obtain ⟨i, hi⟩ := exists_stutter n hn c
  have h0 := congrFun (LinearMap.congr_fun (cosMap_σ_eN F n i) f)
    ((SimplexCategory.δ i.castSucc).toOrderHom.monotone.functor ⋙ c)
  rw [LinearMap.comp_apply, cosMap_apply, LinearMap.zero_apply, Pi.zero_apply] at h0
  have hlast : (SimplexCategory.δ i.castSucc).toOrderHom (Fin.last n) = Fin.last (n + 1) := by
    show i.castSucc.succAbove (Fin.last n) = Fin.last (n + 1)
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))]
    exact Fin.succ_last n
  have hfun : (SimplexCategory.σ i).toOrderHom.monotone.functor ⋙
      ((SimplexCategory.δ i.castSucc).toOrderHom.monotone.functor ⋙ c) = c := by
    fapply CategoryTheory.Functor.ext
    · intro k
      show c.obj (i.castSucc.succAbove (i.predAbove k)) = c.obj k
      by_cases hk : k = i.castSucc
      · subst hk
        rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
        exact hi.symm
      · rw [Fin.succAbove_predAbove hk]
    · intro _ _ _
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  exact zero_of_degenerate F (eN F (n + 1) f) hfun _ (congrArg c.obj hlast.symm) h0

end Vanish

theorem exists_normalisation {R : Type} [CommRing R] (P : Type) [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) :
    ∃ (e : ∀ n, Cn F n →ₗ[R] Cn F n) (h : ∀ n, Cn F (n + 1) →ₗ[R] Cn F n) (B : ℕ),
      (∀ n, e n ∘ₗ e n = e n) ∧ (∀ n, e (n + 1) ∘ₗ dn F n = dn F n ∘ₗ e n) ∧
      e 0 = LinearMap.id + h 0 ∘ₗ dn F 0 ∧
      (∀ n, e (n + 1) = LinearMap.id + dn F n ∘ₗ h n + h (n + 1) ∘ₗ dn F (n + 1)) ∧
      ∀ n, B < n → e n = 0 := by
  refine ⟨eN F, hN F, Nat.card P, eN_idem F, eN_comm F, eN_zero F, eN_succ F, fun n hn => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_lt_zero _)
  | succ m => exact eN_vanish F m hn

end GlobalTheory.CompanionTheory.NerveNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartExtendBaseChange
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

theorem baseChange_loc {B A P P' Q Q' : Type} [CommRing B] [CommRing A] [CommRing P] [CommRing P'] [CommRing Q]
    [CommRing Q'] [Algebra B A] [Algebra B P] [Algebra B P'] [Algebra B Q] [Algebra B Q'] [Algebra A Q] [Algebra A Q']
    [IsScalarTower B A Q] [IsScalarTower B A Q']
    (i : P →+* P') (r : Q →+* Q') (t₁ : P →+* Q) (t : P' →+* Q') (c : P)
    (hi : ∀ b, i (algebraMap B P b) = algebraMap B P' b)
    (hr : ∀ a, r (algebraMap A Q a) = algebraMap A Q' a)
    (ht₁ : ∀ b, t₁ (algebraMap B P b) = algebraMap B Q b)
    (ht : ∀ b, t (algebraMap B P' b) = algebraMap B Q' b)
    (hcomm : ∀ x, t (i x) = r (t₁ x))
    (hP : letI := i.toAlgebra; IsLocalization.Away c P')
    (hQ : letI := r.toAlgebra; IsLocalization.Away (t₁ c) Q')
    (f₁ : P →ₗ[B] Q) (hf₁ : ∀ x, f₁ x = t₁ x) (f : P' →ₗ[B] Q') (hf : ∀ x, f x = t x)
    (h : IsBaseChange A f₁) : IsBaseChange A f := by
  letI a1 : Algebra P P' := i.toAlgebra
  letI a2 : Algebra Q Q' := r.toAlgebra
  letI a3 : Algebra P Q := t₁.toAlgebra
  letI a4 : Algebra P' Q' := t.toAlgebra
  letI a5 : Algebra P Q' := (t.comp i).toAlgebra
  haveI : IsScalarTower B P P' := .of_algebraMap_eq fun b => (hi b).symm
  haveI : IsScalarTower B P Q := .of_algebraMap_eq fun b => (ht₁ b).symm
  haveI : IsScalarTower B P' Q' := .of_algebraMap_eq fun b => (ht b).symm
  haveI : IsScalarTower B P Q' := .of_algebraMap_eq fun b => by
    change _ = t (i _)
    rw [hi, ht]
  haveI : IsScalarTower P P' Q' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower P Q Q' := .of_algebraMap_eq fun x => hcomm x
  haveI : IsScalarTower A Q Q' := .of_algebraMap_eq fun a => (hr a).symm
  haveI : IsScalarTower B Q Q' := .of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B A Q, IsScalarTower.algebraMap_apply B A Q']
    exact (hr _).symm
  have e1 : f₁ = (IsScalarTower.toAlgHom B P Q).toLinearMap := LinearMap.ext hf₁
  have p1 : Algebra.IsPushout B A P Q := ⟨by rw [← e1]; exact h⟩
  haveI p2 : Algebra.IsPushout B P A Q := p1.symm
  haveI : IsLocalization.Away c P' := hP
  have hQ' : IsLocalization (Algebra.algebraMapSubmonoid Q (Submonoid.powers c)) Q' := by
    have e : Algebra.algebraMapSubmonoid Q (Submonoid.powers c) = Submonoid.powers (t₁ c) := by
      simp only [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      rfl
    rw [e]
    exact hQ
  have p3 : Algebra.IsPushout P Q P' Q' := (Algebra.isLocalization_iff_isPushout (Submonoid.powers c) P').1 hQ'
  have p4 : Algebra.IsPushout P P' Q Q' := p3.symm
  have p5 : Algebra.IsPushout B P' A Q' := (Algebra.IsPushout.comp_iff B P A Q).2 p4
  have e2 : f = (IsScalarTower.toAlgHom B P' Q').toLinearMap := LinearMap.ext hf
  rw [e2]
  exact p5.symm.out

variable {K : Type} [Field K] {n d : ℕ}

theorem mon_congr {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (e : g = g') (hg : g ∈ M) (hg' : g' ∈ M) :
    mon K g hg = mon K g' hg' := by
  subst e
  rfl

theorem mon_sum {ι : Type} {M : AddSubmonoid (Gam n d)} (s : Finset ι) (g : ι → Gam n d) (hg : ∀ j, g j ∈ M) :
    mon K (∑ j ∈ s, g j) (sum_mem fun j _ => hg j) = ∏ j ∈ s, mon K (g j) (hg j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact mon_congr (K := K) Finset.sum_empty _ M.zero_mem
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, mon_mul]
    exact mon_congr (Finset.sum_insert ha) _ _

def cE (S : Finset (Fin d)) (k : Fin d) : Gam n d := ∑ j ∈ S, ratE k j

theorem cE_mem (S : Finset (Fin d)) (k : Fin d) : cE S k ∈ (cone {k} : AddSubmonoid (Gam n d)) :=
  sum_mem fun j _ => ratE_mem (Finset.mem_singleton_self k) j

theorem neg_cE_mem {S : Finset (Fin d)} (k : Fin d) : -cE S k ∈ (cone S : AddSubmonoid (Gam n d)) := by
  have e : -cE S k = ∑ j ∈ S, (ratE j k : Gam n d) := by
    simp [cE, ratE, ← Finset.sum_neg_distrib]
  rw [e]
  exact sum_mem fun j hj => ratE_mem hj k

theorem one_le_cE {S : Finset (Fin d)} {k j : Fin d} (hj : j ∈ S) (hne : j ≠ k) :
    1 ≤ (cE S k : Gam n d) (Sum.inr j) := by
  have : (cE S k : Gam n d) (Sum.inr j) = 1 := by
    simp [cE, ratE, oneE, Finset.sum_apply, Pi.single_apply, hj, hne]
  exact this.ge

theorem exists_add_nsmul_mem {S : Finset (Fin d)} (k : Fin d) (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) :
    ∃ N : ℕ, g + N • cE S k ∈ (cone {k} : AddSubmonoid (Gam n d)) := by
  have hc := cE_mem (n := n) S k
  have hN := (cone {k} : AddSubmonoid (Gam n d)).nsmul_mem hc
  refine ⟨∑ j, (g (Sum.inr j)).natAbs, fun l => ?_, fun j hj => ?_, ?_⟩
  · exact add_nonneg (hg.1 l) ((hN _).1 l)
  · have hne : j ≠ k := fun h => hj (h ▸ Finset.mem_singleton_self k)
    by_cases hjS : j ∈ S
    · have h1 := one_le_cE (n := n) hjS hne
      have h2 : (g (Sum.inr j)).natAbs ≤ ∑ j, (g (Sum.inr j)).natAbs :=
        Finset.single_le_sum (f := fun j => (g (Sum.inr j)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      show 0 ≤ g (Sum.inr j) + (∑ j, (g (Sum.inr j)).natAbs) • (cE S k : Gam n d) (Sum.inr j)
      rw [nsmul_eq_mul]
      have h3 : -g (Sum.inr j) ≤ ((g (Sum.inr j)).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact neg_le_abs _
      have h4 : ((g (Sum.inr j)).natAbs : ℤ) ≤ ((∑ j, (g (Sum.inr j)).natAbs : ℕ) : ℤ) := by exact_mod_cast h2
      have h5 : (0 : ℤ) ≤ ((∑ j, (g (Sum.inr j)).natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
      nlinarith
    · exact add_nonneg (hg.2.1 j hjS) ((hN _).2.1 j hj)
  · rw [tdeg_add]
    exact add_nonneg hg.2.2 (hN _).2.2

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

theorem theta_loc : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) (θ₁ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ₁ : ∀ b, θ₁ (poly n K {k} b) = toR C {k} (phi C b)), (∀ j, θ₁ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) → IsBaseChange (Aa C) (thetaLin C θ₁ hθ₁) → ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  intro K _ n d A _ _ C S k hk θ₁ hθ₁ hu hbc
  have hsk : ({k} : Finset (Fin d)) ⊆ S := Finset.singleton_subset_iff.2 hk
  have hle : (cone {k} : AddSubmonoid (Gam n d)) ≤ cone S := cone_mono hsk
  have hc := cE_mem (n := n) S k
  have hP := Away.isLocalization_away (K := K) hle (cE S k) hc (neg_cE_mem k)
    (fun g hg => exists_add_nsmul_mem k g hg)
  have hθc : θ₁ (mon K (cE S k) hc) = ∏ j ∈ S, C.u {k} k (Finset.mem_singleton_self k) j := by
    have e : mon K (cE S k) hc = ∏ j ∈ S, mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j) :=
      mon_sum S _ _
    rw [e, map_prod]
    exact Finset.prod_congr rfl fun j _ => hu j
  letI aP : Algebra (R0 K n d {k}) (R0 K n d S) := (incl (K := K) hle).toRingHom.toAlgebra
  letI aQ : Algebra (C.R {k}) (C.R S) := (C.res hsk).toRingHom.toAlgebra
  haveI hP' : IsLocalization.Away (mon K (cE S k) hc) (R0 K n d S) := hP
  have hQ : IsLocalization.Away (θ₁ (mon K (cE S k) hc)) (C.R S) := by
    rw [hθc]
    exact C.loc S k hk
  have hunit : IsUnit (((C.res hsk).toRingHom.comp θ₁.toRingHom) (mon K (cE S k) hc)) :=
    IsLocalization.Away.algebraMap_isUnit (S := C.R S) (θ₁ (mon K (cE S k) hc))
  let T : R0 K n d S →+* C.R S := IsLocalization.Away.lift (mon K (cE S k) hc) hunit
  have hT : ∀ x, T (incl hle x) = C.res hsk (θ₁ x) := fun x =>
    IsLocalization.Away.lift_eq (mon K (cE S k) hc) hunit x
  let θ : R0 K n d S →ₐ[K] C.R S :=
    { T with
      commutes' := fun r => by
        have e : algebraMap K (R0 K n d S) r = incl hle (algebraMap K (R0 K n d {k}) r) :=
          ((incl (K := K) hle).commutes r).symm
        change T _ = _
        rw [e, hT, θ₁.commutes, (C.res hsk).commutes] }
  have hθT : ∀ x, θ x = T x := fun _ => rfl
  have hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b) := fun b => by
    rw [hθT, ← incl_poly hsk, hT, hθ₁, res_toR]
  refine ⟨θ, hθ, ?_⟩
  exact baseChange_loc (A := Aa C) (Q := Rb C {k}) (Q' := Rb C S)
    (incl (K := K) hle).toRingHom (C.res hsk).toRingHom θ₁.toRingHom T (mon K (cE S k) hc)
    (fun b => incl_poly hsk b) (fun a => res_toR C hsk a) hθ₁ hθ hT hP hQ
    (thetaLin C θ₁ hθ₁) (fun _ => rfl) (thetaLin C θ hθ) (fun _ => rfl) hbc

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedStOfTwoFormCohSt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeClosed

section Algebra

variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem pairing_map (v : Fin 2 → Module.Dual R N) (g : M →ₗ[R] N) (t : ⋀[R]^2 M) :
    exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 v) (exteriorPower.map 2 g t) =
      exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 fun i ↦ v i ∘ₗ g) t := by
  have e : exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 v) ∘ₗ exteriorPower.map 2 g =
      exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 fun i ↦ v i ∘ₗ g) := by
    apply exteriorPower.linearMap_ext
    ext x
    simp [exteriorPower.pairingDual_ιMulti_ιMulti]
  exact LinearMap.congr_fun e t

theorem eq_zero_of_pairing [Module.Finite R M] [Module.Projective R M] (t : ⋀[R]^2 M)
    (h : ∀ v : Fin 2 → Module.Dual R M, exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 v) t = 0) :
    t = 0 := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hu : exteriorPower.map 2 g t = 0 := by
    let b := Pi.basisFun R (Fin n)
    refine (b.exteriorPower 2).repr.injective (Finsupp.ext fun s ↦ ?_)
    rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual, exteriorPower.ιMulti_family]
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact (pairing_map _ g t).trans (h _)
  exact exteriorPower.map_injective f hfg (hu.trans (map_zero _).symm)

theorem eq_zero_of_additive [Module.Finite R M] [Module.Projective R M] (A B : M →ₗ[R] N)
    (hb : Function.Bijective fun x : M × M ↦ A x.1 + B x.2) (t : ⋀[R]^2 M)
    (h : exteriorPower.map 2 (A + B) t = exteriorPower.map 2 A t + exteriorPower.map 2 B t) : t = 0 := by
  let e : (M × M) ≃ₗ[R] N := LinearEquiv.ofBijective (A.coprod B) ((funext fun x ↦ LinearMap.coprod_apply A B x : ⇑(A.coprod B) = _) ▸ hb)
  have eA : ∀ x, e.symm (A x) = (x, 0) := fun x ↦ e.symm_apply_eq.2 (by simp [e])
  have eB : ∀ x, e.symm (B x) = (0, x) := fun x ↦ e.symm_apply_eq.2 (by simp [e])
  refine eq_zero_of_pairing t fun v ↦ ?_
  let L : Module.Dual R N := v 0 ∘ₗ LinearMap.fst R M M ∘ₗ e.symm.toLinearMap
  let L' : Module.Dual R N := v 1 ∘ₗ LinearMap.snd R M M ∘ₗ e.symm.toLinearMap
  have key := congrArg (exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 ![L, L'])) h
  rw [map_add (f := _), pairing_map, pairing_map, pairing_map] at key
  have h0 : (fun i ↦ ![L, L'] i ∘ₗ (A + B)) = v := by
    funext i
    fin_cases i
    · ext x; simp [L, eA, eB]
    · ext x; simp [L', eA, eB]
  have hA : (fun i ↦ ![L, L'] i ∘ₗ A) 1 = 0 := by ext x; simp [L', eA]
  have hB : (fun i ↦ ![L, L'] i ∘ₗ B) 0 = 0 := by ext x; simp [L, eB]
  rw [h0, (exteriorPower.ιMulti R 2).map_coord_zero (m := fun i ↦ ![L, L'] i ∘ₗ A) 1 hA,
    (exteriorPower.ιMulti R 2).map_coord_zero (m := fun i ↦ ![L, L'] i ∘ₗ B) 0 hB] at key
  simpa using key

end Algebra

section Forms

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem nu_natural (c : CoefMap (RingHom.id R) F G) (ν : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (ν' : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hν : ∀ a b T, ν (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hν' : ∀ a b T, ν' (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (t : ⋀[R]^2 (Glob1 F)) (T : D) :
    qOm c 2 T (ν t (c.G.obj T)) = ν' (exteriorPower.map 2 (pullGlob1 c) t) T := by
  have e : (qOm c 2 T : _ →ₗ[R] _) ∘ₗ LinearMap.proj (c.G.obj T) ∘ₗ ν =
      LinearMap.proj T ∘ₗ ν' ∘ₗ exteriorPower.map 2 (pullGlob1 c) := by
    apply exteriorPower.linearMap_ext
    ext x
    obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] := ⟨x 0, x 1, by funext i; fin_cases i <;> rfl⟩
    have hy : (pullGlob1 c : Glob1 F →ₗ[R] Glob1 G) ∘ ![a, b] = ![pullGlob1 c a, pullGlob1 c b] := by
      funext i; fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      exteriorPower.map_apply_ιMulti]
    rw [hy, hν, hν']
    exact congrArg Subtype.val (qOm_wedge c (a.1 (c.G.obj T)) (b.1 (c.G.obj T)))
  exact LinearMap.congr_fun e t

end Forms

theorem closedSt_of_twoFormCohSt : TwoFormCohSt → ClosedSt := by
  intro h2 R _ C _ F hF hBi
  obtain ⟨D, _, G, m, p, q, hS, hP, -, hb, -, hm, -⟩ := hBi
  have hG : Framed G := by
    obtain ⟨-, -, h1, h3⟩ := hF
    let e : (Glob1 F × Glob1 F) ≃ₗ[R] Glob1 G := LinearEquiv.ofBijective ((pullGlob1 p).coprod (pullGlob1 q))
      ((funext fun x ↦ LinearMap.coprod_apply (pullGlob1 p) (pullGlob1 q) x :
        ⇑((pullGlob1 p).coprod (pullGlob1 q)) = _) ▸ hb)
    exact ⟨hS, hP, Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  obtain ⟨ν, hν, -, hsurj⟩ := h2 R C F hF
  obtain ⟨ν', hν', hinj, -⟩ := h2 R D G hG
  obtain ⟨-, -, hfin, hproj⟩ := hF
  refine eq_top_iff.2 fun ω₀ _ T ↦ ?_
  obtain ⟨t, ht⟩ := hsurj (fun T ↦ dOne R _ (ω₀.1 T)) fun T T' φ ↦ by
    rw [pOm_dOne, ω₀.2 φ]
  have step : ∀ (c : CoefMap (RingHom.id R) F G),
      ν' (exteriorPower.map 2 (pullGlob1 c) t) = fun T ↦ dOne R _ ((pullGlob1 c ω₀).1 T) := by
    intro c
    funext T
    rw [← nu_natural c ν ν' hν hν' t T, ht]
    exact qOm_dOne c (ω₀.1 (c.G.obj T))
  have hadd : exteriorPower.map 2 (pullGlob1 p + pullGlob1 q) t =
      exteriorPower.map 2 (pullGlob1 p) t + exteriorPower.map 2 (pullGlob1 q) t := by
    have h1 : pullGlob1 p + pullGlob1 q = pullGlob1 m := LinearMap.ext fun ω ↦ (hm ω).symm
    apply hinj
    rw [h1, step m, map_add (f := _), step p, step q]
    funext T'
    change dOne R _ ((pullGlob1 m ω₀).1 T') = dOne R _ ((pullGlob1 p ω₀).1 T') + dOne R _ ((pullGlob1 q ω₀).1 T')
    rw [hm, ← map_add (f := _)]
    rfl
  have ht0 : t = 0 := eq_zero_of_additive _ _ hb t hadd
  have := congrFun ht T
  rw [ht0, map_zero] at this
  exact this.symm

end GlobalTheory.CompanionTheory.HodgeClosed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMem
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem homIdeal_homog {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) :
    ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  intro f hf n
  have hI : (homIdeal i).IsHomogeneous (grK K N) := by
    refine Ideal.homogeneous_span (grK K N) _ ?_
    rintro g ⟨d, hg, -⟩
    exact ⟨d • 1, hg⟩
  have h := hI n hf
  have e : ((DirectSum.decompose (grK K N) f n : grK K N n) : MvPolynomial (Fin (N + 1)) K) =
      MvPolynomial.homogeneousComponent n f :=
    MvPolynomial.decomposition.decompose'_apply f n
  exact e ▸ h

end GlobalTheory.CompanionTheory.Geo
end

