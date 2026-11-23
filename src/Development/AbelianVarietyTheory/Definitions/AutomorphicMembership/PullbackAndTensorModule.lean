module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaCubIsPullCubical
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0046
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensor
open scoped CategoryTheory.Obj

namespace GlobalTheory.LocM

structure Unim (E : Type) [Field E] [NumberField E] [IsCMField E] : Type where

  n : ℕ

  form : HermForm E (Fin n → E)
  pos : ∀ (σ : E →+* ℂ) (x : Fin n → E), x ≠ 0 → 0 < (σ (form x x)).re

  L : Submodule (𝓞 E) (Fin n → E)
  isLattice : Submodule.IsFullLattice E L
  unimod : Formalism.HermitianLatticesTheory.IsUnimodular form.toSesq.flip L

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Unim

variable (Λ : Unim E)

def gramE : Matrix (Fin Λ.n) (Fin Λ.n) E := fun i j => Λ.form (Pi.single i 1) (Pi.single j 1)

theorem mem_iff (x : Fin Λ.n → E) : x ∈ Λ.L ↔ ∀ y ∈ Λ.L, ∃ c : 𝓞 E, (c : E) = Λ.form x y := by
  conv_lhs => rw [← Λ.unimod]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Submodule.mem_one]
  rfl

instance : Module.Finite (𝓞 E) Λ.L := Module.Finite.iff_fg.2 Λ.isLattice.fg

instance : Module.Projective (𝓞 E) Λ.L :=
  have : Module.FinitePresentation (𝓞 E) Λ.L := Module.finitePresentation_of_finite _ _
  Module.Flat.projective_of_finitePresentation

theorem finrank_L : Module.finrank (𝓞 E) Λ.L = Λ.n := by
  have := Λ.isLattice
  exact (Submodule.IsFullLattice.finrank_eq E Λ.L).trans (Module.finrank_fin_fun E)

theorem isIntegral_form (x y : Λ.L) : IsIntegral ℤ (Λ.form x y) := by
  obtain ⟨c, hc⟩ := (Λ.mem_iff x).1 x.2 y y.2
  exact hc ▸ c.isIntegral_coe

def hInt : HermForm (𝓞 E) Λ.L :=
  HermForm.ofFun (fun x y => ⟨Λ.form x y, Λ.isIntegral_form x y⟩)
    (fun x y z => RingOfIntegers.ext (Λ.form.add_left x y z))
    (fun c x y => RingOfIntegers.ext (Λ.form.smul_left (c : E) x y))
    (fun x y => RingOfIntegers.ext (Λ.form.star_apply x y))

def pres : Summand (𝓞 E) Λ.L := Summand.choose _ _

section Group

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (a : OAct (𝓞 E) G)

abbrev obj : Over X := Λ.pres.obj a

abbrev act : OAct (𝓞 E) (Λ.obj a) := Λ.pres.act a

abbrev isTensor : IsTensor (Λ.obj a) (Λ.act a) G a Λ.L := Λ.pres.isTensor a

end Group


variable (E) in
def stdForm (n : ℕ) : HermForm E (Fin n → E) :=
  HermForm.ofFun (fun x y => ∑ i, x i * star (y i)) (fun x y z => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, _root_.mul_assoc]) (fun x y => by simp [mul_comm])

theorem stdForm_apply {n : ℕ} (x y : Fin n → E) : stdForm E n x y = ∑ i, x i * star (y i) := rfl

theorem stdForm_pos {n : ℕ} (σ : E →+* ℂ) (x : Fin n → E) (hx : x ≠ 0) : 0 < (σ (stdForm E n x x)).re := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
  have e : ∀ j, (σ (x j * star (x j))).re = Complex.normSq (σ (x j)) := fun j => by
    rw [map_mul, complexEmbedding_star]
    exact congrArg Complex.re (Complex.mul_conj _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [stdForm_apply, map_sum, Complex.re_sum]
  simp only [e]
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 ((map_ne_zero σ).2 hi)⟩

def ofGenLat {n : ℕ} (Γ : Formalism.L2.Pj.GenLat E n) (hL : Submodule.IsFullLattice E Γ.La) (hU : Γ.Unimod) : Unim E where
  n := n
  form := stdForm E n
  pos := stdForm_pos
  L := Γ.La
  isLattice := hL
  unimod := by
    ext x
    rw [hU x]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.mem_one]
    refine forall₂_congr fun y _ => ?_
    have e : ∑ j, IsCMField.complexConj E (x j) * y j = star (stdForm E n x y) := by
      rw [HermForm.star_apply, stdForm_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]
    exact ⟨fun ⟨c, hc⟩ => ⟨star c, congrArg star hc⟩, fun ⟨c, hc⟩ => ⟨star c, (congrArg star hc).trans (star_star _)⟩⟩


omit [NumberField E] [IsCMField E] in
theorem mem_stdLat {n : ℕ} (x : Fin n → E) : x ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = x i := by
  simp [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Submodule.mem_one]


omit [NumberField E] [IsCMField E] in
theorem single_mem_stdLat {n : ℕ} (i : Fin n) : (Pi.single i 1 : Fin n → E) ∈ Formalism.L2.Pj.stdLat E n :=
  (mem_stdLat _).2 fun j => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
    by_cases h : j = i <;> simp [h]⟩


variable (E) in
def stdEquiv (n : ℕ) : Formalism.L2.Pj.stdLat E n ≃ₗ[𝓞 E] (Fin n → 𝓞 E) where
  toFun x i := ⟨x.1 i, by obtain ⟨c, hc⟩ := (mem_stdLat _).1 x.2 i; exact hc ▸ c.isIntegral_coe⟩
  invFun v := ⟨fun i => algebraMap (𝓞 E) E (v i), (mem_stdLat _).2 fun i => ⟨v i, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl


omit [NumberField E] [IsCMField E] in
theorem isLattice_stdLat (n : ℕ) : Submodule.IsFullLattice E (Formalism.L2.Pj.stdLat E n) := by
  have hspan : Submodule.span E (Formalism.L2.Pj.stdLat E n : Set (Fin n → E)) = ⊤ :=
    eq_top_iff.2 fun x _ => by
      rw [pi_eq_sum_univ' x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_stdLat i))
  refine { toIsLattice := ?_, span_eq_top := hspan }
  refine (Submodule.IsLattice.iff_fg_and_finrank_span_eq_finrank E _).2 ⟨?_, ?_⟩
  · exact Module.Finite.iff_fg.1 (Module.Finite.equiv (stdEquiv E n).symm)
  · rw [hspan, finrank_top, (stdEquiv E n).finrank_eq, Module.finrank_fin_fun, Module.finrank_fin_fun]

theorem unimod_stdLat (n : ℕ) : (⟨Formalism.L2.Pj.stdLat E n⟩ : Formalism.L2.Pj.GenLat E n).Unimod := fun v => by
  refine ⟨fun hv w hw => ?_, fun h => (mem_stdLat _).2 fun i => ?_⟩
  · choose c hc using (mem_stdLat _).1 hv
    choose d hd using (mem_stdLat _).1 hw
    refine ⟨∑ j, star (c j) * d j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, ← hc, ← hd]; rfl
  · obtain ⟨c, hc⟩ := h _ (single_mem_stdLat i)
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, _root_.mul_one] at hc
    exact ⟨star c, (congrArg star hc).trans (star_star (v i))⟩


variable (E) in
def std (n : ℕ) : Unim E := ofGenLat ⟨Formalism.L2.Pj.stdLat E n⟩ (isLattice_stdLat n) (unimod_stdLat n)

theorem gramE_std (n : ℕ) : (std E n).gramE = (1 : Matrix (Fin n) (Fin n) E) := by
  have : ∀ i j : Fin n, ∑ k : Fin n, (Pi.single i 1 : Fin n → E) k * star ((Pi.single j 1 : Fin n → E) k) =
      (1 : Matrix (Fin n) (Fin n) E) i j := fun i j => by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  exact Matrix.ext this

end Unim

variable {H : Host E} {X X' : Scheme.{0}}

theorem bar_eq_star (H : Host E) (c : 𝓞 E) : H.bar c = star c := RingOfIntegers.ext (H.bar_eq c)

theorem halfUnit_add_star (H : Host E) : H.w0 + star H.w0 = 1 := by
  rw [← bar_eq_star H]; exact PullbackSections.CVA.cmHostUnit_add_conj_eq_one H

theorem isAdj_sab (t : SAB H X) : IsAdj t.act t.PP.L := fun c => bar_eq_star H c ▸ t.adj c

def sabOfTensor (t : SAB H X) {M : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [Module.Projective (𝓞 E) M] {A : Over X} [GrpObj A] [IsCommMonObj A] {b : OAct (𝓞 E) A}
    (T : IsTensor A b t.G t.act M) (P : Summand (𝓞 E) M) (h : HermForm (𝓞 E) M) : SAB H X where
  G := A
  semi := isSemiAbelian_tensor T t.semi
  act := b
  PP := theta T P h H.w0 t.PP
  cub := thetaCub T P h H.w0 t.cub
  sym := theta_isSymmetric T P h H.w0 t.cub t.sym
  adj c := bar_eq_star H c ▸ theta_isAdj T P h t.cub (isAdj_sab t) (halfUnit_add_star H) c
  prim := theta_prim T P h t.cub (isAdj_sab t) (halfUnit_add_star H)

def tens (t : SAB H X) (Λ : Unim E) : SAB H X := sabOfTensor t (Λ.pres.isTensor t.act) Λ.pres Λ.hInt

namespace tens

variable (t : SAB H X) (Λ : Unim E)

def isTensor : IsTensor (tens t Λ).G (tens t Λ).act t.G t.act Λ.L := Λ.pres.isTensor t.act

def poi : RigLB ((tens t Λ).G ⊗ (tens t Λ).G) := HermTensor.poi (isTensor t Λ) Λ.pres Λ.hInt t.PP

theorem pp_iso_pull :
    LBIso (tens t Λ).PP.L ((poi t Λ).L.pull (lift (𝟙 (tens t Λ).G) ((tens t Λ).act.act H.w0)).left) :=
  theta_iso_pull (isTensor t Λ) Λ.pres Λ.hInt H.w0 t.PP

variable {t} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)

theorem isLinearPullback_sabMap : IsLinearPullback t'.act t.act f m.φ := ⟨m.cart, m.act⟩

def map : SABMap (tens t' Λ) (tens t Λ) f :=
  have H := ((isTensor t Λ).exists_isLinearPullback (isTensor t' Λ) (isLinearPullback_sabMap m)).choose_spec
  { cm := cubeMapOf H.1.1
    cart := H.1.1
    base := rfl
    act := H.1.2
    lin := thetaCub_isPullCubical (isTensor t Λ) Λ.pres Λ.hInt (isTensor t' Λ) (isLinearPullback_sabMap m) H.1 H.2 _
      m.cm rfl m.base m.lin }

end tens

section Record

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

def uniTrue (ct : At S κ p) : UniSt ct where
  Unim := Unim D.host.E
  latStd := Unim.std D.host.E

theorem amb_w0_eq_boundaryLocalData_w0 (A : Amb D) : A.H.w0 = BoundaryLocalData.w0 D := RingOfIntegers.ext (by
  have h := congrArg (algebraMap (𝓞 D.host.E) D.host.E) A.H.two_weight_eq_one_add_root
  rw [map_mul, map_add (f := _), map_one, map_ofNat] at h
  change algebraMap (𝓞 D.host.E) D.host.E A.H.w0 = (1 + D.host.sqrtMinusD) / 2
  rw [← A.rt_eq, eq_div_iff two_ne_zero, mul_comm]
  exact h)

end Record

end GlobalTheory.LocM
