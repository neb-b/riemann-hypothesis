module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsSectionRing
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KodairaSpencerClassCohomologousAlongEndomorphism
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroLocusLeOpenPolarisationComplex
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.AmpleBasis

open SectionRing

variable {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X)

def Extends (N : ℕ) (D : X.Opens) (t : Fam p L) (f : Γ(X, D)) (e : ℕ) : Prop :=
  ∃ σ ∈ secs p L (N * e), ∀ k,
    resG X (inf_le_right : D ⊓ chart L k ≤ _) (evalFam p L k σ) =
      resG X (inf_le_left : D ⊓ chart L k ≤ _) f *
        resG X (inf_le_right : D ⊓ chart L k ≤ _) (evalFam p L k t) ^ e

variable {p L} {N : ℕ} {D : X.Opens} {t : Fam p L}

theorem Extends.mul {f g : Γ(X, D)} {e e' : ℕ} (hf : Extends p L N D t f e)
    (hg : Extends p L N D t g e') : Extends p L N D t (f * g) (e + e') := by
  obtain ⟨σ, hσ, h⟩ := hf
  obtain ⟨τ, hτ, h'⟩ := hg
  refine ⟨σ * τ, ?_, fun k => ?_⟩
  · rw [mul_add]
    exact SetLike.GradedMul.mul_mem hσ hτ
  · simp only [map_mul]
    rw [h k, h' k, pow_add]
    ring

theorem Extends.add {f g : Γ(X, D)} {e : ℕ} (hf : Extends p L N D t f e)
    (hg : Extends p L N D t g e) : Extends p L N D t (f + g) e := by
  obtain ⟨σ, hσ, h⟩ := hf
  obtain ⟨τ, hτ, h'⟩ := hg
  refine ⟨σ + τ, add_mem hσ hτ, fun k => ?_⟩
  simp only [map_add (f := _)]
  rw [h k, h' k, add_mul]

theorem extends_one (ht : t ∈ secs p L N) (e : ℕ) : Extends p L N D t 1 e := by
  refine ⟨t ^ e, ?_, fun k => ?_⟩
  · have hp := SetLike.pow_mem_graded e ht
    rwa [smul_eq_mul, mul_comm] at hp
  · rw [map_pow, map_pow, map_one]
    exact (_root_.one_mul _).symm

private theorem resG_constHom' {U V : X.Opens} (h : V ≤ U) (a : K) :
    resG X h (constHom p U a) = constHom p V a := by
  have hU : U ≤ p ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e : p.appLE ⊤ U hU ≫ X.presheaf.map (homOfLE h).op = p.appLE ⊤ V (h.trans hU) := by
    rw [Scheme.Hom.appLE_map]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) e

theorem extends_const (a : K) : Extends p L N D t (constHom p D a) 0 := by
  refine ⟨fun j => constHom p (chart L j) a, ?_, fun k => ?_⟩
  · rw [mul_zero]
    intro i j
    rw [trans_zero, _root_.one_mul]
    change resG X _ (constHom p _ a) = resG X _ (constHom p _ a)
    rw [resG_constHom', resG_constHom']
  · rw [pow_zero, _root_.mul_one]
    change resG X _ (constHom p _ a) = resG X _ (constHom p _ a)
    rw [resG_constHom', resG_constHom']

private theorem extends_add (ht : t ∈ secs p L N) {f : Γ(X, D)} {e : ℕ}
    (hf : Extends p L N D t f e) (e' : ℕ) : Extends p L N D t f (e + e') := by
  simpa only [_root_.mul_one] using hf.mul (extends_one ht e')

theorem extends_eval₂ {J : Type} (ht : t ∈ secs p L N) (r : J → Γ(X, D))
    (hr : ∀ j, Extends p L N D t (r j) 1) (F : MvPolynomial J K) :
    ∃ e, Extends p L N D t (MvPolynomial.eval₂ (constHom p D) r F) e := by
  induction F using MvPolynomial.induction_on
  next a =>
    refine ⟨0, ?_⟩
    rw [MvPolynomial.eval₂_C]
    exact extends_const a
  next P Q hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    refine ⟨a + b, ?_⟩
    rw [MvPolynomial.eval₂_add]
    refine (extends_add ht ha b).add ?_
    rw [add_comm a b]
    exact extends_add ht hb a
  next P j hP =>
    obtain ⟨a, ha⟩ := hP
    refine ⟨a + 1, ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact ha.mul (hr j)

private theorem basicOpen_resG' {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    X.basicOpen (resG X h x) = V ⊓ X.basicOpen x :=
  Scheme.basicOpen_res X x (homOfLE h).op

theorem exists_locus (s : (lbPow L N).Sec) (f : Γ(X, Out.nonzeroLocus s)) (e : ℕ)
    (hf : Extends p L N (Out.nonzeroLocus s) (secEquiv p L N s : Fam p L) f e)
    (y : X) (hy : y ∈ X.basicOpen f) :
    ∃ (n : ℕ) (σ : (lbPow L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ X.basicOpen f := by
  obtain ⟨σ, hσ, h⟩ := hf
  have hmem : σ * (secEquiv p L N s : Fam p L) ∈ secs p L (N * e + N) :=
    SetLike.GradedMul.mul_mem hσ (secEquiv p L N s).2
  have key : ∀ k, (Out.nonzeroLocus s ⊓ chart L k) ⊓
      X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) =
      (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen f) ⊓
        (Out.nonzeroLocus s ⊓ chart L k ⊓ X.basicOpen (evalFam p L k (secEquiv p L N s : Fam p L))) := by
    intro k
    rw [← basicOpen_resG' (inf_le_right : Out.nonzeroLocus s ⊓ chart L k ≤ _), map_mul, map_mul, h k,
      _root_.mul_assoc, ← pow_succ, Scheme.basicOpen_mul, Scheme.basicOpen_pow _ _ e.succ_pos,
      basicOpen_resG', basicOpen_resG']
  refine ⟨N * e + N, (secEquiv p L (N * e + N)).symm ⟨_, hmem⟩, ?_, ?_⟩
  · change y ∈ ⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))
    have hyD : y ∈ Out.nonzeroLocus s := X.basicOpen_le f hy
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp (show y ∈ ⨆ k, X.basicOpen (s.f k) from hyD)
    have hkc : y ∈ chart L k := X.basicOpen_le _ hk
    have hmemk : y ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓
        X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) := by
      rw [key k]
      exact ⟨⟨⟨hyD, hkc⟩, hy⟩, ⟨⟨hyD, hkc⟩, hk⟩⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hmemk.2⟩
  · change (⨆ k, X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L)))) ≤ X.basicOpen f
    refine iSup_le fun k z hz => ?_
    have hz2 := hz
    rw [map_mul, Scheme.basicOpen_mul] at hz2
    have hz' : z ∈ X.basicOpen (s.f k) := hz2.2
    have hzD : z ∈ Out.nonzeroLocus s := TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hz'⟩
    have hkc : z ∈ chart L k := X.basicOpen_le _ hz'
    have hzk : z ∈ (Out.nonzeroLocus s ⊓ chart L k) ⊓
        X.basicOpen (evalFam p L k (σ * (secEquiv p L N s : Fam p L))) := ⟨⟨hzD, hkc⟩, hz⟩
    rw [key k] at hzk
    exact hzk.1.2

end GlobalTheory.AmpleBasis

namespace GlobalTheory

open SectionRing AmpleBasis

theorem exists_nonzeroLocus_le : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (O : P₀.A.left.Opens) (y : P₀.A.left), y ∈ O → ∃ (n : ℕ) (σ : (lbPow P₀.L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ O := by
  intro hL P₀ O y hy
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow hL.ample ℂ P₀ 4 le_rfl
  have hyt : y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by
    rw [hcov]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hyt
  obtain ⟨haff, r, hr, hpoly⟩ := hs i
  obtain ⟨f, hfO, hyf⟩ := haff.exists_basicOpen_le ⟨y, hy⟩ hi
  obtain ⟨F, hF⟩ := hpoly f
  have hrj : ∀ j, Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i)) (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L)
      (r j) 1 := by
    intro j
    refine ⟨secEquiv P₀.A.hom P₀.L 4 (s j), ?_, fun k => ?_⟩
    · rw [Nat.mul_one]
      exact (secEquiv P₀.A.hom P₀.L 4 (s j)).2
    · rw [pow_one]
      exact hr j k
  obtain ⟨e, he⟩ := extends_eval₂ (secEquiv P₀.A.hom P₀.L 4 (s i)).2 r hrj F
  have he' : Extends P₀.A.hom P₀.L 4 (Out.nonzeroLocus (s i))
      (secEquiv P₀.A.hom P₀.L 4 (s i) : Fam P₀.A.hom P₀.L) f e := by
    rw [hF]
    exact he
  obtain ⟨n, σ, hyσ, hσf⟩ := exists_locus (s i) f e he' y hyf
  exact ⟨n, σ, hyσ, hσf.trans hfO⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits

noncomputable section

namespace GlobalTheory.SquareGenerated

section
variable {X Y : Scheme.{0}} {H : LB X}

theorem unitAt_of_mem (s : LB.Sec H) (φ : Y ⟶ X) (y : Y) (hy : φ y ∈ Out.nonzeroLocus s) :
    UnitAt H (K := Fin 1) (fun _ => φ) (fun _ => 1) y := by
  have v : ∀ (j : Fin 1 → H.ι) (z : Y), z ∈ LB.wchart H (fun _ : Fin 1 => φ) j →
      gs (𝟙 Y) z (LB.wchart H (fun _ : Fin 1 => φ) j)
        ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))) = gs (𝟙 Y ≫ φ) z (H.U (j 0)) (s.f (j 0)) := fun j z hz =>
    (gs_res _ z _ hz _).trans (gs_pull _ φ z _ (LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz) _)
  let s' : LB.Sec (LB.LinComb H (K := Fin 1) (fun _ => φ) (fun _ => 1)) :=
    { f := fun j => (Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) j 0)).op).hom
          ((φ.app _).hom (s.f (j 0)))
      compat := fun j j' => fn_ext fun z hz => by
        refine ((gs_res (𝟙 Y) z _ hz _).trans (v j z hz.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) z _ hz _ _).trans
          (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) z _ hz _).trans
            (congrArg Units.val (gm_linComb H _ _ (𝟙 Y) z j j' hz.1 hz.2)))
              ((gs_res (𝟙 Y) z _ hz _).trans (v j' z hz.2)))).symm)
        have hm : (𝟙 Y ≫ φ) z ∈ H.U (j 0) ⊓ H.U (j' 0) :=
          ⟨LB.wchart_le H (fun _ : Fin 1 => φ) j 0 hz.1, LB.wchart_le H (fun _ : Fin 1 => φ) j' 0 hz.2⟩
        refine (gs_res _ z _ hm _).symm.trans ((congrArg (gs _ z _) (s.compat (j 0) (j' 0))).trans
          ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res _ z _ hm _))))
        rw [gs_unit _ z _ hm, Fin.prod_univ_one, zpow_one] }
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨s', fun J hJ => isUnit_sval s' (𝟙 Y) y hJ (fun _ => k) ?_⟩
  have hm : y ∈ LB.wchart H (fun _ : Fin 1 => φ) (fun _ => k) :=
    Set.mem_iInter.2 fun _ => X.basicOpen_le _ hk
  show y ∈ Y.basicOpen ((Y.presheaf.map (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op).hom
          ((φ.app _).hom (s.f k)))
  have e := Y.basicOpen_res ((φ.app _).hom (s.f k))
    (homOfLE (LB.wchart_le H (fun _ : Fin 1 => φ) (fun _ => k) 0)).op
  refine e ▸ ⟨hm, ?_⟩
  exact (SetLike.ext_iff.1 (Scheme.preimage_basicOpen φ (s.f k)) y).1 hk

theorem exists_sec_pw (hH : H.IsLB) (t : ℤ) (y : X)
    (h : UnitAt H (K := Fin 1) (fun _ => 𝟙 X) (fun _ => t) y) :
    ∃ u : LB.Sec (pw H t), y ∈ Out.nonzeroLocus u := by
  obtain ⟨s, hs⟩ := h
  have le : ∀ i : H.ι, H.U i ≤ LB.wchart H (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i z hz => Set.mem_iInter.2 fun _ => hz
  let u : LB.Sec (pw H t) :=
    { f := fun i => (X.presheaf.map (homOfLE (le i)).op).hom (s.f fun _ => i)
      compat := fun i j => fn_ext fun z hz => by
        refine ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le i) hz.1 _)).trans
          (Eq.trans ?_ ((gs_mul (𝟙 X) z _ hz _ _).trans
          (congrArg₂ (· * ·) (gs_unit (𝟙 X) z _ hz _)
              ((gs_res (𝟙 X) z _ hz _).trans (gs_res (𝟙 X) z (le j) hz.2 _)))).symm)
        refine (sec_trans s (𝟙 X) z (le i hz.1) (le j hz.2)).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
        exact (Fin.prod_univ_one _).trans (map_zpow _ _ _).symm }
  choose I hI using fun χ : X ⟶ X => exists_chart hH (χ y)
  have hm : y ∈ H.U (I (𝟙 X ≫ 𝟙 X)) := hI (𝟙 X ≫ 𝟙 X)
  refine ⟨u, TopologicalSpace.Opens.mem_iSup.2 ⟨I (𝟙 X ≫ 𝟙 X), (X.mem_basicOpen _ _ hm).2 ?_⟩⟩
  exact (congrArg IsUnit ((gs_eq (𝟙 X) y _ hm _).symm.trans (gs_res (𝟙 X) y (le _) hm _))).mpr (hs I hI)

end

theorem exists_sec_sq {O : Type} [CommRing O] [IsLocalRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A]
    {H : LB A.left} (hH : H.IsLB) (hT : Triv (Theta A H)) (s : LB.Sec H) (a : 𝟙_ (Over (Sp O)) ⟶ A)
    (y : A.left) (h₁ : ((toUnit A ≫ a) * 𝟙 A).left y ∈ Out.nonzeroLocus s)
    (h₂ : ((toUnit A ≫ a⁻¹) * 𝟙 A).left y ∈ Out.nonzeroLocus s) :
    ∃ u : LB.Sec (pw H 2), y ∈ Out.nonzeroLocus u := by
  obtain ⟨t, ht⟩ := hT
  let χ : Fin 4 → (Sp O ⟶ A.left) := ![(a * a⁻¹).left, a.left, (a⁻¹).left, (1 : 𝟙_ (Over (Sp O)) ⟶ A).left]
  choose i hi using fun k => exists_chart hH (χ k (IsLocalRing.closedPoint O))
  have e : ∀ k, (![((toUnit A ≫ a) * (toUnit A ≫ a⁻¹)).left, (toUnit A ≫ a).left,
      (toUnit A ≫ a⁻¹).left, (1 : A ⟶ A).left] k) = (toUnit A).left ≫ χ k := by
    intro k
    fin_cases k
    · show _ = (toUnit A ≫ (a * a⁻¹)).left
      rw [MonObj.comp_mul]; rfl
    · rfl
    · rfl
    · show _ = (toUnit A ≫ (1 : 𝟙_ (Over (Sp O)) ⟶ A)).left
      rw [MonObj.comp_one]; rfl
  obtain ⟨u, hu⟩ := GlobalTheory.AbSquare.exists_gen_square hH t ht (toUnit A ≫ a) (toUnit A ≫ a⁻¹) (𝟙 A) i
    (fun k z => by
      rw [e k]
      have h : χ k ⁻¹ᵁ H.U (i k) = ⊤ := (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
      show (toUnit A).left z ∈ χ k ⁻¹ᵁ H.U (i k)
      rw [h]; trivial)
  have hu' : UnitAt H _ _ y := ⟨genSec u hu, fun J hJ => by
    rw [sval_genSec u hu _ y hJ]; exact Units.isUnit _⟩
  have e1 : (toUnit A ≫ a) * (toUnit A ≫ a⁻¹) * 𝟙 A = 𝟙 A := by
    rw [← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, _root_.one_mul]
  refine exists_sec_pw hH 2 y (UnitAt.congr hH (formEq_of_add fun U _ hh => ?_)
    (((unitAt_of_mem s _ y h₁).mul (unitAt_of_mem s _ y h₂)).mul hu'))
  simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, e1, Sum.elim_inl, Sum.elim_inr]
  simp
  module

theorem exists_secs_sq_generate : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ H : LB A.left, H.IsLB → Triv (Theta A H) → ∀ s : LB.Sec H, (∃ x ∈ Out.nonzeroLocus s, A.hom x = IsLocalRing.closedPoint O) → ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw H 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro O K _ _ _ _ _ _ _ A _ _ hA H hH hT s hs
  obtain ⟨-, hk, hlift⟩ := _root_.GlobalTheory.valuationRing_henselian_and_lift_of_isAlgClosed O K
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ inferInstance inferInstance
  let t : Sp (IsLocalRing.ResidueField O) ⟶ Sp O := spMap (IsLocalRing.residue O)
  let T : Over (Sp O) := Over.mk t
  have : IsIntegral (T ⊗ A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t A.hom).flip
  let p : Sp (IsLocalRing.ResidueField O) := IsLocalRing.closedPoint (IsLocalRing.ResidueField O)
  have htp : t p = IsLocalRing.closedPoint O := IsLocalRing.comap_closedPoint (IsLocalRing.residue O)
  have up : ∀ x : A.left, A.hom x = IsLocalRing.closedPoint O → ∃ z : (T ⊗ A).left, (snd T A).left z = x := by
    intro x hx
    have : x ∈ Set.range (pullback.snd t A.hom) := by
      rw [Scheme.Pullback.range_snd]
      exact ⟨p, htp.trans hx.symm⟩
    exact this
  let W : A.left.Opens := ⨆ u : LB.Sec (pw H 2), Out.nonzeroLocus u
  have hW : W = ⊤ := by
    by_contra hne
    have hZ : ((W : Set A.left)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      exact fun h => hne (SetLike.coe_injective h)
    have hc : IsClosed (A.hom '' (W : Set A.left)ᶜ) := A.hom.isClosedMap _ W.isOpen.isClosed_compl
    obtain ⟨x₀, hx₀, hx₁⟩ : IsLocalRing.closedPoint O ∈ A.hom '' (W : Set A.left)ᶜ := by
      obtain ⟨q, hq⟩ := hZ.image A.hom
      exact (IsLocalRing.specializes_closedPoint q).mem_closed hc hq
    obtain ⟨z₀, hz₀⟩ := up x₀ hx₁
    have : LocallyOfFiniteType (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left :=
      inferInstanceAs (LocallyOfFiniteType (pullback.fst t A.hom))
    have : JacobsonSpace (T ⊗ A).left :=
      LocallyOfFiniteType.jacobsonSpace (X := (T ⊗ A).left) (Y := Sp (IsLocalRing.ResidueField O)) (fst T A).left
    obtain ⟨c, hcZ, hcc⟩ := nonempty_inter_closedPoints
      (Z := (((snd T A).left ⁻¹ᵁ W : (T ⊗ A).left.Opens) : Set (T ⊗ A).left)ᶜ)
      ⟨z₀, by
        show ¬ (snd T A).left z₀ ∈ W
        rw [hz₀]; exact hx₀⟩ ((snd T A).left ⁻¹ᵁ W).isOpen.isClosed_compl.isLocallyClosed
    let σ := pointOfClosedPoint (X := (T ⊗ A).left) (K := IsLocalRing.ResidueField O) (fst T A).left c hcc
    have hσ : σ ≫ (fst T A).left = 𝟙 _ := pointOfClosedPoint_comp _ c hcc
    have hσp : σ p = c := pointOfClosedPoint_apply _ c hcc p
    let σ' : T ⟶ T ⊗ A := Over.homMk σ (by
      rw [← Over.w (fst T A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hσ).trans (Category.id_comp _))
    let x : T ⟶ A := σ' ≫ snd T A
    have hx : x.left p ∉ W := by
      show (snd T A).left (σ p) ∉ W
      rw [hσp]; exact hcZ
    obtain ⟨y₀, hy₀, hy₁⟩ := hs
    obtain ⟨z₁, hz₁⟩ := up y₀ hy₁
    obtain ⟨a, h₁, h₂⟩ := GlobalTheory.NoBasePoint.exists_two_points t ((snd T A).left ⁻¹ᵁ Out.nonzeroLocus s)
      ⟨z₁, by
        show (snd T A).left z₁ ∈ Out.nonzeroLocus s
        rw [hz₁]; exact hy₀⟩ x x
    obtain ⟨b, hb, hba⟩ := hlift A.left A.hom inferInstance a.left (Over.w a)
    let b' : 𝟙_ (Over (Sp O)) ⟶ A := Over.homMk b hb
    have hb' : toUnit T ≫ b' = a := Over.OverMorphism.ext hba
    have key : ∀ (d : 𝟙_ (Over (Sp O)) ⟶ A), (Out.ptSecT A ((toUnit T ≫ d) * x)).left p ∈
        (snd T A).left ⁻¹ᵁ Out.nonzeroLocus s →
        ((toUnit A ≫ d) * 𝟙 A).left (x.left p) ∈ Out.nonzeroLocus s := by
      intro d hd
      have e : x ≫ ((toUnit A ≫ d) * 𝟙 A) = Out.ptSecT A ((toUnit T ≫ d) * x) ≫ snd T A := by
        simp [Out.ptSecT, MonObj.comp_mul]
      have e' : ((toUnit A ≫ d) * 𝟙 A).left (x.left p) =
          (snd T A).left ((Out.ptSecT A ((toUnit T ≫ d) * x)).left p) :=
        congrArg (fun q => q.left p) e
      rw [e']; exact hd
    obtain ⟨u, hu⟩ := exists_sec_sq A hH hT s b' (x.left p) (key b' (by rw [hb']; exact h₁ p))
      (key b'⁻¹ (by rw [GrpObj.comp_inv, hb']; exact h₂ p))
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨u, hu⟩)
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun u : LB.Sec (pw H 2) => (Out.nonzeroLocus u : Set A.left)) (fun u => (Out.nonzeroLocus u).isOpen)
    (fun y _ => by
      have : y ∈ W := by rw [hW]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 this))
  refine ⟨F.card, Fin.cons (secZero _) (fun i => (F.equivFin.symm i : LB.Sec (pw H 2))), top_unique fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨(F.equivFin ⟨u, hu⟩).succ, ?_⟩
  rw [Fin.cons_succ, Equiv.symm_apply_apply]
  exact hy

end GlobalTheory.SquareGenerated
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MatrixIntertwinesAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS

private lemma constFn_sub' {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (a b : K) :
    constFn q O (a - b) = constFn q O a - constFn q O b := by
  unfold constFn
  simp only [map_sub]

private lemma constFn_mul_moduli {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (a b : K) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  unfold constFn
  simp only [map_mul]

private lemma constFn_sum {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) {n : ℕ}
    (f : Fin n → K) : constFn q O (∑ k, f k) = ∑ k, constFn q O (f k) := by
  unfold constFn
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]

private lemma sum_sub_sum_mul_eq_sub_sub_sum {R : Type*} [CommRing R] {n : ℕ} (A B u v : Fin n → R) (M N : Fin n → Fin n → R) :
    ∑ a, (∑ b, A b * M b a - ∑ b, B b * N a b) * v a =
      (∑ a, A a * u a - ∑ a, B a * ∑ b, N b a * v b) - ∑ a, A a * (u a - ∑ b, M a b * v b) := by
  have h1 : ∑ a, ∑ b, A b * M b a * v a = ∑ a, ∑ b, A a * (M a b * v b) := by
    rw [Finset.sum_comm]; simp only [_root_.mul_assoc]
  have h2 : ∑ a, ∑ b, B b * N a b * v a = ∑ a, ∑ b, B a * (N b a * v b) := by
    rw [Finset.sum_comm]; simp only [_root_.mul_assoc]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_sub, Finset.mul_sum]
  rw [h1, h2]
  abel

theorem lc_row_mul_sub {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens} (q : Y ⟶ Sp K) {g : ℕ}
    (F Θ F' : Matrix (Fin g) (Fin g) K) (θ φ : Fin g → C1 U) (x : Fin g) :
    lc q ((F * Θ - Θ * F'.transpose) x) φ =
      (lc q (F x) θ - lc q (Θ x) (fun c => lc q (fun y => F' y c) φ)) -
        lc q (F x) (fun b => θ b - lc q (Θ b) φ) := by
  funext i j
  simp only [lc, Pi.sub_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    constFn_sub', constFn_sum, constFn_mul_moduli]
  exact sum_sub_sum_mul_eq_sub_sub_sum (fun b => constFn q (U i ⊓ U j) (F x b)) (fun b => constFn q (U i ⊓ U j) (Θ x b))
    (fun b => θ b i j) (fun b => φ b i j) (fun a b => constFn q (U i ⊓ U j) (Θ a b))
    (fun a b => constFn q (U i ⊓ U j) (F' a b))

theorem matrix_intertwines_adjoint : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)) (g : ℕ) (v : Fin g → (epsR K ⟶ P₀.A)) (dd : Fin g → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)), IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (P : Out.PolAV (Sp R)) (m : P₀.A.left ⟶ P.A.left) (L : LB P.A.left) [Finite L.ι] (D : R → K) (d : L.ι → ∀ O : P.A.left.Opens, Γ(P.A.left, O) → Γ(P₀.A.left, m ⁻¹ᵁ O)) (θ φ : Fin g → C1 (fun i => m ⁻¹ᵁ L.U i)), IsGrpPullback P₀.A P.A (spMap x₀) m → L.IsLB → (∀ i, IsAffineOpen (L.U i)) → LBIso P₀.L (L.pull m) → KSCoc P₀.A.hom P.A.hom m D L.U dd d θ → IsDlog m L dd φ → ∀ (Θ : Matrix (Fin g) (Fin g) K) (f : P.A ⟶ P.A) (f₀ f₀' : P₀.A ⟶ P₀.A) (F F' : Matrix (Fin g) (Fin g) K), (∀ b, IsCob (fun i => m ⁻¹ᵁ L.U i) (θ b - lc P₀.A.hom (Θ b) φ)) → IsMonHom f₀ → IsMonHom f₀' → f₀.left ≫ m = m ≫ f.left → LBIso (cubeLB P₀.A ![fst P₀.A P₀.A ≫ f₀, snd P₀.A P₀.A] P₀.L) (cubeLB P₀.A ![fst P₀.A P₀.A, snd P₀.A P₀.A ≫ f₀'] P₀.L) → (∀ j, IsLieComb (fun i => F i j) v (v j ≫ f₀)) → (∀ j, IsLieComb (fun i => F' i j) v (v j ≫ f₀')) → F * Θ = Θ * F'.transpose := by
  intro K _ P₀ g v dd hv hdd R _ x₀ P m L _ D d θ φ hpb hL hLaff hLB hKS hφ Θ f f₀ f₀' F F' hcob hf₀ hf₀' hfm hcube hF hF'
  have hsm : Smooth P₀.A.hom := @IsAbelianScheme.smooth _ P₀.A P₀.grp P₀.isAb
  have hA := _root_.GlobalTheory.KS.cohom_ksCoc_of_endomorphism K P₀.A g v dd hsm hv hdd R x₀ P.A.left P.A.hom m hpb.1 L.ι L.U D d θ f.left f₀ F hKS hf₀
    (Over.w f) hfm hF
  have hB := _root_.GlobalTheory.KS.AdjDlog.cohom_dlog_of_adjoint K P₀ g v dd hv hdd P.A.left m L φ f₀ f₀' F' hL hLB hφ hf₀ hf₀' hcube hF'
  have hI := (_root_.GlobalTheory.KS.DlogPol.dlog_independent K P₀ g v dd hv hdd P.A.left m L hL hLB).2 φ hφ |>.2
  have hcov : ⨆ i, m ⁻¹ᵁ L.U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hL.cover]; rfl
  have hrow : ∀ x, (F * Θ - Θ * F'.transpose) x = 0 := by
    intro x
    apply hI
    rw [lc_row_mul_sub]
    refine IsCob.sub (Cohom.isCob_sub f₀.left hcov (hA x)
      (cohom_lc P₀.A.hom f₀.left (Over.w f₀) (Θ x) _ φ hB) (hcob x)) ?_
    exact isCob_lc P₀.A.hom (F x) _ hcob
  rw [← sub_eq_zero]
  ext x y
  exact congrFun (hrow x) y

end GlobalTheory.KS
end
end

