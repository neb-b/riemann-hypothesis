module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
public import Formalism.LocalToGlobal.Divisibility.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourthPowerUnderIsogeny
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaShift

section Reindex

variable {X : Scheme.{0}}

theorem res_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE h3).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem unitsRes_res {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res h3 x :=
  Units.ext (res_res h1 h2 h3 (x : Γ(X, U)))

theorem chart_le (L : LB X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
  fun _ hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0

theorem chart_ge (L : LB X) (k : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => 𝟙 X) k ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k PUnit.unit) :=
  fun _ hx => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx PUnit.unit

end Reindex

section Reindex2

variable {X : Scheme.{0}}

theorem basicOpen_res' {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) :
    X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE h).op

theorem g_finOne (L : LB X) (n : ℕ) (i j : Fin 1 → L.ι) :
    (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))).g i j =
      res (inf_le_inf (chart_le L i) (chart_le L j)) ((lbPow L n).g (fun _ => i 0) (fun _ => j 0)) := by
  simp only [lbPow, LB.LinComb, Fin.prod_univ_one, Finset.univ_unique, Finset.prod_singleton, map_zpow]
  congr 1
  exact (unitsRes_res _ _ _ _).symm

def secFinOne {L : LB X} {n : ℕ} (s : (lbPow L n).Sec) : Out.H0 L n where
  f j := (X.presheaf.map (homOfLE (chart_le L j)).op).hom (s.f (fun _ => j 0))
  compat i j := by
    have K := inf_le_inf (chart_le L i) (chart_le L j)
    have hc := congrArg (X.presheaf.map (homOfLE K).op).hom (s.compat (fun _ => i 0) (fun _ => j 0))
    have hl : LB.wchart L (fun _ : Fin 1 => 𝟙 X) i ⊓ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤
        LB.wchart L (fun _ : Fin 1 => 𝟙 X) i := inf_le_left
    have hr : LB.wchart L (fun _ : Fin 1 => 𝟙 X) i ⊓ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤
        LB.wchart L (fun _ : Fin 1 => 𝟙 X) j := inf_le_right
    have hl0 : LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => i 0) ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) ≤
        LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => i 0) := inf_le_left
    have hr0 : LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => i 0) ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) ≤
        LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) := inf_le_right
    have e1 := res_res (chart_le L i) hl (K.trans hl0) (s.f (fun _ => i 0))
    have e2 := res_res hl0 K (K.trans hl0) (s.f (fun _ => i 0))
    have e3 := res_res (chart_le L j) hr (K.trans hr0) (s.f (fun _ => j 0))
    have e4 := res_res hr0 K (K.trans hr0) (s.f (fun _ => j 0))
    have e5 := RingHom.map_mul (X.presheaf.map (homOfLE K).op).hom
      ((lbPow L n).g (fun _ => i 0) (fun _ => j 0)).val ((X.presheaf.map (homOfLE hr0).op).hom (s.f (fun _ => j 0)))
    have e6 := congrArg Units.val (g_finOne L n i j)
    exact e1.trans (e2.symm.trans (hc.trans (e5.trans (congrArg₂ (· * ·) e6.symm (e4.trans e3.symm)))))

theorem nonzeroLocus_secFinOne {L : LB X} {n : ℕ} (s : (lbPow L n).Sec) :
    Out.nonzeroLocus (secFinOne s) = Out.nonzeroLocus s := by
  apply le_antisymm
  · refine iSup_le fun (j : Fin 1 → L.ι) => ?_
    exact (basicOpen_res' (chart_le L j) _).le.trans (inf_le_right.trans (le_iSup (fun k => X.basicOpen (s.f k)) _))
  · refine iSup_le fun (k : PUnit → L.ι) => ?_
    refine le_trans ?_ (le_iSup (fun j => X.basicOpen ((secFinOne s).f j)) (fun _ => k PUnit.unit))
    exact (le_inf ((X.basicOpen_le _).trans (chart_ge L k)) le_rfl).trans (basicOpen_res' (chart_le L _) _).ge

end Reindex2

section Theta

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {A' : Over (Sp ℂ)} [GrpObj A'] {M' : LB A'.left} {g : ℕ}

theorem differentiable_hermForm_left (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin g → ℂ) :
    Differentiable ℂ (fun z : Fin g → ℂ => hermForm Hm z a) := by
  simp only [hermForm, dotProduct]
  fun_prop

theorem isThetaFn_shift (u : HolUnif A M g) (u' : HolUnif A' M' g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hH : Hm.IsHermitian) {χ : u.Λ → ℂ} {χ' : u'.Λ → ℂ} (h : u.Λ ≤ u'.Λ) (a : Fin g → ℂ)
    (hχ : ∀ l : u.Λ, χ l = χ' (Submodule.inclusion h l) *
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im))
    {θ : (Fin g → ℂ) → ℂ} (hθ : u'.IsThetaFn Hm χ' 4 θ) :
    u.IsThetaFn Hm χ 4 (fun z => θ (z + a) * Complex.exp (-(4 * Real.pi) * hermForm Hm z a)) := by
  refine ⟨(hθ.1.comp (differentiable_id.add_const a)).mul
    (((differentiable_hermForm_left Hm a).const_mul _).cexp), fun l z => ?_⟩
  have hl : z + (l : Fin g → ℂ) + a = (z + a) + ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) := by
    simp only [Submodule.coe_inclusion]; abel
  have e1 : hermForm Hm (z + a) ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) =
      hermForm Hm z l + hermForm Hm a l := by
    simp [hermForm, add_dotProduct]
  have e2 : hermForm Hm (z + l) a = hermForm Hm z a + hermForm Hm l a := by
    simp [hermForm, add_dotProduct]
  have e3 : hermForm Hm ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) ((Submodule.inclusion h l : u'.Λ) : Fin g → ℂ) =
      hermForm Hm l l := rfl
  have e4 : hermForm Hm l a = (starRingEnd ℂ) (hermForm Hm a l) := GlobalTheory.LatticeHom.hermForm_swap_of_isHermitian hH a l
  have hw : (starRingEnd ℂ) (hermForm Hm a l) = hermForm Hm a l - 2 * Complex.I * ((hermForm Hm a l).im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  show θ (z + (l : Fin g → ℂ) + a) * _ = _ * (θ (z + a) * _)
  rw [hl, hθ.2, e1, e3, e2, e4, hw, hχ l]
  have key : Complex.exp (Real.pi * (hermForm Hm z l + hermForm Hm a l) + Real.pi / 2 * hermForm Hm l l) ^ 4 *
      Complex.exp (-(4 * Real.pi) * (hermForm Hm z a + (hermForm Hm a l - 2 * Complex.I * ((hermForm Hm a l).im : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im) ^ 4 *
      Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ 4 *
      Complex.exp (-(4 * Real.pi) * hermForm Hm z a) := by
    simp only [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_pow, mul_pow, mul_pow]
  linear_combination (χ' (Submodule.inclusion h l) ^ 4 * θ (z + a)) * key

end Theta


open GlobalTheory.LatticeHom in
theorem exists_morphism_affine_cover : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → (∀ θ, u.IsThetaFn Hm χ 4 θ → ∃ s, u.IsFnPow 4 s θ) →
    ∀ (P : Out.PolAV (Sp ℂ)) (u' : HolUnif P.A P.L g) (χ' : u'.Λ → ℂ) (h : u.Λ ≤ u'.Λ) (a : Fin g → ℂ),
    P.g = g → u'.IsAH Hm χ' →
    (∀ l : u.Λ, χ l = χ' (Submodule.inclusion h l) *
      Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im)) →
    ∃ ψ : A.left ⟶ P.A.left, ψ ≫ P.A.hom = A.hom ∧ (∀ z, (u.ex z).left ≫ ψ = (u'.ex (z + a)).left) ∧
      ∀ x : A.left, ∃ (s : Out.H0 M 4) (V : P.A.left.Opens), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen V ∧
        Out.nonzeroLocus s = ψ ⁻¹ᵁ V := by
  intro g A _ hA M u Hm χ hM hAH hsec P u' χ' h a hg hAH' hχ
  subst hg
  have hsm : Smooth A.hom := hA.smooth
  have hred : IsReduced A.left := isReduced_of_smooth_complex _ A.hom hsm
  obtain ⟨-, -, -, -, -, -, -, hsecfn, -⟩ := AnyAppellHumbert.isAH_properties abelianSchemeLaws_all.1
    abelianSchemeLaws_all.2 (fun S P M hM => AbLaw.CubeAssembly.cube_gen S P M hM) thetaUnifAV_all P u' Hm χ' hAH'
  obtain ⟨m, t, hcov, hD⟩ := veryAmple_lbPow abelianSchemeLaws_all.1.ample ℂ P 4 le_rfl
  choose θ hθ hθt using fun j => ((hsecfn 4).1 (t j)).exists
  have hG : ∀ z, Complex.exp (-(4 * Real.pi) * hermForm Hm z a) ≠ 0 := fun z => Complex.exp_ne_zero _
  choose s hs using fun j => hsec _ (isThetaFn_shift u u' hAH'.1 h a hχ (hθ j))
  let Φ : (𝟙_ (Over (Sp ℂ)) ⟶ A) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    fun y => u'.ex (Function.surjInv u.ex_onto y + a)
  have hΦ : ∀ z, Φ (u.ex z) = u'.ex (z + a) := fun z => by
    have h1 : Function.surjInv u.ex_onto (u.ex z) - z ∈ u.Λ := by
      rw [← u.ker]
      have := u.ex_add (Function.surjInv u.ex_onto (u.ex z) - z) z
      rw [sub_add_cancel, Function.surjInv_eq u.ex_onto] at this
      exact mul_eq_right.1 this.symm
    have := SectionTheta.ex_add_lattice u' (z + a) ⟨_, h h1⟩
    rw [← this]
    show u'.ex _ = u'.ex _
    congr 1
    simp only
    abel
  have hmem : ∀ j z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ Out.nonzeroLocus (t j) ↔ θ j z ≠ 0 :=
    fun j => le_preimage_nonzeroLocus_iff u' P.isLB (hθt j)
  have hmemA : ∀ j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Out.nonzeroLocus (s j) ↔
      θ j (z + a) * Complex.exp (-(4 * Real.pi) * hermForm Hm z a) ≠ 0 :=
    fun j => le_preimage_nonzeroLocus_iff u hM (hs j)
  obtain ⟨f, hf, -⟩ := existsUnique_hom_of_locally_regular existsUnique_point_of_ringHom
      (eq_of_valAt'_eq valAt'_rules existsUnique_point_of_ringHom) P.A A hred inferInstance Φ fun y => by
    obtain ⟨z₀, rfl⟩ := u.ex_onto y
    obtain ⟨i, hi⟩ := TorusEnd.exists_top_le_preimage_of_iSup_eq_top (u'.ex (z₀ + a)).left _ hcov
    obtain ⟨haff, r, hrr, hgen⟩ := hD i
    obtain ⟨U, ρ, hU0, hU⟩ := exists_regular_quotients u hM hs i (mul_ne_zero ((hmem i _).1 hi) (hG z₀))
    refine ⟨U, _, hU0, haff, fun y' hy' => ?_, fun φ => ?_⟩
    · obtain ⟨z, rfl⟩ := u.ex_onto y'
      rw [hΦ]
      exact (hmem i _).2 (left_ne_zero_of_mul (hU z hy').1)
    · obtain ⟨Q, rfl⟩ := hgen φ
      refine ⟨MvPolynomial.eval₂ (RingHom.comp (A.hom.appLE ⊤ _ le_top).hom
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) ρ Q, fun y' hy' => ?_⟩
      obtain ⟨z, rfl⟩ := u.ex_onto y'
      have h1 := left_ne_zero_of_mul (hU z hy').1
      have h2 := right_ne_zero_of_mul (hU z hy').1
      rw [hΦ, TorusEnd.valAt'_eval₂ _ _ hy', TorusEnd.valAt'_eval₂ _ _ ((hmem i _).2 h1)]
      congr 2
      funext j
      rw [(hU z hy').2 j, valAt'_eq_div_of_mul u' P.isLB (hθt i) (hθt j) (r j) (hrr j) h1,
        mul_div_mul_right _ _ h2]
  have hfe : ∀ z, (u.ex z).left ≫ f.left = (u'.ex (z + a)).left := fun z => by
    rw [← Over.comp_left, hf, hΦ]
  have heq : ∀ j, Out.nonzeroLocus (s j) = f.left ⁻¹ᵁ Out.nonzeroLocus (t j) := fun j => by
    have hpt : ∀ x' : Sp ℂ ⟶ A.left, x' ≫ A.hom = 𝟙 _ → (⊤ ≤ x' ⁻¹ᵁ Out.nonzeroLocus (s j) ↔
        ⊤ ≤ (x' ≫ f.left) ⁻¹ᵁ Out.nonzeroLocus (t j)) := by
      intro x' hx'
      obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x' hx')
      have hz' : (u.ex z).left = x' := by rw [hz]; rfl
      rw [← hz', hfe, hmemA, hmem]
      exact ⟨left_ne_zero_of_mul, fun h0 => mul_ne_zero h0 (hG z)⟩
    exact le_antisymm (ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun x' hx' => (hpt x' hx').1)
      (ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun x' hx' => (hpt x' hx').2)
  refine ⟨f.left, Over.w f, hfe, fun x => ?_⟩
  have hx : x ∈ f.left ⁻¹ᵁ (⨆ j, Out.nonzeroLocus (t j)) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨secFinOne (s j), Out.nonzeroLocus (t j), ?_, (hD j).1, ?_⟩
  · rw [nonzeroLocus_secFinOne, heq]
    exact hj
  · rw [nonzeroLocus_secFinOne, heq]

end GlobalTheory.ThetaShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLevelConjugateCharacter
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.LinkLev

theorem spack_X_eq_of_heq {D : D7} {F F' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F = F') (P : GlobalTheory.Mem.SRe.SPack D F)
    (P' : GlobalTheory.Mem.SRe.SPack D F') (h : HEq P P') : P.X = P'.X := by
  subst hF
  rw [eq_of_heq h]

theorem conjLevel_of_setting_eq {D : D7} (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X')
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ι : Formalism.L2.Theta.GA D (D.sp.Y 0) ≃* X.B.I.GA) (hι : ι = (Formalism.L2.SG.RowsJoinPinned.iotaX X h).toMulEquiv)
    (t t' : Formalism.L2.Theta.GA D (Yc D 0)) (ht : t = t') (J : Set (Formalism.L2.Theta.GA D (Yc D 0)))
    (χ : Formalism.L2.Theta.GA D (Yc D 0) → ℂ)
    (hc : Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ J χ (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X')
      (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X' (Formalism.L2.SG.RowsJoinPinned.iotaX X' h' k))) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ J χ (ι ⁻¹' seeKS X) (fun k => seeChiS X (ι k)) := by
  subst hX
  subst hι
  subst ht
  exact hc

theorem of_setting_eq {D : D7}
    (P : ∀ X : Formalism.L2.SG.HidaSetting.HidaSetting D, X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Formalism.L2.Theta.GA D (D.sp.Y 0) → Prop)
    (X X' : Formalism.L2.SG.HidaSetting.HidaSetting D) (hX : X = X') (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (h' : X'.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t t' : Formalism.L2.Theta.GA D (D.sp.Y 0)) (ht : t = t') (hP : P X' h' t') :
    P X h t := by
  subst hX
  subst ht
  exact hP

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levels_withErr_updS (R : RealDat3 D A3 Ks) (kap : ℝ) (lam e) (F : Face3 D A3) (Dc Sp Zsc)
    (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) :
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (((R.updS kap lam).withErr e).βY 0) (((R.updS kap lam).withErr e).dat0 (((R.updS kap lam).withErr e).toRealDat.levR (reFace F Dc Sp Zsc).lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt ((R.updS kap lam).withErr e).toRealDat (reFace F Dc Sp Zsc).lv2 X h t) ↔
    (Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (GlobalTheory.Mem.SRe.JR R.toRealDat F.lv2) (GlobalTheory.Mem.SRe.chiR R.toRealDat F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt R.toRealDat F.lv2 X h t) := Iff.rfl

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 4000000 in
theorem levels_of_twArgs {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : TwArgs ex t) (x : TwIn ex) (ax : HEq a.x x) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf (w.st Z).toD7) (s : Formalism.L2.Theta.GA (w.st Z).toD7 ((w.st Z).toD7.sp.Y 0))
    (hs : Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (GlobalTheory.Mem.SRe.JR t.r.z.R.toRealDat t.r.z.F.lv2) (GlobalTheory.Mem.SRe.chiR t.r.z.R.toRealDat t.r.z.F.lv2)
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt t.r.z.R.toRealDat t.r.z.F.lv2 X h s) :
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel s⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true)))
      (Formalism.L2.SG.RowsJoinPinned.iotaX X h ⁻¹' GlobalTheory.Mem.SRe.concreteLevelAdelicSubset X) (fun k => GlobalTheory.Mem.SRe.adelicCharacterOfHidaSetting X (Formalism.L2.SG.RowsJoinPinned.iotaX X h k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt x.R.toRealDat x.F.lv2 X h s := by
  cases ax
  obtain ⟨Dc, Sp, Zsc, lam, err, lam_eq, x, pack, _⟩ := a
  obtain ⟨G, grp, fin, Pl0, I0, T0, A3, core, alg, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  exact (levels_withErr_updS _ _ _ _ _ _ _ _ _ _ _).2 hs

end GlobalTheory.Mem.R3.LinkLev

namespace GlobalTheory.Mem.R3.LinkLev


end GlobalTheory.Mem.R3.LinkLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem conj_form {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w l : Fin g → ℂ) :
    l ⬝ᵥ Hm.mulVec (star w) = (starRingEnd ℂ) (w ⬝ᵥ Hm.mulVec (star l)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (starRingEnd ℂ) (Hm i j) = Hm j i := by
    have := hH.apply j i
    simpa using this
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_conj]
  rw [h1]
  ring

theorem exists_basis_in {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (s : Set (Fin g → ℂ)) (b : Module.Basis s ℝ (Fin g → ℂ)), Finite s ∧ ∀ i, b i ∈ Λ := by
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  let b := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hΛ])
  refine ⟨s, b, ?_, ?_⟩
  · exact Module.Finite.finite_basis b
  · intro i
    rw [Module.Basis.mk_apply]
    exact hs i.2

end GlobalTheory.ThetaLiouville

namespace GlobalTheory.ThetaLiouville

open Matrix Complex

theorem im_form_mem_int (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (w : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (hθ : Differentiable ℂ θ) (hθ0 : ∀ z, θ z ≠ 0)
    (hper : ∀ l ∈ Λ, ∀ z, θ (z + l) = Complex.exp (Real.pi * (w ⬝ᵥ Hm.mulVec (star l))) * θ z) :
    ∀ l ∈ Λ, ∃ n : ℤ, (w ⬝ᵥ Hm.mulVec (star l)).im = n := by
  set u : Fin g → ℂ := Hm.mulVec (star w) with hu
  let ψ : (Fin g → ℂ) → ℂ := fun z => θ z * Complex.exp (-(Real.pi * (z ⬝ᵥ u)))
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ u) := by
    have : (fun z : Fin g → ℂ => z ⬝ᵥ u) = fun z => ∑ i, z i * u i := rfl
    rw [this]
    exact Differentiable.fun_sum fun i _ => (differentiable_apply i).mul_const _
  have hψ : Differentiable ℂ ψ :=
    hθ.mul ((hlin.const_mul _).neg.cexp)

  have hshift : ∀ l ∈ Λ, ∀ z, ψ (z + l) = ψ z *
      Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) := by
    intro l hl z
    have hc := conj_form Hm hH w l
    simp only [ψ, hper l hl z, add_dotProduct]
    rw [hc]
    set a := w ⬝ᵥ Hm.mulVec (star l)
    have hsub : a - (starRingEnd ℂ) a = ((2 * a.im : ℝ) : ℂ) * I := by
      rw [Complex.sub_conj]
    rw [← hsub]
    rw [show -(↑Real.pi * (z ⬝ᵥ u + (starRingEnd ℂ) a)) =
        -(↑Real.pi * (z ⬝ᵥ u)) + (-(↑Real.pi * (starRingEnd ℂ) a)) by ring,
      Complex.exp_add,
      show (↑Real.pi * (a - (starRingEnd ℂ) a)) = ↑Real.pi * a + (-(↑Real.pi * (starRingEnd ℂ) a))
        by ring, Complex.exp_add]
    ring
  have hnorm : ∀ l ∈ Λ, ∀ z, ‖ψ (z + l)‖ = ‖ψ z‖ := by
    intro l hl z
    rw [hshift l hl z, norm_mul, Complex.norm_exp]
    simp

  obtain ⟨s, b, hfin, hbΛ⟩ := exists_basis_in Λ hΛ
  haveI : Fintype s := Fintype.ofFinite s
  have hspan : ∀ x ∈ Submodule.span ℤ (Set.range b), x ∈ Λ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hbΛ i
    | zero => exact Λ.zero_mem
    | add x y _ _ hx hy => exact Λ.add_mem hx hy
    | smul n x _ hx => exact Λ.toAddSubgroup.zsmul_mem hx n
  have hcpt : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hψ.continuous.continuousOn
  have hbd : Bornology.IsBounded (Set.range ψ) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
      rw [ZSpan.fract_apply]; abel
    rw [hz, hnorm _ (hspan _ (ZSpan.floor b z).2)]
    exact hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain b z))
  intro l hl
  have hconst : ψ (0 + l) = ψ 0 := hψ.apply_eq_apply_of_bounded hbd _ _
  rw [hshift l hl 0] at hconst
  have hψ0 : ψ 0 ≠ 0 := mul_ne_zero (hθ0 0) (Complex.exp_ne_zero _)
  have hexp : Complex.exp (Real.pi * (((2 * (w ⬝ᵥ Hm.mulVec (star l)).im : ℝ) : ℂ) * I)) = 1 := by
    have := hconst
    rw [mul_eq_left₀ hψ0] at this
    exact this
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨n, ?_⟩
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) = n := by
    have : (Real.pi : ℂ) * 2 * I * ((w ⬝ᵥ Hm.mulVec (star l)).im : ℂ) =
        (Real.pi : ℂ) * 2 * I * n := by
      push_cast at hn
      linear_combination hn
    have h0 : (Real.pi : ℂ) * 2 * I ≠ 0 := mul_ne_zero (mul_ne_zero hpi two_ne_zero) hI
    exact mul_left_cancel₀ h0 this
  exact_mod_cast h2

end GlobalTheory.ThetaLiouville
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalZeroCochainsFiniteCategoryBaseChangeBijecti
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem totalZeroCochains_finiteCategory_baseChange_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → ∀ g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F', (∀ x T, g x T = α T (x T)) → Function.Bijective (liftSemi g) := by
  intro R R' _ _ _ C _ _ _ F F' α _ hs hb g hg
  let f : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T =>
    { toFun := α T
      map_add' := fun a b => map_add (α T) a b
      map_smul' := fun r b => hs T r b }
  exact liftSemi_pi_bijective R R' C (fun T => F.obj T) (fun T => F'.obj T) f g
    (fun x T => hg x T) (fun T => hb T (f T) (fun _ => rfl))

end GlobalTheory
end

