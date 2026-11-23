module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoSymmetricBirigidifiedCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin

open GlobalTheory.CatCoh GlobalTheory.CechDR

variable {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens)

def IsCoc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
      resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
        (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')

def CechFG (R : Type) [CommRing R] (act : ∀ i i' : J, R →+* Γ(Z, W i ⊓ W i')) : Prop :=
  ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, IsCoc W (e k)) ∧
    ∀ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCoc W c → ∃ (r : Fin N → R) (h : ∀ i : J, Γ(Z, W i)),
      ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') + ∑ k, act i i' (r k) * e k i i'

variable {R : Type} [CommRing R] (s : Z ⟶ Sp R)

def fv (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) : Γ(Z, B.1) :=
  f (Opposite.op A) (Opposite.op B) (homOfLE h).op

def gv (g : C0 (OAff s)) (A : Z.affineOpens) : Γ(Z, A.1) := g (Opposite.op A)

theorem fv_d0 (g : C0 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (d0 (OAff s) g) h = gv s g B - resG Z h (gv s g A) := rfl

theorem fv_add (f f' : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (f + f') h = fv s f h + fv s f' h := rfl

theorem fv_smul (r : R) (f : C1 (OAff s)) {A B : Z.affineOpens} (h : B.1 ≤ A.1) :
    fv s (r • f) h = (secMap s B.1).hom r * fv s f h := rfl

theorem res_val (f : Z1 (OAff s)) {A B C : Z.affineOpens} (hBA : B.1 ≤ A.1) (hCB : C.1 ≤ B.1) :
    resG Z hCB (fv s f.1 hBA) = fv s f.1 (hCB.trans hBA) - fv s f.1 (A := B) hCB :=
  eq_sub_of_add_eq (f.2 (homOfLE hBA).op (homOfLE hCB).op).symm

variable (hW : ∀ i, IsAffineOpen (W i)) (hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i'))

def rho (f : C1 (OAff s)) (i i' : J) : Γ(Z, W i ⊓ W i') :=
  fv s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_left -
    fv s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) inf_le_right

theorem rho_isCoc (hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) (f : Z1 (OAff s)) :
    IsCoc W (rho W s hW hW2 f.1) := by
  intro i i' i''
  let T : Z.affineOpens := ⟨W i ⊓ W i' ⊓ W i'', hW3 i i' i''⟩
  have h1 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_left inf_le_left
  have h2 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i ⊓ W i', hW2 i i'⟩) (C := T) inf_le_right inf_le_left
  have h3 := res_val s f (A := ⟨W i', hW i'⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h4 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i' ⊓ W i'', hW2 i' i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have h5 := res_val s f (A := ⟨W i, hW i⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have h6 := res_val s f (A := ⟨W i'', hW i''⟩) (B := ⟨W i ⊓ W i'', hW2 i i''⟩) (C := T) inf_le_right
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  simp only [rho, map_sub]
  rw [h1, h2, h3, h4, h5, h6]
  ring

theorem rho_add (f f' : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (f + f') i i' = rho W s hW hW2 f i i' + rho W s hW hW2 f' i i' := by
  simp only [rho, fv_add]
  ring

theorem rho_smul (r : R) (f : C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (r • f) i i' = (secMap s (W i ⊓ W i')).hom r * rho W s hW hW2 f i i' := by
  simp only [rho, fv_smul]
  ring

theorem rho_zero (i i' : J) : rho W s hW hW2 0 i i' = 0 := sub_self (0 : Γ(Z, W i ⊓ W i'))

theorem rho_sum {N : ℕ} (r : Fin N → R) (f : Fin N → C1 (OAff s)) (i i' : J) :
    rho W s hW hW2 (∑ k, r k • f k) i i' = ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * rho W s hW hW2 (f k) i i' := by
  induction N with
  | zero => simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact rho_zero W s hW hW2 i i'
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, rho_add, rho_smul, ih]

theorem rho_d0 (g : C0 (OAff s)) (i i' : J) :
    rho W s hW hW2 (d0 (OAff s) g) i i' =
      resG Z inf_le_left (-gv s g ⟨W i, hW i⟩) - resG Z inf_le_right (-gv s g ⟨W i', hW i'⟩) := by
  simp only [rho, fv_d0, map_neg]
  ring

end GlobalTheory.CechFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointIffBiextensionPullbacksIsomorphic
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.RosatiFormAdj

theorem real_eq_of_exp {p : ℤ} {r : ℝ}
    (h : ∀ n : ℕ, 0 < n → Complex.exp (-(2 * Real.pi * Complex.I) * (p : ℂ) / n) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / n)) : (p : ℝ) = r := by
  have h1 := h 1 one_pos
  simp only [Nat.cast_one, div_one] at h1
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  have hr : (r : ℂ) = ((p + m : ℤ) : ℂ) := by
    have := Complex.two_pi_I_ne_zero
    push_cast
    apply mul_left_cancel₀ this
    linear_combination hm
  have hr' : r = ((p + m : ℤ) : ℝ) := by exact_mod_cast hr
  have := GlobalTheory.HermAdjoint.int_eq_of_exp (p := p) (q := p + m) (fun n hn => by rw [h n hn, hr])
  rw [hr', ← this]

theorem lbIso_pull_iff_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∀ (f f' : A ⟶ A) (u u' : La →+ La), IsMonHom f → IsMonHom f' → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f) → (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (u' x)) = e ((k : ℂ)⁻¹ • Q x) ≫ f') → (LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔ ∀ x y, EF (u x) y = EF x (u' y)) := by
  intro A _ _ g hA hg P hP h1 h2 hsym hamp e La _ Q EF he hQ hker hW f f' u u' hf hf' hu hu'
  obtain ⟨M, hM, hPM⟩ := _root_.GlobalTheory.BiRoot.exists_lbIso_lam_of_birigid_symm A g hA hg P hP h1 h2 hsym
  obtain ⟨v, Hm, χ, hve, hAH⟩ := _root_.GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp A g hA hg e he M hM
  have hN : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hND := _root_.GlobalTheory.LamPull.lbIso_pull_lift A P M hP hM hPM A (𝟙 A) (𝟙 A)
  have hmem : ∀ z, z ∈ v.Λ ↔ z ∈ Q.range := fun z => (v.ker z).symm.trans (by rw [hve]; exact hker z)
  have hEF : ∀ a b, (EF a b : ℝ) = 2 * (hermForm Hm (Q a) (Q b)).im := by
    intro a b
    apply real_eq_of_exp
    intro k hk
    have hc := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k)
    have hc' := Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm (Q a) (Q b)).im : ℝ)) : ℂ) / k)
    have w1 := hW k a b (Units.mk0 _ hc) hk rfl
    have w2 := _root_.GlobalTheory.DiagWeil.weilIs_diag_lam A g hA hg M v Hm χ hM hAH _ hN hND hamp k (Q a) (Q b) (Units.mk0 _ hc') hk
      ((hmem _).2 ⟨a, rfl⟩) ((hmem _).2 ⟨b, rfl⟩) rfl
    rw [hve, hve] at w2
    exact congrArg Units.val (_root_.GlobalTheory.WeilComplexUnique.weilIs_unitOn_unique_complex (Sp ℂ) A g hA hg _ hN (𝟙 (Sp ℂ)) k _ _ _ _ w1 w2)
  obtain ⟨F, hF, -⟩ := _root_.GlobalTheory.ExpLin.existsUnique_linear_lift (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e e f he he hf
  obtain ⟨F', hF', -⟩ := _root_.GlobalTheory.ExpLin.existsUnique_linear_lift (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e e f' he he hf'
  have hlift : ∀ (G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (w : La →+ La), (∀ z, e (G z) = e z ≫ φ) →
      (∀ (k : ℕ) x, 0 < k → e ((k : ℂ)⁻¹ • Q (w x)) = e ((k : ℂ)⁻¹ • Q x) ≫ φ) → ∀ x, G (Q x) = Q (w x) := by
    intro G φ w hG hw x
    refine sub_eq_zero.1 (_root_.GlobalTheory.discrete_submodule_inv_smul_eq_zero g v.Λ v.discrete (G (Q x) - Q (w x)) fun k hk => ?_)
    refine (hmem _).2 ((hker _).1 ?_)
    have e1 : e ((k : ℂ)⁻¹ • G (Q x)) = e ((k : ℂ)⁻¹ • Q (w x)) := by
      rw [← map_smul, hG, hw k x hk]
    have e2 := he.1 ((k : ℂ)⁻¹ • (G (Q x) - Q (w x))) ((k : ℂ)⁻¹ • Q (w x))
    rw [← smul_add, sub_add_cancel, e1] at e2
    exact mul_eq_right.1 e2.symm
  have hFQ := hlift F f u hF hu
  have hFQ' := hlift F' f' u' hF' hu'
  have hvF : ∀ z, v.ex (F z) = v.ex z ≫ f := fun z => by rw [hve, hve]; exact hF z
  have hvF' : ∀ z, v.ex (F' z) = v.ex z ≫ f' := fun z => by rw [hve, hve]; exact hF' z
  have hisoL := _root_.GlobalTheory.LamPull.lbIso_pull_lift A P M hP hM hPM (A ⊗ A) (fst A A ≫ f) (snd A A)
  have hisoR := _root_.GlobalTheory.LamPull.lbIso_pull_lift A P M hP hM hPM (A ⊗ A) (fst A A) (snd A A ≫ f')
  have hcl : ∀ (a b : A ⊗ A ⟶ A), (cubeLB A ![a, b] M).IsLB := fun a b => LB.isLB_linComb hM _ _
  have key : LBIso (P.pull (lift (fst A A ≫ f) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ f')).left) ↔
      LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
    constructor
    · intro h
      exact LBIso.trans (hcl _ _) (pull_isLB hP _) (hcl _ _) hisoL.symm
        (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (hcl _ _) h hisoR)
    · intro h
      exact LBIso.trans (pull_isLB hP _) (hcl _ _) (pull_isLB hP _) hisoL
        (LBIso.trans (hcl _ _) (hcl _ _) (pull_isLB hP _) h hisoR.symm)
  rw [key]
  constructor
  · intro h x y
    have := _root_.GlobalTheory.AdjFwd.adjoint_hermForm_of_lbIso A g hA hg _ hN hamp M v Hm χ hM hAH f f' F F' hf hf' hvF hvF' h (Q x) (Q y)
    have hh : ((EF (u x) y : ℤ) : ℝ) = ((EF x (u' y) : ℤ) : ℝ) := by
      rw [hEF, hEF, ← hFQ, ← hFQ', this]
    exact_mod_cast hh
  · intro h
    apply GlobalTheory.T.cubeLineBundle_iso_of_appellHumbert_adjoint A g hA hg _ hN hamp M v Hm χ hM hAH f f' F F' hf hf' hvF hvF'
    refine GlobalTheory.HermAdjoint.adjoint_of_im Hm F F' _ v.full fun a ha b hb => ?_
    obtain ⟨x, rfl⟩ := (hmem a).1 ha
    obtain ⟨y, rfl⟩ := (hmem b).1 hb
    have h1 := hEF (u x) y
    have h2 := hEF x (u' y)
    have h3 : ((EF (u x) y : ℤ) : ℝ) = ((EF x (u' y) : ℤ) : ℝ) := by rw [h x y]
    rw [hFQ, hFQ']
    linarith

end GlobalTheory.RosatiFormAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPowerValueChartChangeByTransitionPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecValLC

theorem valR_def' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := by
  unfold valR; rw [dite_eq_left h]

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_def' x U h, map_mul]

theorem valR_map' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE e).op).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_def' x V h, valR_def' x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]

theorem valR_id_app {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ U)) (f : Γ(X, U)) :
    valR x ((𝟙 X) ⁻¹ᵁ U) ((Scheme.Hom.app (𝟙 X) U).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h
  rw [valR_def' x _ h, valR_def' x U hU]
  congr 1

theorem valR_pow' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (n : ℕ) :
    valR x U (f ^ n) = valR x U f ^ n := by
  simp only [valR_def' x U h, map_pow]

theorem secM_valR_transition : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → valR ξ _ (σ.f fun _ => j) = valR ξ (L.U j ⊓ L.U j') (L.g j j').val ^ k * valR ξ _ (σ.f fun _ => j') := by
  intro X L k σ F _ ξ j j' hj hj'
  set LC := LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k:ℤ)) with hLC
  have hW : ∀ i : L.ι, L.U i ≤ LC.U (fun _ => i) :=
    fun i x hx => Set.mem_iInter.2 fun _ => hx
  have h1 : ⊤ ≤ ξ ⁻¹ᵁ (LC.U (fun _ => j) ⊓ LC.U (fun _ => j')) := by
    intro x hx
    exact ⟨hW j (hj hx), hW j' (hj' hx)⟩
  have h2 : ⊤ ≤ ξ ⁻¹ᵁ ((𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j')) := fun x hx => ⟨hj hx, hj' hx⟩
  have hle : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ (𝟙 X) ⁻¹ᵁ (L.U j ⊓ L.U j') :=
    le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
  have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
      Γ(X, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) =
      (X.presheaf.map (homOfLE hle).op).hom ((Scheme.Hom.app (𝟙 X) (L.U j ⊓ L.U j')).hom
        (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) ^ k := by
    show Units.val (∏ _i : Fin 1, (res _ (pullU (𝟙 X) _ (L.g j j'))) ^ (k:ℤ)) = _
    rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  have hc := σ.compat (fun _ => j) (fun _ => j')
  have := congrArg (valR ξ _) hc
  rw [valR_map' _ _ h1, valR_mul' _ _ h1, valR_map' _ _ h1] at this
  rw [this, hg, valR_pow' _ _ h1, valR_map' _ _ h1, valR_id_app _ _ h2]

end GlobalTheory.SecValLC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDescendAlongFlatMapToLocalDomain
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LocRegDesc

theorem exists_unit_mul_eq_of_flat {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R]
    (ρ : A →+* R) (hρ : ρ.Flat) (s b : A) (r : R) (hs : ρ s = ρ b * r) :
    ∃ g a : A, IsUnit (ρ g) ∧ g * s = b * a := by
  letI := ρ.toAlgebra
  haveI : Module.Flat A R := hρ
  have hrel : ∑ i, (![s, -b] : Fin 2 → A) i • (![1, r] : Fin 2 → R) i = 0 := by
    simp [Fin.sum_univ_two, Algebra.smul_def, RingHom.algebraMap_toAlgebra, hs]
  have ht : Module.IsTrivialRelation (![s, -b] : Fin 2 → A) (![1, r] : Fin 2 → R) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, a, y, hx, hf⟩ := ht
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (ρ (a 0 j)) := by
    by_contra hne
    push_neg at hne
    have h1 : (1 : R) ∈ maximalIdeal R := by
      have := hx 0
      simp only [Matrix.cons_val_zero] at this
      rw [this]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      exact Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).2 (hne j))
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨a 0 j, a 1 j, hj, ?_⟩
  have := hf j
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  linear_combination this

end LocRegDesc

namespace LocRegDesc

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill_on_basicOpen (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0)
    (f : Γ(X, U.1)) (hf : X.basicOpen f ≤ W) :
    ∃ g, IsUnit (ρ g) ∧
      (X.presheaf.map (homOfLE hf).op).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0 := by
  haveI hloc := U.2.isLocalization_basicOpen f
  set δV := (X.presheaf.map (homOfLE hf).op).hom δ with hδV
  set hV := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom h with hhV
  have key : X.basicOpen hV = X.basicOpen f ⊓ X.basicOpen h := Scheme.basicOpen_res _ _ _
  have hB : X.basicOpen hV ≤ X.basicOpen h := key ▸ inf_le_right
  have hzero : (X.presheaf.map (homOfLE (X.basicOpen_le hV)).op).hom δV = 0 := by
    rw [hδV, res_res, ← res_res hh hB, hδ, map_zero]
  obtain ⟨n, hn⟩ :=
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X (U.2.basicOpen f).isCompact δV hV hzero
  obtain ⟨⟨e, m⟩, hem⟩ := IsLocalization.surj (Submonoid.powers f) δV
  simp only at hem
  have h0 : algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (h ^ n * e) = 0 := by
    rw [map_mul, ← hem, map_pow]
    change hV ^ n * (δV * _) = 0
    rw [← _root_.mul_assoc, hn, zero_mul]
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).1 h0
  simp only at hj
  have hc : ρ (f ^ j * e) = 0 := by
    have : ρ h ^ n * ρ (f ^ j * e) = 0 := by
      rw [← map_pow, ← map_mul, show h ^ n * (f ^ j * e) = f ^ j * (h ^ n * e) by ring, hj, map_zero]
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hρh)
  obtain ⟨g, a, hu, hg⟩ := exists_unit_mul_eq_of_flat ρ hρ (f ^ j * e) 0 0 (by simp [hc])
  refine ⟨g, hu, ?_⟩
  rw [map_mul, res_res]
  change algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) g * δV = 0
  have u1 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (m : Γ(X, U.1))) :=
    IsLocalization.map_units _ m
  have u2 : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) (f ^ j)) :=
    IsLocalization.map_units _ (⟨f ^ j, j, rfl⟩ : Submonoid.powers f)
  rw [← u1.mul_left_eq_zero, ← u2.mul_left_eq_zero, _root_.mul_assoc _ δV, hem, ← map_mul, ← map_mul,
    show g * e * f ^ j = g * (f ^ j * e) by ring, hg, zero_mul, map_zero]

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_kill (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (δ : Γ(X, W)) (hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0) :
    ∃ g, IsUnit (ρ g) ∧ (X.presheaf.map (homOfLE hWU).op).hom g * δ = 0 := by
  let p : Set X → Prop := fun t => ∃ g, IsUnit (ρ g) ∧ ∀ y (hy : y ∈ W), y ∈ t →
    (X.presheaf.germ W y hy).hom ((X.presheaf.map (homOfLE hWU).op).hom g * δ) = 0
  have hp : p (W : Set X) := by
    refine hW.induction_on ?_ ?_ ?_ ?_
    · exact ⟨1, by simp, fun y _ hy => hy.elim⟩
    · rintro s t hst ⟨g, hg, H⟩
      exact ⟨g, hg, fun y hy hs => H y hy (hst hs)⟩
    · rintro s t ⟨g₁, hg₁, H₁⟩ ⟨g₂, hg₂, H₂⟩
      refine ⟨g₁ * g₂, by rw [map_mul]; exact hg₁.mul hg₂, fun y hy hyst => ?_⟩
      rw [map_mul (X.presheaf.map (homOfLE hWU).op).hom g₁ g₂]
      rcases hyst with hs | ht
      · rw [mul_right_comm, map_mul (X.presheaf.germ W y hy).hom, H₁ y hy hs, zero_mul]
      · rw [_root_.mul_assoc, map_mul (X.presheaf.germ W y hy).hom, H₂ y hy ht, mul_zero]
    · intro x hx
      obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (hWU hx)
      obtain ⟨g, hg, H⟩ := exists_unit_kill_on_basicOpen X U W hWU R ρ hρ h hh hρh δ hδ f hf
      refine ⟨X.basicOpen f, mem_nhdsWithin_of_mem_nhds ((X.basicOpen f).isOpen.mem_nhds hxf),
        g, hg, fun y hy hyf => ?_⟩
      rw [← X.presheaf.germ_res_apply (homOfLE hf) y hyf, H, map_zero]
  obtain ⟨g, hg, H⟩ := hp
  refine ⟨g, hg, ?_⟩
  refine TopCat.Presheaf.section_ext X.sheaf W _ 0 fun y hy => ?_
  exact (H y hy hy).trans (map_zero (X.presheaf.germ W y hy).hom).symm

end LocRegDesc

namespace LocRegDesc

theorem exists_unit_one (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens)
    (hWU : W ≤ U.1) (hW : IsCompact (W : Set X)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ρ : Γ(X, U.1) →+* R) (hρ : ρ.Flat) (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W) (hρh : ρ h ≠ 0)
    (θ : Γ(X, W))
    (H : ∀ (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s =
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) *
        (X.presheaf.map (homOfLE hh).op).hom θ → ρ h ^ N ∣ ρ s) :
    ∃ g, IsUnit (ρ g) ∧ ∃ s : Γ(X, U.1),
      (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ := by
  haveI hloc := U.2.isLocalization_basicOpen h
  obtain ⟨⟨s, ⟨_, N, rfl⟩⟩, hsm⟩ :=
    IsLocalization.surj (Submonoid.powers h) ((X.presheaf.map (homOfLE hh).op).hom θ)
  simp only at hsm
  obtain ⟨r, hr⟩ := H s N (by
    change algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) s =
      algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) * _
    rw [← hsm, mul_comm])
  obtain ⟨g₁, a, hu₁, hga⟩ := exists_unit_mul_eq_of_flat ρ hρ s (h ^ N) r (by rw [map_pow, hr])
  set δ := (X.presheaf.map (homOfLE hWU).op).hom a - (X.presheaf.map (homOfLE hWU).op).hom g₁ * θ
    with hδdef
  have hδ : (X.presheaf.map (homOfLE hh).op).hom δ = 0 := by
    have u : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N)) :=
      IsLocalization.map_units _ (⟨h ^ N, N, rfl⟩ : Submonoid.powers h)
    rw [← u.mul_left_eq_zero, hδdef, map_sub, map_mul, res_res, res_res]
    change (algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) a - algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) g₁ *
      (X.presheaf.map (homOfLE hh).op).hom θ) * algebraMap Γ(X, U.1) Γ(X, X.basicOpen h) (h ^ N) = 0
    rw [sub_mul, _root_.mul_assoc, hsm, ← map_mul, ← map_mul, hga, mul_comm a, sub_self]
  obtain ⟨g₂, hu₂, hk⟩ := exists_unit_kill X U W hWU hW R ρ hρ h hh hρh δ hδ
  refine ⟨g₂ * g₁, by rw [map_mul]; exact hu₂.mul hu₁, g₂ * a, ?_⟩
  rw [map_mul, map_mul]
  rw [hδdef] at hk
  linear_combination hk

end LocRegDesc

theorem LocRegDesc.descent : ∀ (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens) (hWU : W ≤ U.1), IsCompact (W : Set X) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ρ : Γ(X, U.1) →+* R), ρ.Flat → ∀ mm : Ideal Γ(X, U.1), (maximalIdeal R).comap ρ = mm → ∀ (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W), ρ h ≠ 0 → ∀ (J : Type) [Finite J] (θ : J → Γ(X, W)), (∀ i (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s = (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) * (X.presheaf.map (homOfLE hh).op).hom (θ i) → ρ h ^ N ∣ ρ s) → ∃ g ∉ mm, ∀ i, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ i := by
  intro X U W hWU hW R _ _ _ ρ hρ mm hmm h hh hρh J _ θ H
  choose g hg s hs using fun i => LocRegDesc.exists_unit_one X U W hWU hW R ρ hρ h hh hρh (θ i) (H i)
  haveI := Fintype.ofFinite J
  classical
  refine ⟨∏ i, g i, ?_, fun i => ⟨s i * ∏ j ∈ Finset.univ.erase i, g j, ?_⟩⟩
  · rw [← hmm, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun i _ => hg i)
  · rw [map_mul, hs i, ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i), map_mul]
    ring

end GlobalTheory
end

