module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.EllComp

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem lbIso_pull_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X} (h : LBIso (L.pull φ) L')
    (ψ : X'' ⟶ X') : LBIso (L.pull (ψ ≫ φ)) (L'.pull ψ) :=
  LBIso.chartPull (chartPullSame L _ _ _ ψ fun _ => rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' ψ ψ rfl) h

theorem dualMapR_comp (f : R →+* R') (g : R' →+* R'') :
    spMap (Chart.dualMapR g) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR (g.comp f)) := by
  refine (spMap_comp_spMap _ _).trans ?_
  congr 1
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem isPolFibre_comp {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')}
    {P'' : Out.PolAV (Sp R'')} {φ : P'.A.left ⟶ P.A.left} {ψ : P''.A.left ⟶ P'.A.left}
    (h : IsPolFibre f P P' φ) (h' : IsPolFibre g P' P'' ψ) : IsPolFibre (g.comp f) P P'' (ψ ≫ φ) :=
  ⟨h'.1.trans h.1, (h'.2.1.comp h.2.1).congr (spMap_comp_spMap _ _) rfl,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB P'.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ) h'.2.2⟩

theorem isVecOver_comp {f : R →+* R'} {g : R' →+* R''} {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')}
    {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''}
    (h : IsVecOver f φ v v') (h' : IsVecOver g ψ v' v'') : IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  unfold IsVecOver at *
  rw [← Category.assoc, h', Category.assoc, h, ← Category.assoc]
  exact congrArg (· ≫ v.left) (dualMapR_comp f g)

theorem exists_isPolFibre_lift {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')}
    {P'' : Out.PolAV (Sp R'')} {φ : P'.A.left ⟶ P.A.left} {χ : P''.A.left ⟶ P.A.left}
    (h : IsPolFibre f P P' φ) (n : IsPolFibre (g.comp f) P P'' χ) :
    ∃ ψ : P''.A.left ⟶ P'.A.left, ψ ≫ φ = χ ∧ IsPolFibre g P' P'' ψ := by
  have n' : IsGrpPullback P''.A P.A (spMap g ≫ spMap f) χ := n.2.1.congr (spMap_comp_spMap _ _).symm rfl
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ spMap g) ≫ spMap f := n'.1.w.trans (Category.assoc _ _ _).symm
  have e : h.2.1.1.lift _ _ w ≫ φ = χ := h.2.1.1.lift_fst _ _ w
  refine ⟨h.2.1.1.lift _ _ w, e, n.1.trans h.1.symm,
    h.2.1.cancel (n'.congr rfl e.symm) (h.2.1.1.lift_snd _ _ w), ?_⟩
  refine LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) P''.isLB (lbIso_pull_comp h.2.2 _).symm ?_
  rw [e]
  exact n.2.2

theorem isVecOver_cancel {f : R →+* R'} {g : R' →+* R''} {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')}
    {φ : A'.left ⟶ A.left} {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'} {v'' : epsR R'' ⟶ A''}
    (hφ : IsPullback φ A'.hom A.hom (spMap f)) (hψ : IsPullback ψ A''.hom A'.hom (spMap g))
    (h : IsVecOver f φ v v') (n : IsVecOver (g.comp f) (ψ ≫ φ) v v'') : IsVecOver g ψ v' v'' := by
  obtain ⟨w, hw, -⟩ := existsUnique_isVecOver hψ v'
  have hp : IsPullback (ψ ≫ φ) A''.hom A.hom (spMap (g.comp f)) := by
    rw [← spMap_comp_spMap]
    exact hψ.paste_horiz hφ
  rw [(existsUnique_isVecOver hp v).unique n (isVecOver_comp h hw)]
  exact hw

theorem isLieNormSq_iff {f : R →+* R'} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {φ : P'.A.left ⟶ P.A.left}
    {v : epsR R ⟶ P.A} {v' : epsR R' ⟶ P'.A} (h : IsPolFibre f P P' φ) (hv : IsVecOver f φ v v') (σ : R' →+* ℂ)
    (r : ℝ) : IsLieNormSq P' v' σ r ↔ IsLieNormSq P v (σ.comp f) r := by
  constructor
  · rintro ⟨Q, ψ, w, u, Hm, χ, z, h₁, h₂, h₃⟩
    exact ⟨Q, ψ ≫ φ, w, u, Hm, χ, z, isPolFibre_comp h h₁, isVecOver_comp hv h₂, h₃⟩
  · rintro ⟨Q, ψ₀, w, u, Hm, χ, z, h₁, h₂, h₃⟩
    obtain ⟨ψ, rfl, hψ⟩ := exists_isPolFibre_lift h h₁
    exact ⟨Q, ψ, w, u, Hm, χ, z, hψ, isVecOver_cancel h.2.1.1 hψ.2.1.1 hv h₂, h₃⟩

theorem ellMap_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → (∀ (R'' : Type) [CommRing R''] (ω'' : R'') (C'' : Ell H R'' ω'') (f' : R' →+* R'') (φ' : C''.P.A.left ⟶ C'.P.A.left), EllMap C'' C' f' φ' → EllMap C'' C (f'.comp f) (φ' ≫ φ)) ∧ (∀ σ : R' →+* ℂ, C.IsPrincipalAt (σ.comp f) → C'.IsPrincipalAt σ) ∧ ∀ (σ : R' →+* ℂ) (r : ℝ), Out.PolBaseChangeSt → (IsLieNormSq C'.P C'.v σ r ↔ IsLieNormSq C.P C.v (σ.comp f) r) := by
  intro E _ _ _ H R _ ω C R' _ ω' C' f φ h
  refine ⟨fun R'' _ ω'' C'' f' φ' h' => ⟨?_, isPolFibre_comp h.2.1 h'.2.1, isVecOver_comp h.2.2.1 h'.2.2.1, fun a => ?_⟩,
    fun σ hC Q ψ hψ => hC Q (ψ ≫ φ) (isPolFibre_comp h.2.1 hψ), fun σ r _ => isLieNormSq_iff h.2.1 h.2.2.1 σ r⟩
  · rw [RingHom.comp_apply, h.1, h'.1]
  · rw [← Category.assoc, h'.2.2.2 a, Category.assoc, h.2.2.2 a, Category.assoc]

end GlobalTheory.CM.EllComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveLieCharacterOfAdjoinGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieChar

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

theorem isLieComb_one_iff (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨![w], fun i => by fin_cases i; exact h, by simp⟩

theorem isLieComb_comp {c : R} {v w : epsR R ⟶ G} (h : IsLieComb ![c] ![v] w) (f : G ⟶ G') :
    IsLieComb ![c] ![v ≫ f] (w ≫ f) := by
  rw [isLieComb_one_iff] at h ⊢
  simp [h]

theorem isTangent_comp {v : epsR R ⟶ G} (h : IsTangent v) (f : G ⟶ G') [IsMonHom f] :
    IsTangent (v ≫ f) := by
  unfold IsTangent at h ⊢
  rw [Over.comp_left, ← Category.assoc, h, ← Over.comp_left, IsMonHom.one_hom]

theorem spMap_epsScaleR_one : spMap (epsScaleR (1 : R)) = 𝟙 _ := by
  have : epsScaleR (1 : R) = RingHom.id _ := by
    ext x <;> simp [epsScaleR]
  rw [this]
  exact Spec.map_id _

theorem isLieComb_mul (x y : epsR R ⟶ G) : IsLieComb ![(1 : R), 1] ![x, y] (x * y) :=
  ⟨![x, y], fun i => by fin_cases i <;> simp [spMap_epsScaleR_one], by simp⟩

theorem exists_char [IsCommMonObj G] {O : Type} [CommRing O] (act : OAct O G) {v : epsR R ⟶ G}
    (hv : IsLieBasis ![v]) :
    ∃ τ : O →+* R, (∀ c, IsLieComb ![τ c] ![v] (v ≫ act.act c)) ∧
      ∀ c r, IsLieComb ![r] ![v] (v ≫ act.act c) → τ c = r := by
  have ht : ∀ c, IsTangent (v ≫ act.act c) := fun c => by
    haveI := act.hom c
    exact isTangent_comp (hv.1 0) _
  have e1 : ∀ d : Fin 1 → R, d = ![d 0] := fun d => by
    funext i; fin_cases i; rfl
  choose d hd hu using fun c => hv.2 _ (ht c)
  have hτ : ∀ c, IsLieComb ![d c 0] ![v] (v ≫ act.act c) := fun c => by
    rw [← e1]; exact hd c
  have huq : ∀ c r, IsLieComb ![r] ![v] (v ≫ act.act c) → d c 0 = r := fun c r h => by
    rw [← hu c _ h]; rfl
  obtain ⟨-, -, hcomp, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra R G 1 ![v] hv.1
  have hone : d 1 0 = 1 := huq _ _ (by
    rw [isLieComb_one_iff, act.one, spMap_epsScaleR_one]; simp)
  have hmul : ∀ a b, d (a * b) 0 = d a 0 * d b 0 := fun a b => huq _ _ (by
    have := hcomp 1 ![![d b 0]] ![v ≫ act.act b] ![d a 0] _
      (fun i => by fin_cases i; exact hτ b) (isLieComb_comp (hτ a) (act.act b))
    rw [act.mul, ← Category.assoc]
    convert this using 1
    funext i; fin_cases i; simp)
  have hadd : ∀ a b, d (a + b) 0 = d a 0 + d b 0 := fun a b => huq _ _ (by
    have := hcomp 2 ![![d a 0], ![d b 0]] ![v ≫ act.act a, v ≫ act.act b] ![1, 1] _
      (fun i => by
        fin_cases i
        · exact hτ a
        · exact hτ b) (isLieComb_mul _ _)
    rw [act.add, MonObj.comp_mul]
    convert this using 1
    funext i; fin_cases i; simp)
  exact ⟨RingHom.mk' ⟨⟨fun c => d c 0, hone⟩, hmul⟩ hadd, hτ, huq⟩

theorem ell_char : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R)
    (C : Ell H R ω), ∃ τ₀ : OK H →+* R, τ₀ (wK H) = ω ∧ ∀ c, IsLieComb ![τ₀ c] ![C.v] (C.v ≫ C.act.act c) := by
  intro E _ _ _ H R _ ω C
  obtain ⟨τ, h, hu⟩ := exists_char C.act C.basis
  exact ⟨τ, hu _ _ C.eig, h⟩

end GlobalTheory.CM.LieChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmLieStatementsIffLibrary
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LamF

theorem pnsmulPt_eq_frozen {S : Scheme.{0}} {G : Over S} [GrpObj G] {T : Over S} (n : ℕ) (x : T ⟶ G) :
    pnsmulPt n x = Formalism.L2.Pj.abelian₂.pnsmulPt n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pnsmulPt, Formalism.L2.Pj.abelian₂.pnsmulPt, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
  {c : Coeff l} {nΨ n' : ℕ}

@[reducible] def LamObj.toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.LamObj c nΨ n' where
  K₁ := o.K₁
  B := o.B
  oa := o.oa
  AΨ := o.AΨ
  oaΨ := o.oaΨ
  A' := o.A'
  oa' := o.oa'
  φΨ := o.φΨ
  φ' := o.φ'
  hΨ := o.hΨ
  h' := o.h'
  xB := o.xB
  xΨ := o.xΨ
  x' := o.x'
  φB := o.φB
  φΨg := o.φΨg
  φ'g := o.φ'g
  τΨ := o.τΨ
  τ' := o.τ'
  ℓΨ := o.ℓΨ
  ℓ' := o.ℓ'
  Tl := o.Tl
  LamL := o.LamL

@[reducible] def LamObj.ofFrozen (o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n') : LamObj c nΨ n' where
  K₁ := o.K₁
  B := o.B
  oa := o.oa
  AΨ := o.AΨ
  oaΨ := o.oaΨ
  A' := o.A'
  oa' := o.oa'
  φΨ := o.φΨ
  φ' := o.φ'
  hΨ := o.hΨ
  h' := o.h'
  xB := o.xB
  xΨ := o.xΨ
  x' := o.x'
  φB := o.φB
  φΨg := o.φΨg
  φ'g := o.φ'g
  τΨ := o.τΨ
  τ' := o.τ'
  ℓΨ := o.ℓΨ
  ℓ' := o.ℓ'
  Tl := o.Tl
  LamL := o.LamL

theorem rosatiConj_iff_frozen {K : Type} [Field K] [NumberField K] (A : PolAV (Sp (𝓞 K))) (oa : A.OAct (𝓞 E)) :
    RosatiConj A oa ↔ Formalism.L2.Pj.abelian₂.RosatiConj A oa := by
  simp only [RosatiConj, Formalism.L2.Pj.abelian₂.RosatiConj, pnsmulPt_eq_frozen]

theorem isIsogSum_toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.IsIsogSum o.toFrozen ↔ IsIsogSum o := by
  simp only [IsIsogSum, Formalism.L2.Pj.abelian₂.IsIsogSum, pnsmulPt_eq_frozen]
  rfl

theorem polClause_toFrozen (o : LamObj c nΨ n') : Formalism.L2.Pj.abelian₂.PolClause o.toFrozen ↔ PolClause o := by
  simp only [PolClause, Formalism.L2.Pj.abelian₂.PolClause, pnsmulPt_eq_frozen]

theorem fixed_of_lambdaBundle_objectCondition (o : LamObj c nΨ n') (f : ℕ) (La : ℝ) :
    Formalism.L2.Pj.abelian₂.LamObjGood o.toFrozen f La ↔ LamObjGood o f La := by
  unfold LamObjGood Formalism.L2.Pj.abelian₂.LamObjGood
  rw [isIsogSum_toFrozen, polClause_toFrozen, rosatiConj_iff_frozen, rosatiConj_iff_frozen, rosatiConj_iff_frozen]
  rfl

theorem lambdaBundle_objectCondition_of_fixed (o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n') (f : ℕ) (La : ℝ) :
    LamObjGood (LamObj.ofFrozen o) f La ↔ Formalism.L2.Pj.abelian₂.LamObjGood o f La :=
  (fixed_of_lambdaBundle_objectCondition (LamObj.ofFrozen o) f La).symm

@[reducible] def LamLetters.toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) : Formalism.L2.Pj.abelian₂.LamLetters o.toFrozen where
  m := L.m
  e := L.e
  src := L.src
  U := L.U
  ℓ := L.ℓ

@[reducible] def LamLetters.ofFrozen {o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n'} (L : Formalism.L2.Pj.abelian₂.LamLetters o) :
    LamLetters (LamObj.ofFrozen o) where
  m := L.m
  e := L.e
  src := L.src
  U := L.U
  ℓ := L.ℓ

theorem LamLetters.isLetter_toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) (k : Fin o.xB.P.g)
    (w : epsR o.K₁ ⟶ o.xB.P.A) : L.toFrozen.IsLetter k w ↔ L.IsLetter k w := by
  unfold LamLetters.IsLetter Formalism.L2.Pj.abelian₂.LamLetters.IsLetter
  dsimp only
  cases L.src k <;> rfl

theorem LamLetters.isGood_toFrozen {o : LamObj c nΨ n'} (L : LamLetters o) : L.toFrozen.IsGood ↔ L.IsGood := by
  unfold LamLetters.IsGood Formalism.L2.Pj.abelian₂.LamLetters.IsGood
  refine and_congr Iff.rfl (and_congr (forall_congr' fun b => forall_congr' fun i => ?_)
    (and_congr (forall_congr' fun k => exists_congr fun w => and_congr (L.isLetter_toFrozen k w) Iff.rfl)
      (forall_congr' fun k => ?_)))
  · dsimp only
    cases L.src (L.e ⟨b, i⟩) <;> rfl
  · dsimp only
    cases L.src k <;> rfl

theorem LamLetters.isGood_ofFrozen {o : Formalism.L2.Pj.abelian₂.LamObj c nΨ n'} (L : Formalism.L2.Pj.abelian₂.LamLetters o) :
    (LamLetters.ofFrozen L).IsGood ↔ L.IsGood :=
  (LamLetters.isGood_toFrozen (LamLetters.ofFrozen L)).symm

omit [StarRing (𝓞 E)] in
theorem lambdaBundle_degree_iff (H : Host E) (x : ℝ) : LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x :=
  ⟨fun h _ l c hs nΨ n' f o La ho => h l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho),
   fun h _ l c hs nΨ n' f o La ho => h l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho)⟩

theorem lambdaBundle_index_iff : LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt :=
  ⟨fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho) (LamLetters.ofFrozen L)
        ((LamLetters.isGood_ofFrozen L).2 hL),
   fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho) L.toFrozen (L.isGood_toFrozen.2 hL)⟩

theorem lambdaBundle_length_iff : LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt :=
  ⟨fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f (LamObj.ofFrozen o) La ((lambdaBundle_objectCondition_of_fixed o f La).2 ho) (LamLetters.ofFrozen L)
        ((LamLetters.isGood_ofFrozen L).2 hL),
   fun h E _ _ _ _ H l c hs nΨ n' f o La ho L hL =>
      h E H l c hs nΨ n' f o.toFrozen La ((fixed_of_lambdaBundle_objectCondition o f La).2 ho) L.toFrozen (L.isGood_toFrozen.2 hL)⟩

theorem lambdaBundle_conditions_iff :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (x : ℝ),
      GlobalTheory.LamF.LamDegSt H x ↔ Formalism.L2.Pj.abelian₂.LamDegSt H x) ∧
    (GlobalTheory.LamF.LamIndSt ↔ Formalism.L2.Pj.abelian₂.LamIndSt) ∧ (GlobalTheory.LamF.LamLenSt ↔ Formalism.L2.Pj.abelian₂.LamLenSt) :=
  ⟨fun _ _ _ _ H x => lambdaBundle_degree_iff H x, lambdaBundle_index_iff, lambdaBundle_length_iff⟩

end GlobalTheory.LamF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.TenDim

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem exists_isLieBasis {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (h : SmoothOfRelativeDimension n G.hom) : ∃ v : Fin n → (epsR k ⟶ G), IsLieBasis v := by
  obtain ⟨x, hx⟩ := ObjDim.univChart_of_relativeDimension G h
  exact ⟨_, Chart.basis_of_chart (G := G) hx⟩

theorem dim_eq_field {k O M : Type} [Field k] [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] {G A : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M)
    (hG : SmoothOfRelativeDimension 1 G.hom) {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) :
    n = Module.finrank O M := by
  obtain ⟨v, hv⟩ := exists_isLieBasis G hG
  obtain ⟨w, hw⟩ := exists_isLieBasis A hA
  have h1 : Module.finrank k (Serre.Lie a) = 1 :=
    (Module.finrank_eq_card_basis (Serre.Lie.basis a hv)).trans (Fintype.card_fin 1)
  have hb : Function.Bijective (algebraMap k (Module.End k (Serre.Lie a))) := by
    have := Module.Finite.of_basis (Serre.Lie.basis a hv)
    rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap, Module.finrank_linearMap, h1]
  let e := RingEquiv.ofBijective _ hb
  let τ : O →+* k := e.symm.toRingHom.comp (Module.toModuleEnd k (Serre.Lie a))
  have hτ : Serre.Lie.eig a τ = ⊤ := eq_top_iff.2 fun u _ => Serre.Lie.mem_eig_iff.2 fun x =>
    (LinearMap.congr_fun (e.apply_symm_apply (Module.toModuleEnd k (Serre.Lie a) x)) u).symm
  letI : Algebra O k := τ.toAlgebra
  have e' := t.lieEquivScalar b (N := k)
    ((Serre.Lie.basis a hv).equivFun ≪≫ₗ LinearEquiv.funUnique (Fin 1) k k).symm hτ
  rw [← finrank_fibre O M k, e'.finrank_eq, Module.finrank_eq_card_basis (Serre.Lie.basis b hw),
    Fintype.card_fin]

theorem smoothOfRelativeDimension {S : Scheme.{0}} {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] {G A : Over S} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M)
    (hab : IsAbelianScheme G) (hG : SmoothOfRelativeDimension 1 G.hom) :
    SmoothOfRelativeDimension (Module.finrank O M) A.hom := by
  have hA : IsAbelianScheme A := t.isAbelianScheme hab
  have := hA.smooth
  have := hA.geomConnected
  choose n W hW hd using H1.exists_dim A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank O M)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (Module.finrank O M)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := A.left.residueField y
  let z : Sp k ⟶ A.left := A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ A.hom
  have : ConnectedSpace ↥(pullback A.hom x) :=
    GeometricallyConnected.geometrically_connectedSpace (f := A.hom) x _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd A.hom x) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hG' : SmoothOfRelativeDimension 1 (pullback.snd G.hom x) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG
  have hdim := dim_eq_field (t.pullback x) hG' hm
  have hdim' : n y = Module.finrank O M := e₁.trans hdim
  rw [← hdim']
  exact hd y

end GlobalTheory.CM.TenDim

namespace GlobalTheory.CM

theorem tensor_smoothOfRelativeDimension :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A), Nonempty (Serre.IsTensor A b C.P.A C.act D.La) → SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) A.hom := by
  rintro E _ _ _ H R _ ω C D A _ _ b ⟨t⟩
  obtain ⟨h1, h2, h3⟩ := (OK_isDedekindDomain_and_projective E H).2.2.2.2.2 D.La D.fin D.proj
  rw [← D.rank, ← h3]
  exact TenDim.smoothOfRelativeDimension t C.P.isAb (C.dim ▸ C.P.smoothDim)

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllMapCancelAndSabMapCancel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Factor

theorem dualMapR_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    Chart.dualMapR (f'.comp f) = (Chart.dualMapR f').comp (Chart.dualMapR f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

theorem ellMap_cancel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' R'' : Type} [CommRing R]
    [CommRing R'] [CommRing R''] {f : R →+* R'} {f' : R' →+* R''} {ω : R} {ω' : R'} {ω'' : R''} {C : Ell H R ω}
    {C' : Ell H R' ω'} {C'' : Ell H R'' ω''} {φ : C'.P.A.left ⟶ C.P.A.left} {ψ : C''.P.A.left ⟶ C.P.A.left}
    (h : EllMap C' C f φ) (k : EllMap C'' C (f'.comp f) ψ) :
    ∃ φ' : C''.P.A.left ⟶ C'.P.A.left, EllMap C'' C' f' φ' ∧ φ' ≫ φ = ψ := by
  obtain ⟨hω, ⟨hg, hp, hL⟩, hv, ha⟩ := h
  obtain ⟨kω, ⟨kg, kp, kL⟩, kv, ka⟩ := k
  rw [← spMap_comp_spMap] at kp
  have w : ψ ≫ C.P.A.hom = (C''.P.A.hom ≫ spMap f') ≫ spMap f := by rw [kp.1.w, Category.assoc]
  obtain ⟨l, h₁, h₂⟩ : ∃ l : C''.P.A.left ⟶ C'.P.A.left, l ≫ φ = ψ ∧ l ≫ C'.P.A.hom = C''.P.A.hom ≫ spMap f' :=
    ⟨hp.1.lift _ _ w, hp.1.lift_fst _ _ w, hp.1.lift_snd _ _ w⟩
  subst h₁
  refine ⟨l, ⟨hω ▸ kω, ⟨kg.trans hg.symm, hp.cancel kp h₂, ?_⟩, ?_, fun a => ?_⟩, rfl⟩
  · have e : LBIso (C.P.L.pull (l ≫ φ)) (C'.P.L.pull l) :=
      LBIso.chartPull (chartPullSame C.P.L _ _ _ l fun _ => rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull C'.P.L l l rfl) hL
    exact LBIso.trans (pull_isLB C'.P.isLB _) (pull_isLB C.P.isLB _) C''.P.isLB e.symm kL
  · unfold IsVecOver at hv kv ⊢
    apply hp.1.hom_ext
    · rw [Category.assoc, kv, Category.assoc, hv, dualMapR_comp, ← spMap_comp_spMap, Category.assoc]
    · rw [Category.assoc, h₂, ← Category.assoc, Over.w C''.v, Category.assoc, Over.w C'.v]
      refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
      congr 1
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · apply hp.1.hom_ext
    · rw [Category.assoc, ka, Category.assoc, Category.assoc, ha]
    · rw [Category.assoc, h₂, ← Category.assoc, Over.w, Category.assoc, Over.w, h₂]

theorem ellMap_cancel_and_sabMap_cancel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R''),
  (∀ (ω : R) (ω' : R') (ω'' : R'') (C : Ell H R ω) (C' : Ell H R' ω') (C'' : Ell H R'' ω'') (φ : C'.P.A.left ⟶ C.P.A.left) (ψ : C''.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → EllMap C'' C (f'.comp f) ψ → ∃ φ' : C''.P.A.left ⟶ C'.P.A.left, EllMap C'' C' f' φ' ∧ φ' ≫ φ = ψ) ∧
  ∀ (S : Scheme.{0}) (y : Sp R' ⟶ S) (y' : Sp R'' ⟶ S) (t : SAB H S) (t' : SAB H (Sp R')) (t'' : SAB H (Sp R'')) (m : SABMap t' t y) (n : SABMap t'' t y'), spMap f' ≫ y = y' → ∃ m' : SABMap t'' t' (spMap f'), m'.φ ≫ m.φ = n.φ := by
  intro E _ _ _ H R R' R'' _ _ _ f f'
  refine ⟨fun _ _ _ _ _ _ _ _ h k => ellMap_cancel h k, fun S y y' t t' t'' m n e => ?_⟩
  subst e
  obtain ⟨m', h⟩ := ObjMaps.exists_sab_cancel m n
  exact ⟨m', h.symm⟩

end GlobalTheory.CM.Factor
end
end

