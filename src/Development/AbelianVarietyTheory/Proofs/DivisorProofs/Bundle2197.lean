module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCotValEqTanVal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def sqToEps {M S : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [CommRing S] [Algebra R S] (k : M →ₗ[R] S) : TrivSqZeroExt R M →ₐ[R] DualNumber S where
  toFun z := (algebraMap R S z.fst, k z.snd)
  map_one' := TrivSqZeroExt.ext (map_one (algebraMap R S)) (map_zero k)
  map_mul' a b := TrivSqZeroExt.ext (map_mul (algebraMap R S) _ _) (by
    change k (a.fst • b.snd + MulOpposite.op b.fst • a.snd) =
      algebraMap R S a.fst * k b.snd + k a.snd * algebraMap R S b.fst
    rw [op_smul_eq_smul, map_add (f := _), map_smul, map_smul, Algebra.smul_def, Algebra.smul_def,
      mul_comm (k a.snd)])
  map_zero' := TrivSqZeroExt.ext (map_zero (algebraMap R S)) (map_zero k)
  map_add' a b := TrivSqZeroExt.ext (map_add (algebraMap R S) _ _) (map_add k _ _)
  commutes' _ := TrivSqZeroExt.ext rfl (map_zero k)

attribute [local instance] cotOp cotCentral cotTower

theorem tanDer_cotVal {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} (t : G.TorsionTower A)
    (β : Form (A.hom ≫ 𝟙 _)) {v : epsR R ⟶ A} (hv : IsTangent v) (n : ℕ) :
    t.tanDer hv n (cotVal β.1 (t.y n)) = algebraMap R (PDiv.ModPow p R n) (tanVal v β) := by
  let S := PDiv.ModPow p R n
  let E : SqExt R := SqExt.ofModule R S S
  let ρ : (cotExt R (G.A n)).C →ₐ[R] DualNumber S := sqToEps (t.tanDer hv n)
  let y' : Pt A (cotExt R (G.A n)).C := spOver (cotPt R (G.A n)) ≫ t.y n
  have hρ : ρ.comp (cotPt R (G.A n)) = t.tanPt hv n := AlgHom.ext fun a ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [t.fst_tanPt]
      exact congrArg (algebraMap R S) (add_zero _)
    · rw [← t.tanDer_d]
      exact congrArg (t.tanDer hv n) (zero_add _)
  have e : spOver ρ ≫ y' = epsRedPow p n v := by
    rw [← Category.assoc, spOver_comp, hρ, t.tanPt_y]
  have k1 := (cotExt R (G.A n)).val_map E ρ (Algebra.ofId R S) (fun _ ↦ rfl)
    (fun _ ↦ TrivSqZeroExt.ext rfl (map_zero (t.tanDer hv n))) y'.left y'.w _
    (Pt.w (epsRedPow p n v)) (congrArg Over.Hom.left e) β
  have k2 := (SqExt.dual R).val_map E (epsTo R S) (Algebra.ofId R S) (fun c ↦ (fst_epsTo S c).symm)
    (fun c ↦ TrivSqZeroExt.ext (fst_epsTo S _) ((snd_epsTo S _).trans (map_zero _))) v.left (pt_w v) _
    (Pt.w (epsRedPow p n v)) rfl β
  have h0 : fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n) = 0 := β.2 _ rfl rfl
  have k3 := congrArg TrivSqZeroExt.snd (k1.symm.trans k2)
  rw [snd_epsTo] at k3
  refine Eq.trans ?_ k3
  change t.tanDer hv n (cotSnd R _ (_ - fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n))) = _
  rw [h0, sub_zero]
  rfl

theorem lie_cotVal_eq_tanVal : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), IsNilpotent (p : R) → ∀ (β : Form (A.hom ≫ 𝟙 _)) (w : G.omega), (∀ n, w.1 n = cotVal β.1 (t.y n)) → ∀ (x : G.Lie) (v : epsR R ⟶ A), t.LieCorr x v → x w = tanVal v β := by
  intro R _ A _ p G t ⟨n, hn⟩ β w hw x v h
  have h1 := (t.lieCorr_iff h.1 x).1 h n w
  rw [hw, tanDer_cotVal] at h1
  have h2 := Ideal.Quotient.eq.1 h1
  rw [hn, Ideal.mem_span_singleton, zero_dvd_iff] at h2
  exact sub_eq_zero.1 h2

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyAtPointLambdaTrivial
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

theorem upa_mul {Y : Over (Sp V)} (x y : Y ⟶ bc A φ) : upa φ (x * y) = upa φ x * upa φ y := by
  have h := (isGrpPullback_pullback A (φ ≫ T.hom)).2 Y x y (upa φ x) (upa φ y) rfl rfl
  exact Over.OverMorphism.ext h.symm

theorem upa_one {Y : Over (Sp V)} : upa φ (1 : Y ⟶ bc A φ) = 1 := by
  have e := upa_mul φ (1 : Y ⟶ bc A φ) 1
  rw [_root_.mul_one] at e
  exact left_eq_mul.1 e

theorem pull_cls_twist {N : LB (A ⊗ T).left} (hN : N.IsLB) (h : (twist A φ N).IsLB) {Y : Over (Sp V)}
    (x : Y ⟶ bc A φ) : CechPic.pull x.left (cls _ h) = evc hN (upa φ x) (upt φ Y) := by
  let u : up φ Y ⟶ bcR A φ := Over.homMk x.left (by
    show x.left ≫ (bc A φ).hom ≫ φ ≫ T.hom = Y.hom ≫ φ ≫ T.hom
    rw [← Category.assoc, Over.w x])
  have ha : u ≫ pa A φ = upa φ x := Over.OverMorphism.ext rfl
  have ht : u ≫ pt A φ = upt φ Y := Over.OverMorphism.ext (by
    show x.left ≫ (bc A φ).hom ≫ φ = Y.hom ≫ φ
    rw [← Category.assoc, Over.w x])
  have e := pull_evc hN u (pa A φ) (pt A φ)
  rw [ha, ht] at e
  exact e


variable (A) in
theorem triv_lam_twist (N : LB (A ⊗ T).left) (hF : Fam A N) : Triv (abelian₂ (bc A φ) (twist A φ N)) := by
  have hO : (twist A φ N).IsLB := pull_isLB hF.isLB _
  have hP : (abelian₂ (bc A φ) (twist A φ N)).IsLB := LB.isLB_linComb hO _ _
  refine (cls_eq_zero_iff hP).1 ?_
  have e : cls _ hP = lam (G := bc A φ) (cls (X := (bc A φ).left) _ hO) (fst (bc A φ) (bc A φ)) (snd (bc A φ) (bc A φ)) := cls_cube_two (G := bc A φ) (L := twist A φ N) hO _ _ hP
  rw [e, lam, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO,
    pull_cls_twist φ hF.isLB hO, upa_mul, upa_one, (isAdditive_iff hF.isLB).1 hF.add, hF.add.evc_one hF.isLB]
  simp only [add_sub_cancel_left, sub_self, add_zero]

end GlobalTheory.TwistFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoExponentDivisorPullbackFlagCover
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlagLL

open GlobalTheory.FlagMod (FlagCover Frames ev)
open GlobalTheory.ShFam (EigFrame FlagCpt stalkPt genericPt constF)
open GlobalTheory.VarFlag GlobalTheory.VarFlagSpec
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

theorem spMap_alg_stalkPt {F : Type} [Field F] (Yv : GlobalTheory.ProjVar.Var F) (y : Yv.X) :
    spMap (algebraMap (Yv.X.presheaf.stalk y) Yv.X.functionField) ≫ stalkPt Yv y = genericPt Yv :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Yv.X).specializes trivial)

theorem mem_of_top_le {Xs Ys : Scheme.{0}} (x : Xs) (f : Xs ⟶ Ys) {V : Ys.Opens}
    (h : ⊤ ≤ (Xs.fromSpecStalk x ≫ f) ⁻¹ᵁ V) : f x ∈ V := by
  have h1 : f (Xs.fromSpecStalk x (IsLocalRing.closedPoint (Xs.presheaf.stalk x))) ∈ V := h trivial
  rwa [Scheme.fromSpecStalk_closedPoint] at h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Frames

variable {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_cast {R : Type} [CommRing R] {φ φ' : c.F →+* R} {x x' : Sp R ⟶ Z.X} (f : EigFrame Z φ x)
    (hφ : φ' = φ) (hx : x' = x) : ∃ f' : EigFrame Z φ' x', ∀ τ i, f'.v τ i = f.v τ i := by
  subst hφ hx
  exact ⟨f, fun _ _ => rfl⟩

theorem tri_cast {R R' : Type} [CommRing R] [CommRing R'] {φ : c.F →+* R} {φ' φ'' : c.F →+* R'} {x : Sp R ⟶ Z.X}
    {x' x'' : Sp R' ⟶ Z.X} {f : EigFrame Z φ x} {ψ : R →+* R'} {g : EigFrame Z φ' x'} {g' : EigFrame Z φ'' x''}
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R'ˣ} (h : f.Tri ψ g t) (hφ : φ'' = φ') (hx : x'' = x')
    (hv : ∀ τ i, g'.v τ i = g.v τ i) : f.Tri ψ g' t := by
  subst hφ hx
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun τ i => by rw [hv]; exact h3 τ i⟩

end Frames

variable {Y : Model Xo c (RingHom.id c.F)}

theorem co_chart {Zs : Scheme.{0}} {π : Zs ⟶ Y.X} (F : Frames Y π) {R : Type} [CommRing R] {φ : c.F →+* R}
    {x : Sp R ⟶ Y.X} (z z₁ z₂ : Sp R ⟶ Zs) (hx : x = z ≫ π) (h₁ : z₁ = z) (h₂ : z₂ = z) (k k' : F.J)
    (hk : ⊤ ≤ z₁ ⁻¹ᵁ F.U k) (hk' : ⊤ ≤ z₂ ⁻¹ᵁ F.U k') (hh : ⊤ ≤ z ⁻¹ᵁ (F.U k ⊓ F.U k')) {g g' : EigFrame Y φ x}
    (hg : ∀ σ i, g.v σ i = (tv (F.vecAt k z₁ hk rfl σ i)).left)
    (hg' : ∀ σ i, g'.v σ i = (tv (F.vecAt k' z₂ hk' rfl σ i)).left) (τ : E →+* ℂ) :
    g.co g' τ = (F.B k k' τ).map (ev z _ hh) := by
  subst hx
  subst h₁
  subst h₂
  exact EigFrame.co_eq fun i => by
    rw [funext (hg τ), hg' τ i, GlobalTheory.LieMet.isComb_iff]
    exact F.vecAt_eq_sum k k' _ hk hk' hh rfl τ i

theorem gen_frame (X : FlagCover Y) (C : FlagCpt Y (RingEquiv.refl c.F)) (g : C.Y.X ⟶ X.YY)
    (hg : g ≫ X.π = C.π ≫ GlobalTheory.Toroidal.genι Y) (hrel : Rel X.F C (genericPt C.Y ≫ g) (genericPt C.Y)) :
    ∃ (k₀ : X.F.J) (hk₀ : ⊤ ≤ (genericPt C.Y ≫ g) ⁻¹ᵁ X.F.U k₀)
      (G₀ : EigFrame Y (constF (RingEquiv.refl c.F) C.Y) (genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y))
      (t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ),
      (∀ σ i, G₀.v σ i = (tv (X.F.vecAt k₀ _ hk₀ rfl σ i)).left) ∧
      ∀ τ, (G₀.co C.f0 τ).BlockTriangular id ∧ ∀ i, G₀.co C.f0 τ i i = t₀ τ i := by
  obtain ⟨φ₀, k₀, hz₀, g₀, -, hfr, hcar⟩ := hrel
  have hx : (genericPt C.Y ≫ g) ≫ X.π = genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y := by
    rw [Category.assoc, hg]
  obtain ⟨g₁, hg₁⟩ := exists_cast g₀ (φ' := φ₀) rfl hx.symm
  have hcar₁ : C.Carries (genericPt C.Y) g₁ := by
    obtain ⟨y, ψ, φ₁, f, t, t', h1, h2, h3⟩ := hcar
    exact ⟨y, ψ, φ₁, f, t, t', h1, h2, tri_cast h3 rfl hx.symm hg₁⟩
  have hcf : C.Carries (genericPt C.Y) C.f0 := by
    obtain ⟨φy, fy, ty, hT, -⟩ := C.gr_spec (genericPoint C.Y.X)
    exact ⟨_, _, φy, fy, ty, ty, (spMap_alg_stalkPt C.Y _).symm, hT, hT⟩
  obtain ⟨t₀, ht₀⟩ := tri_of_carries C hcar₁ hcf
  obtain ⟨G₀, hG₀⟩ := g₁.exists_isMap (φ' := constF (RingEquiv.refl c.F) C.Y)
    (x' := genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y) (RingHom.id _) ht₀.2.1 ht₀.1
  refine ⟨k₀, hz₀, G₀, t₀, fun σ i => ?_, fun τ => ?_⟩
  · rw [hG₀ σ i, spMap_dualMap_id, Category.id_comp, hg₁ σ i]
    exact hfr σ i
  · obtain ⟨h1, h2⟩ := ht₀.co τ hG₀
    exact ⟨fun a i h => h1 a i h, h2⟩

theorem isEqn_chart (X : FlagCover Y) (C : FlagCpt Y (RingEquiv.refl c.F)) (g : C.Y.X ⟶ X.YY)
    (hg : g ≫ X.π = C.π ≫ GlobalTheory.Toroidal.genι Y) (hFE : FramesExist X) {k₀ : X.F.J}
    {hk₀ : ⊤ ≤ (genericPt C.Y ≫ g) ⁻¹ᵁ X.F.U k₀}
    {G₀ : EigFrame Y (constF (RingEquiv.refl c.F) C.Y) (genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y)}
    {t₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ}
    (hG₀v : ∀ σ i, G₀.v σ i = (tv (X.F.vecAt k₀ _ hk₀ rfl σ i)).left)
    (hG₀ : ∀ τ, (G₀.co C.f0 τ).BlockTriangular id ∧ ∀ i, G₀.co C.f0 τ i i = t₀ τ i) (k : X.F.J) (y : C.Y.X)
    (hy : g y ∈ X.F.U k) (hh : ⊤ ≤ (genericPt C.Y ≫ g) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k₀)) (τ : E →+* ℂ)
    (i : Fin (Dw.mult τ)) :
    (C.gr τ i).IsEqn y (X.F.TAt k k₀ (genericPt C.Y ≫ g) hh (some ⟨τ, i⟩) * t₀ τ i) := by
  classical
  set α := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField with hα_def
  have hα : Function.Injective α := IsFractionRing.injective _ _
  have hzy : ⊤ ≤ (stalkPt C.Y y ≫ g) ⁻¹ᵁ X.F.U k := GlobalTheory.ShFam.top_le_stalk_preimage y g hy
  obtain ⟨φy, fy, ty, hT, hE⟩ := C.gr_spec y
  have hgs : g ≫ X.π ≫ Y.s = C.π ≫ GlobalTheory.Toroidal.genι Y ≫ Y.s := by rw [← Category.assoc, hg, Category.assoc]
  have hs : (stalkPt C.Y y ≫ g) ≫ X.π ≫ Y.s = spMap φy := by
    rw [Category.assoc, hgs]
    exact flagSpaceComponent_stalkPoint_over_coefficientField C y hT
  obtain ⟨gy, hgy⟩ := hFE _ φy _ k hzy hs
  have hzα : spMap α ≫ (stalkPt C.Y y ≫ g) = genericPt C.Y ≫ g := by
    rw [← Category.assoc, spMap_alg_stalkPt]
  have hxy : stalkPt C.Y y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y = (stalkPt C.Y y ≫ g) ≫ X.π := by
    rw [Category.assoc, hg]
  have hx0 : genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y = spMap α ≫ ((stalkPt C.Y y ≫ g) ≫ X.π) := by
    rw [← hxy]
    exact hT.1
  obtain ⟨gF, hgF⟩ := gy.exists_isMap (φ' := constF (RingEquiv.refl c.F) C.Y)
    (x' := genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y) α hT.2.1 hx0
  obtain ⟨gF₂, hgF₂⟩ := gy.exists_isMap α (x' := (spMap α ≫ (stalkPt C.Y y ≫ g)) ≫ X.π) hT.2.1
    (Category.assoc _ _ _)
  have hF₂ := isFrameAt_map X.F hgy α hgF₂
  have hgFv : ∀ σ j, gF.v σ j = (tv (X.F.vecAt k (spMap α ≫ (stalkPt C.Y y ≫ g))
      (GlobalTheory.FlagMod.le_preimage_comp _ hzy) rfl σ j)).left := fun σ j => by
    rw [hgF σ j, ← hgF₂ σ j]
    exact hF₂ σ j
  have hB : gF.co G₀ τ = (X.F.B k k₀ τ).map (ev (genericPt C.Y ≫ g) _ hh) :=
    co_chart X.F (genericPt C.Y ≫ g) _ _ (by rw [Category.assoc, hg]) hzα rfl k k₀ _ hk₀ hh hgFv hG₀v τ
  obtain ⟨fF, hfF⟩ := fy.exists_isMap (φ' := constF (RingEquiv.refl c.F) C.Y)
    (x' := genericPt C.Y ≫ C.π ≫ GlobalTheory.Toroidal.genι Y) α hT.2.1 hT.1
  have hTf := hT.co τ hfF
  obtain ⟨gy', hgy'⟩ := exists_cast gy (φ' := φy) rfl hxy
  have hMap : gy'.IsMap α gF := fun σ j => by rw [hgF σ j, hgy' σ j]
  have hco : gF.co fF τ = (gy'.co fy τ).map α := hMap.co τ hfF hT.1
  set A := gF.co C.f0 τ with hA_def
  set T := fF.co C.f0 τ with hT_def
  set M := gy'.co fy τ with hM_def
  have hA : A = (X.F.B k k₀ τ).map (ev _ _ hh) * G₀.co C.f0 τ := by rw [← hB, EigFrame.co_mul]
  have hAt : A.BlockTriangular id := hA ▸ (X.F.B_map_tri k k₀ τ _).mul (hG₀ τ).1
  have hAd : A i i = ev _ _ hh (X.F.B k k₀ τ i i) * t₀ τ i := by
    rw [hA, GlobalTheory.FlagMod.tri_mul_diag (X.F.B_map_tri k k₀ τ _) (hG₀ τ).1, Matrix.map_apply, (hG₀ τ).2]
  have hTt : T.BlockTriangular id := fun a b h => hTf.1 a b h
  have hTT : T * C.f0.co fF τ = 1 := by rw [hT_def, EigFrame.co_mul, EigFrame.co_self]
  letI : Invertible T := Matrix.invertibleOfIsUnitDet T (Matrix.isUnit_det_of_right_inverse hTT)
  have hinv : C.f0.co fF τ = T⁻¹ := (Matrix.inv_eq_right_inv hTT).symm
  have hTi : (T⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hTt
  have hM' : M.map α = A * T⁻¹ := by rw [hM_def, ← hco, ← hinv, hA_def, EigFrame.co_mul]
  have hMt : M.BlockTriangular id := fun a b h => by
    have h1 := (hAt.mul hTi) h
    rw [← hM', Matrix.map_apply] at h1
    exact hα (h1.trans (map_zero α).symm)
  have hMu : IsUnit (M i i) := by
    have hdet := gy'.isUnit_det_co fy τ
    rw [← hM_def, Matrix.det_of_upperTriangular hMt] at hdet
    exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun j => M j j) (Finset.mem_univ i)) hdet
  have hTd : T i i * T⁻¹ i i = 1 := by
    rw [← GlobalTheory.FlagMod.tri_mul_diag hTt hTi, Matrix.mul_inv_of_invertible, Matrix.one_apply_eq]
  have hMd : α (M i i) = A i i * ((ty τ i : C.Y.Fnˣ) : C.Y.Fn)⁻¹ := by
    have e1 : α (M i i) = (A * T⁻¹) i i := by rw [← hM', Matrix.map_apply]
    rw [e1, GlobalTheory.FlagMod.tri_mul_diag hAt hTi]
    congr 1
    rw [← hTf.2 i]
    exact eq_inv_of_mul_eq_one_right hTd
  refine (hE τ i).iff_unitAt.2 ⟨M i i, hMu, ?_⟩
  rw [hMd, hAd, Units.val_mul, div_eq_mul_inv]
  rfl

theorem fnOf_pull_g {Xs Ys : Scheme.{0}} [IsIntegral Xs] (M : LB Ys) (f : Xs ⟶ Ys) (J J' : (M.pull f).ι)
    (hgen : genericPoint Xs ∈ (M.pull f).U J ⊓ (M.pull f).U J')
    (hh : ⊤ ≤ (Xs.fromSpecStalk (genericPoint Xs) ≫ f) ⁻¹ᵁ (M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit))) :
    GlobalTheory.Cartier.fnOf _ hgen ((M.pull f).g J J' : Γ(Xs, _)) =
      ev (Xs.fromSpecStalk (genericPoint Xs) ≫ f) _ hh (M.g (J PUnit.unit) (J' PUnit.unit)).val := by
  show GlobalTheory.Cartier.fnOf _ hgen (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, GlobalTheory.Cartier.fnOf_resG]
  have hg' : genericPoint Xs ∈ f ⁻¹ᵁ (M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit)) :=
    ⟨mem_pull.1 hgen.1, mem_pull.1 hgen.2⟩
  exact GlobalTheory.ShFam.fnOf_app_eq_ev f hg' hh _

end GlobalTheory.VarFlagLL


open GlobalTheory.VarFlagLL GlobalTheory.ShFam GlobalTheory.VarFlag in
theorem GlobalTheory.VarFlag.lbIso_LL_pull : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)) (g : C.Y.X ⟶ X.YY), g ≫ X.π = C.π ≫ GlobalTheory.Toroidal.genι Y → (∀ (K : Type) [Field K] (p : Sp K ⟶ C.Y.X), GlobalTheory.VarFlag.Rel X.F C (p ≫ g) p) → ∀ ex : Ix Dw → ℤ, ex none = 0 → LBIso (C.Y.lb (C.LEx ex)) ((X.LL ex).pull g) := by
  intro E _ _ _ H Dw l Xo c Y X C g hg hrel ex hex
  classical
  obtain ⟨k₀, hk₀, G₀, t₀, hG₀v, hG₀⟩ := gen_frame X C g hg (hrel _ (genericPt C.Y))
  have hFE := framesExist_flagCover X
  have hL : ((X.LL ex).pull g).IsLB := pull_isLB (X.F.isLB_LL ex) g
  let J₀ : ((X.LL ex).pull g).ι := fun _ => k₀
  have h₀ : genericPoint C.Y.X ∈ ((X.LL ex).pull g).U J₀ := mem_pull.2 (mem_of_top_le _ g hk₀)
  let cst : C.Y.Fnˣ := ∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t₀ x.1 x.2 ^ (-ex (some x))
  let r : ((X.LL ex).pull g).ι → C.Y.X.functionFieldˣ := fun J => GlobalTheory.Cartier.frameRat _ J₀ h₀ J * cst
  have hr : GlobalTheory.Cartier.IsRatSec ((X.LL ex).pull g) r := fun J J' h => by
    simp only [r, Units.val_mul]
    rw [GlobalTheory.Cartier.isRatSec_frameRat hL J₀ h₀ J J' h, mul_assoc]
  have heq : ∀ J, ∀ y ∈ ((X.LL ex).pull g).U J, (C.LEx ex).IsEqn y (r J) := by
    intro J y hy
    have hyk : g y ∈ X.F.U (J PUnit.unit) := mem_pull.1 hy
    have hgen : genericPoint C.Y.X ∈ ((X.LL ex).pull g).U J := GlobalTheory.Cartier.gen_mem hy
    have hh : ⊤ ≤ (genericPt C.Y ≫ g) ⁻¹ᵁ (X.F.U (J PUnit.unit) ⊓ X.F.U k₀) :=
      GlobalTheory.ShFam.top_le_stalk_preimage _ g ⟨mem_pull.1 hgen, mem_pull.1 h₀⟩
    have hx := fun x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) =>
      isEqn_chart X C g hg hFE hG₀v hG₀ (J PUnit.unit) y hyk hh x.1 x.2
    have h1 := (GlobalTheory.ShFam.isEqn_finset_sum Finset.univ
      (fun x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => ex (some x) • C.gr x.1 x.2) y _
      fun x => (hx x).zsmul (ex (some x))).neg
    have hval : r J = (∏ x ∈ Finset.univ, (X.F.TAt (J PUnit.unit) k₀ (genericPt C.Y ≫ g) hh (some x) *
        t₀ x.1 x.2) ^ ex (some x))⁻¹ := by
      apply Units.ext
      have e1 : (r J : C.Y.X.functionField) = (GlobalTheory.Cartier.frameRat _ J₀ h₀ J : C.Y.X.functionField) * cst :=
        Units.val_mul _ _
      rw [e1, GlobalTheory.Cartier.val_frameRat J₀ h₀ J hgen, fnOf_pull_g _ g J J₀ _ hh]
      erw [GlobalTheory.FlagMod.Frames.ev_LL_g]
      have hu : (∏ ix : Ix Dw, X.F.TAt (J PUnit.unit) k₀ (genericPt C.Y ≫ g) hh ix ^ (-ex ix)) * cst =
          (∏ x ∈ Finset.univ, (X.F.TAt (J PUnit.unit) k₀ (genericPt C.Y ≫ g) hh (some x) *
            t₀ x.1 x.2) ^ ex (some x))⁻¹ := by
        rw [Fintype.prod_option, hex, neg_zero, zpow_zero, one_mul, ← Finset.prod_mul_distrib,
          ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun x _ => ?_
        rw [zpow_neg, zpow_neg, ← mul_inv, ← mul_zpow]
      exact (Units.val_mul _ _).symm.trans (congrArg Units.val hu)
    rw [hval]
    exact h1
  exact (GlobalTheory.Cartier.presents_toLB _).lbIso ⟨hL, hr, heq⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackExtendDVR
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullIsoExt

theorem isPullback_sq {S S' : Scheme.{0}} {G : Over S} {A : Over S'} {f : S' ⟶ S}
    {a : A.left ⟶ G.left} (hA : IsPullback a A.hom G.hom f)
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : Geo.Tor.IsSquare a φ₂) :
    IsPullback φ₂ (A ⊗ A).hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, ← v₁, Category.assoc]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, ← v₂, Category.assoc]

theorem lbIso_pull_ext : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → ∀ (a b : G2 A ⟶ G2 A) (a' b' : G2 G ⟶ G2 G), a.left ≫ φ₂ = φ₂ ≫ a'.left → b.left ≫ φ₂ = φ₂ ≫ b'.left → LBIso (P.pull a.left) (P.pull b.left) → LBIso (P'.pull a'.left) (P'.pull b'.left) := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hG hφ hsq P P' hP hP' hPP' a b a' b' ha hb h
  have hpb : IsPullback φ₂ (G2 A).hom (G2 G).hom (spMap (algebraMap W L)) := isPullback_sq hφ.1 hsq
  have hG2 : IsAbelianScheme (G2 G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  have side : ∀ (c : G2 A ⟶ G2 A) (c' : G2 G ⟶ G2 G), c.left ≫ φ₂ = φ₂ ≫ c'.left →
      LBIso ((P'.pull c'.left).pull φ₂) (P.pull c.left) := fun c c' hc =>
    LBIso.trans (pull_isLB (pull_isLB hP' _) _) (pull_isLB hP' _) (pull_isLB hP _)
      (GlobalTheory.GenSpread.lbIso_pull_pull hP' φ₂ hc).symm
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hPP' c.left rfl).symm
  have key : LBIso ((P'.pull a'.left).pull φ₂) ((P'.pull b'.left).pull φ₂) :=
    LBIso.trans (pull_isLB (pull_isLB hP' _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP' _) _)
      (side a a' ha)
      (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (pull_isLB (pull_isLB hP' _) _) h (side b b' hb).symm)
  exact GlobalTheory.GenericIsoAb.lbIso_of_generic_pullback W L (G2 G) (G2 A).left (G2 A).hom φ₂ hG2 hpb
    (P'.pull a'.left) (P'.pull b'.left) (pull_isLB hP' _) (pull_isLB hP' _) key

end GlobalTheory.PullIsoExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairOfLambdaBundleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LamPull

theorem lbIso_pull_lift : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (M : LB A.left), P.IsLB → M.IsLB → LBIso P (cubeLB A ![fst A A, snd A A] M) → ∀ (T : Over (Sp ℂ)) (a b : T ⟶ A), LBIso (P.pull (lift a b).left) (cubeLB A ![a, b] M) := by
  intro A _ _ P M hP hM e T a b
  have hc : ∀ {T' : Over (Sp ℂ)} (x : Fin 2 → (T' ⟶ A)), (cubeLB A x M).IsLB := fun x => by
    unfold cubeLB; exact LB.isLB_linComb hM _ _
  have h₁ : LBIso (P.pull (lift a b).left) ((cubeLB A ![fst A A, snd A A] M).pull (lift a b).left) :=
    GlobalTheory.GenSpread.lbIso_pullback e _
  have h₂ : LBIso ((cubeLB A ![fst A A, snd A A] M).pull (lift a b).left) (cubeLB A ![a, b] M) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
      (GlobalTheory.PrimNorm.chartSquare M (lift a b) (lift_fst a b).symm (lift_snd a b).symm) (GlobalTheory.lbIso_refl (hc _))
  exact LBIso.trans (pull_isLB hP _) (pull_isLB (hc _) _) (hc _) h₁ h₂

end GlobalTheory.LamPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanRelationsConductorOfEvalEqZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_relations_conductor_of_eval_eq_zero : ∀ (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E] (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D) (F : σ → MvPolynomial ν R), Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) → RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) → IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ) → ∀ G : MvPolynomial ν R', MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0 → G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔ (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  first | exact @GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | exact GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero | (intros; apply GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero <;> assumption)
end

