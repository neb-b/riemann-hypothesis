module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChartPtChartPt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

variable {K : Type} [Field K]

abbrev baseMap (K B : Type) [Field K] [CommRing B] [Algebra (DualNumber K) B] : K →+* B :=
  (algebraMap (DualNumber K) B).comp (algebraMap K (DualNumber K))

def transl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) : Sp (DualNumber B) ⟶ A.left :=
  if h : ∃ w, IsTransl φ x v w then h.choose else spMap (algebraMap B (DualNumber B)) ≫ x

theorem isTransl_transl {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (hx : x ≫ A.hom = spMap φ) (v : epsR K ⟶ A) : IsTransl φ x v (transl φ x v) := by
  have h : ∃ w, IsTransl φ x v w := exists_isTransl φ x hx v
  rw [transl, dite_eq_left h]
  exact h.choose_spec

def dlogAt {A : Over (Sp K)} [GrpObj A] {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left)
    (v : epsR K ⟶ A) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ) : B :=
  (valR (transl φ x v) Wo g.val).snd * valR x Wo g⁻¹.val

def chartVal {A : Over (Sp K)} [GrpObj A] {Z : Scheme.{0}} (m : A.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω))
    {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (f : Γ(Z, Ω)) : B :=
  valR (x ≫ m) Ω f + algebraMap (DualNumber K) B DualNumber.eps *
    (valR (x ≫ m) Ω (δ f) + ∑ a, (∑ b, baseMap K B (θ a b) * dlogAt (baseMap K B) x (u b) Wo g) *
      (valR (transl (baseMap K B) x (u a) ≫ m) Ω f).snd)

def IsChartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) {Z : Scheme.{0}} (m : A.left ⟶ Z)
    (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (l : Sp B ⟶ A'.left) : Prop :=
  l ≫ A'.hom = spMap (algebraMap (DualNumber K) B) ∧ ⊤ ≤ (l ≫ m') ⁻¹ᵁ Ω ∧
    ∀ f, valR (l ≫ m') Ω f = chartVal m Ω δ u θ Wo g x f

def chartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left) {Z : Scheme.{0}}
    (m : A.left ⟶ Z) (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ} (u : Fin n → (epsR K ⟶ A))
    (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) : Sp B ⟶ A'.left :=
  if h : ∃ l, IsChartPt A' m m' Ω δ u θ Wo g x l then h.choose else x ≫ i

theorem isChartPt_chartPt {A : Over (Sp K)} [GrpObj A] (A' : Over (Sp (DualNumber K))) (i : A.left ⟶ A'.left)
    {Z : Scheme.{0}} (m : A.left ⟶ Z) (m' : A'.left ⟶ Z) (Ω : Z.Opens) (δ : Γ(Z, Ω) → Γ(Z, Ω)) {n : ℕ}
    (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (Wo : A.left.Opens) (g : Γ(A.left, Wo)ˣ)
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left)
    (h : ∃ l, IsChartPt A' m m' Ω δ u θ Wo g x l) :
    IsChartPt A' m m' Ω δ u θ Wo g x (chartPt A' i m m' Ω δ u θ Wo g x) := by
  rw [chartPt, dite_eq_left h]
  exact h.choose_spec

theorem valR_eq_ev {Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U)
    (f : Γ(Z, U)) : valR z U f = ev z U h f := by
  rw [valR, dite_eq_left h]
  rfl

theorem IsChartPt.unique {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z}
    (hm' : IsPullback m' A'.hom h y1) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ}
    {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ}
    {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l l' : Sp B ⟶ A'.left}
    (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l) (hl' : IsChartPt A' m m' Ω.1 δ u θ Wo g x l') : l = l' := by
  obtain ⟨h1, h2, h3⟩ := hl
  obtain ⟨h1', h2', h3'⟩ := hl'
  have e : ev (l ≫ m') Ω.1 h2 = ev (l' ≫ m') Ω.1 h2' := by
    ext f
    rw [← valR_eq_ev, ← valR_eq_ev, h3 f, h3' f]
  have e2 : l ≫ m' = l' ≫ m' := by
    rw [← GlobalTheory.FlagMod.spMap_ev (l ≫ m') Ω.2 h2, ← GlobalTheory.FlagMod.spMap_ev (l' ≫ m') Ω.2 h2', e]
  exact hm'.hom_ext e2 (h1.trans h1'.symm)

end GlobalTheory.CechKS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSplitTorusIntoTorusExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory.TorusFieldCrit

theorem exists_prime_hom_of_not_surjective {X : Type} [AddCommGroup X] {r : ℕ}
    (M : X →+ (Fin r → ℤ)) (hM : ¬ Function.Surjective M) :
    ∃ p : ℕ, p.Prime ∧ ∃ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 ∧ φ.comp M = 0 := by
  obtain ⟨y, hy⟩ := not_forall.1 hM
  have hQ : Nontrivial ((Fin r → ℤ) ⧸ M.range) :=
    ⟨⟨(y : (Fin r → ℤ) ⧸ M.range), 0, fun h => hy ((QuotientAddGroup.eq_zero_iff y).1 h)⟩⟩
  haveI : AddGroup.FG ((Fin r → ℤ) ⧸ M.range) := inferInstance
  obtain ⟨n, κ, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod ((Fin r → ℤ) ⧸ M.range)
  suffices h : ∃ q, q.Prime ∧ ∃ ψ : ((Fin r → ℤ) ⧸ M.range) →+ ZMod q, Function.Surjective ψ by
    obtain ⟨q, hq, ψ, hψ⟩ := h
    haveI := Fact.mk hq
    refine ⟨q, hq, ψ.comp (QuotientAddGroup.mk' M.range), fun h => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hψ 1
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective M.range x
      have := DFunLike.congr_fun h z
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zero_apply] at this
      rw [this] at hx
      exact zero_ne_one hx
    · ext x
      simp [(QuotientAddGroup.eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨x, rfl⟩)]
  by_cases hn : 0 < n
  · refine ⟨2, Nat.prime_two, ((Int.castAddHom (ZMod 2)).comp
        ((Finsupp.applyAddHom (⟨0, hn⟩ : Fin n)).comp (AddMonoidHom.fst _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (Finsupp.single ⟨0, hn⟩ k, 0), ?_⟩
    simp
  · have hn0 : n = 0 := by omega
    subst hn0
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push_neg at h
      apply not_subsingleton ((Fin r → ℤ) ⧸ M.range)
      refine ⟨fun a b => f.injective ?_⟩
      have key : ∀ x : (Fin 0 →₀ ℤ) × DirectSum κ (fun j ↦ ZMod (p j ^ e j)), x = 0 := fun x => by
        refine Prod.ext (Finsupp.ext fun j => j.elim0) (DFinsupp.ext fun j => ?_)
        haveI : Subsingleton (ZMod (p j ^ e j)) := by rw [h j, pow_zero]; infer_instance
        exact Subsingleton.elim _ _
      rw [key (f a), key (f b)]
    classical
    haveI := Fact.mk (hp i)
    refine ⟨p i, hp i, ((ZMod.castHom (dvd_pow_self (p i) hi) (ZMod (p i))).toAddMonoidHom.comp
      ((DirectSum.component ℤ κ (fun j => ZMod (p j ^ e j)) i).toAddMonoidHom.comp
        (AddMonoidHom.snd _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (0, DirectSum.lof ℤ κ (fun j => ZMod (p j ^ e j)) i (k : ZMod (p i ^ e i))), ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.apply_symm_apply, AddMonoidHom.coe_snd, LinearMap.toAddMonoidHom_coe,
      DirectSum.component.lof_self, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply]
    exact ZMod.cast_intCast (dvd_pow_self (p i) hi) k

theorem isClosedImmersion_of_torusExtension (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω)))
    [GrpObj H] (E : TorusExtension H) (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H)
    (hv : IsMonHom v)
    (hker : ∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 →
      GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) :
    IsClosedImmersion v.left := by
  letI := E.addCommGroup; letI := E.grpB
  haveI := E.free; haveI := E.finite
  haveI := E.i_hom; haveI := E.q_hom; haveI := E.isAbelian.proper
  haveI : ConnectedSpace (Spec (CommRingCat.of Ω)) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing Ω
  have h1 : v ≫ E.q = toUnit _ ≫ η[E.B] :=
    GlobalTheory.splitTorus_hom_proper_trivial_local Ω (Fin r → ℤ) E.B (v ≫ E.q) inferInstance
  let w := E.isKernel.lift v (toUnit _) h1
  have hw : w ≫ E.i = v := E.isKernel.lift_fst _ _ _
  have hmono : Mono E.i := ⟨fun a b e => E.isKernel.hom_ext e (toUnit_unique _ _)⟩
  haveI : IsMonHom w := GlobalTheory.Serre.isMonHom_of_mul_comp w fun T x y => by
    rw [← cancel_mono E.i, MonObj.mul_comp (x ≫ w), Category.assoc, Category.assoc, Category.assoc, hw,
      MonObj.mul_comp]
  obtain ⟨M, hM⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap w
  by_cases hs : Function.Surjective M
  · have hdiag : w = GlobalTheory.Diag.diagMap _ M := by
      rw [hM]; symm
      exact (GlobalTheory.SplitTorus.eq_torusMap_iff _ M).2 fun b => GlobalTheory.Diag.diagMap_chi _ M b
    have hη : IsClosedImmersion (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      GlobalTheory.isClosedImmersion_of_section_of_isSeparated E.B.hom _ (by simpa using Over.w η[E.B])
    have hpb : IsPullback E.i.left (toUnit _ : splitTorus _ E.X ⟶ 𝟙_ _).left E.q.left (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      E.isKernel.map (Over.forget _)
    have hi : IsClosedImmersion E.i.left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη
    have hw' : IsClosedImmersion w.left := hdiag ▸ GlobalTheory.Diag.isClosedImmersion_diagMap _ hs
    rw [← hw, Over.comp_left]
    infer_instance
  · exfalso
    obtain ⟨p, hp, φ, hφ, hφM⟩ := exists_prime_hom_of_not_surjective M hs
    apply hker p hp φ hφ
    rw [← hw, hM, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, hφM, GlobalTheory.SplitTorus.torusMap_zero,
      MonObj.one_comp]

end GlobalTheory.TorusFieldCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocCocOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

abbrev SmallCat (W : K → X.left.Opens) : Type 1 := (IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).FullSubcategory

abbrev smallAt (W : K → X.left.Opens) {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) (h : Sm W x) :
    SmallCat W := ⟨trivAt x, h⟩

theorem Sm.map {W : K → X.left.Opens} {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') {x : Pt X D} (h : Sm W x) : Sm W (D := D') (spOver φ ≫ x) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, (trivMap φ x).le_preimage hi⟩


open Classical in
def cocOf (W : K → X.left.Opens) (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _))) :
    Fn1 X := fun _ _ _ _ _ _ φ x ↦
  if h : Sm W x then n (smallAt W x h) (smallAt W _ (h.map φ)) (ObjectProperty.homMk (trivMap φ x)) else 0

end GlobalTheory.PtExt

namespace GlobalTheory.PtExt
variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type}

private theorem thickHom_ext {T T' : Thick (dp0 R) (X.hom ≫ 𝟙 _)}
    {f g : Thick.Hom T T'} (h : ∀ b, f.φ b = g.φ b) : f = g := by
  rcases f with ⟨φ, φ₀, comm, dp, pt⟩
  rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
  obtain rfl : φ = ψ := AlgHom.ext h
  obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := T.surj c
    rw [comm, comm']
  rfl

theorem isCoc_cocOf (W : K → X.left.Opens)
    (n : C1 ((IsSmall (dp0 R) (X.hom ≫ 𝟙 _) W).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _)))
    (hn : ∀ (T T' T'' : SmallCat W) (a : T ⟶ T') (b : T' ⟶ T''), T.obj.J = ⊥ → T'.obj.J = ⊥ →
      T''.obj.J = ⊥ → d1 _ n T T' T'' a b = 0) : IsCoc W (cocOf W n) := by
  intro D _ _ D' _ _ D'' _ _ φ ψ x hx
  have tr : ∀ (y y' : Pt X D'') (e : y = y') (h : Sm W y) (h' : Sm W y')
      (f : smallAt W x hx ⟶ smallAt W y h) (f' : smallAt W x hx ⟶ smallAt W y' h'),
      (∀ r, f.hom.φ r = f'.hom.φ r) → n _ _ f = n _ _ f' := by
    rintro y _ rfl h h' f f' hf
    have : f = f' := ObjectProperty.hom_ext _ (thickHom_ext hf)
    subst this; rfl
  have key := hn (smallAt W x hx) (smallAt W _ (hx.map φ)) (smallAt W _ ((hx.map φ).map ψ))
    (ObjectProperty.homMk (trivMap φ x)) (ObjectProperty.homMk (trivMap ψ _)) rfl rfl rfl
  rw [d1_apply] at key
  simp only [cocOf, dite_eq_left hx, dite_eq_left (hx.map φ)]
  have e := tr (spOver (ψ.comp φ) ≫ x) (spOver ψ ≫ spOver φ ≫ x)
    (by rw [← spOver_comp, Category.assoc]) (hx.map (ψ.comp φ)) ((hx.map φ).map ψ)
    (ObjectProperty.homMk (trivMap (ψ.comp φ) x))
    ((ObjectProperty.homMk (trivMap φ x) : smallAt W x hx ⟶ smallAt W _ (hx.map φ)) ≫
      (ObjectProperty.homMk (trivMap ψ (spOver φ ≫ x)) : smallAt W _ (hx.map φ) ⟶ smallAt W _ ((hx.map φ).map ψ)))
    (fun _ ↦ rfl)
  rw [e]
  change ψ _ - _ + _ = 0 at key
  linear_combination -key
end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnectingSumMultDiag
section
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
  [IsCocomm R A] [IsCocomm R B]


variable (R A) in
abbrev multDiag (i : ℕ) : A ⊗[R] A →ₐ[R] A :=
  Algebra.TensorProduct.lift (mulBy R A i : A →ₐ[R] A) (AlgHom.id R _) (fun _ _ ↦ Commute.all _ _)


variable (R A) in
abbrev valZero : A ⊗[R] A →ₐ[R] R :=
  Algebra.TensorProduct.lift (counitAlgHom R A) (counitAlgHom R A) (fun _ _ ↦ Commute.all _ _)


theorem pullTwo_mulBy_eq (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) (k : ℕ) :
    pullbackTwo (mulBy R A k) c = algebraMap R _ (valZero R A c) + k • c +
      cobOne R A (∑ i ∈ Finset.range k, multDiag R A i c) := by
  induction k with
  | zero =>
    have h0 : ∀ a : A, mulBy R A 0 a = algebraMap R A (counit a) := fun _ => rfl
    rw [Finset.sum_range_zero, map_zero, zero_smul, add_zero, add_zero]
    generalize c = t
    induction t with
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
    | tmul a b =>
      simp [h0, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
        smul_smul, mul_comm]
  | succ k ih =>
    have h := pullTwo_convMul (mulBy R A k) (BialgHom.id R A) c hc
    have e : (toConv (mulBy R A k) * toConv (BialgHom.id R A)).ofConv = mulBy R A (k + 1) := by
      rw [mulBy, mulBy, pow_succ]
    have e2 : ∀ t : A ⊗[R] A, LinearMap.mul' R A (TensorProduct.map (mulBy R A k : A →ₗ[R] A)
        (BialgHom.id R A : A →ₗ[R] A) t) = multDiag R A k t := fun t => by
      induction t with
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
      | tmul a b => simp
    rw [e, e2, pullTwo_id, ih] at h
    rw [h, Finset.sum_range_succ, map_add (f := _), succ_nsmul]
    abel

end PDiv

namespace PDivGroup

open PDiv

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantOfIsIsoRestrict
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem isDominant_of_isIso_restrict (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X)
    (U : X.Opens) (hU : (U : Set X).Nonempty) (h : IsIso (s ∣_ U)) : IsDominant s := by
  refine ⟨?_⟩
  have hd : Dense (U : Set X) := U.isOpen.dense hU
  refine hd.mono ?_
  intro x hx
  obtain ⟨y, hy⟩ := (s ∣_ U).surjective ⟨x, hx⟩
  refine ⟨y.1, ?_⟩
  have := morphismRestrict_base_coe s U y
  rw [hy] at this
  exact this.symm

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

def e8 (W : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) ℤ := W + W.transpose

def actMat (W : Matrix (Fin 8) (Fin 8) ℤ) : Fin 2 → Matrix (Fin 8) (Fin 8) ℤ :=
  ![(e8 W).adjugate * W, (e8 W).adjugate * W.transpose]

variable {S : Scheme.{0}}

def IsProd {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)) : Prop :=
  (∀ a, IsMonHom (pr a)) ∧ ∀ (T : Over S) (y : Fin 8 → (T ⟶ B)), ∃! x : T ⟶ A, ∀ a, x ≫ pr a = y a

def IsE8WeightedBundle (W : Matrix (Fin 8) (Fin 8) ℤ) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B))
    (L : LB A.left) (M : LB B.left) : Prop :=
  LBIso L (LB.LinComb M (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2)))

def IsPPFib (B : Over S) [GrpObj B] (g : ℕ) (M : RigLB B) : Prop :=
  IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ Nonempty (CubicalStr B M) ∧ RelAmple B M.L ∧ KTriv B M.L

def ActsBy {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (f : A ⟶ A)
    (m : Matrix (Fin 8) (Fin 8) ℤ) : Prop :=
  ∀ a, f ≫ pr a = ∏ b, pr b ^ m a b

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenOfIsTopFormFrame
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameEtale

theorem etale_eval₂Hom_of_basis {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (hα : α.Smooth)
    {n : ℕ} (z : Fin n → A) (b : Module.Basis (Fin n) A (Omega α)) (hb : ∀ i, b i = dFun α (z i)) :
    (MvPolynomial.eval₂Hom α z).Etale := by
  letI := α.toAlgebra
  haveI : Algebra.Smooth k A := hα
  letI := (MvPolynomial.eval₂Hom α z).toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C α z r).symm
  have hX (i) : algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i) = z i :=
    MvPolynomial.eval₂Hom_X' α z i
  exact EtaleCoordJacobian.etale_of_basis k A (Fin n) b fun i => by rw [hX]; exact hb i

theorem isEtCoord_of_isFrame : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (V : Y.Opens) (z : Fin n → Γ(Y, V)), IsFrame (dOn q z) → IsAffineOpen V ∧ IsEtCoord q V z := by
  intro k _ Y q n hq V z hz
  refine ⟨hz.affine, ?_⟩
  obtain ⟨b, hb⟩ := FrameBasis.exists_basis_of_isFrame k Y q n hq V z hz
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have h := HasRingHomProperty.appLE (@Smooth) q inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hz.affine⟩ le_top
  have h₁ : (DVR.FlatBC.algX q V).Smooth :=
    RingHom.Smooth.respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv h
  exact etale_eval₂Hom_of_basis (DVR.FlatBC.algX q V) h₁ z b hb

end GlobalTheory.FrameEtale
end
end

