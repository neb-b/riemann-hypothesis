module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplit
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open Opposite

namespace GlobalTheory.TwoOpens

theorem sections_inter_eq_sub_of_subsingleton_cohOn : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  intro Y F W₁ W₂ h t
  let A := (GlobalTheory.toAbSheaf Y).obj F
  let S := Flasque.injectiveShortComplex A
  have hS : S.ShortExact := Flasque.injectiveShortComplex_shortExact A
  have hfl : TopCat.Sheaf.IsFlasque S.X₂ := Flasque.isFlasque_injectiveShortComplex_X₂ A
  have hinj : ∀ W : Y.Opens, Function.Injective (S.f.hom.app (op W)) := by
    intro W x y hxy
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective x
    obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
    rw [← SheafLES.equivZero_map, ← SheafLES.equivZero_map] at hxy
    rw [SheafLES.injective_zero hS W ((SheafLES.equivZero.{0} S.X₂ W).injective hxy)]
  have hex : ∀ W : Y.Opens, Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) := by
    intro W x
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₂ W).surjective x
    rw [← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (SheafLES.equivZero_map S.f W y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
      exact ⟨y, (SheafLES.equivZero.{0} S.X₂ W).injective
        ((SheafLES.equivZero_map S.f W y).trans hy)⟩

  have natf : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.f.hom.app (op V) (S.X₁.obj.map (homOfLE hUV).op x) =
        S.X₂.obj.map (homOfLE hUV).op (S.f.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.f.hom (homOfLE hUV).op x
  have natg : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hUV).op x) =
        S.X₃.obj.map (homOfLE hUV).op (S.g.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.g.hom (homOfLE hUV).op x
  have resres : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₂.obj.map (homOfLE h₂).op (S.X₂.obj.map (homOfLE h₁).op x) =
        S.X₂.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have resres3 : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₃.obj.map (homOfLE h₂).op (S.X₃.obj.map (homOfLE h₁).op x) =
        S.X₃.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

  obtain ⟨b', hb'⟩ := (AddCommGrpCat.epi_iff_surjective
    (S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op)).1 (hfl.epi _)
    (S.f.hom.app (op (W₁ ⊓ W₂)) (sectionsOn.toΓ F _ t))

  let U : Bool → Y.Opens := fun b => cond b W₂ W₁
  let sf : ∀ b : Bool, ToType (S.X₃.obj.obj (op (U b))) := fun b =>
    match b with
    | true => S.g.hom.app (op W₂) b'
    | false => 0
  have h0 : S.X₃.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    rw [← natg, hb']
    exact (hex _).apply_apply_eq_zero _
  have h0' : S.X₃.obj.map (homOfLE (inf_le_left : W₂ ⊓ W₁ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    have e := resres3 (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (inf_comm W₂ W₁).le (S.g.hom.app (op W₂) b')
    rw [h0, map_zero] at e
    exact e.symm
  have hcomp : TopCat.Presheaf.IsCompatible S.X₃.obj U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (map_zero _).trans h0.symm
    · exact h0'.trans (map_zero _).symm
    · rfl
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := Y.toPresheafedSpace.carrier) S.X₃ U (W₁ ⊔ W₂)
    (fun b => homOfLE (by cases b; exacts [le_sup_left, le_sup_right]))
    (sup_le (le_iSup U false) (le_iSup U true)) sf hcomp

  obtain ⟨i, hi⟩ := SheafLES.sections_surjective_of_subsingleton.{0} hS (W₁ ⊔ W₂) h q
  obtain ⟨bb, hbb⟩ := (hex W₂ (b' - S.X₂.obj.map (homOfLE (le_sup_right : W₂ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_sub, natg, hi]
    exact sub_eq_zero.2 (hq true).symm)
  obtain ⟨aa, haa⟩ := (hex W₁ (- S.X₂.obj.map (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_neg, natg, hi]
    exact neg_eq_zero.2 (hq false))
  refine ⟨(sectionsOn.toΓ F W₁).symm aa, (sectionsOn.toΓ F W₂).symm bb, ?_⟩
  apply (sectionsOn.toΓ F _).injective
  rw [map_sub, sectionsOn.toΓ_res, sectionsOn.toΓ_res]
  simp only [AddEquiv.apply_symm_apply]
  apply hinj
  change _ = S.f.hom.app _ (S.X₁.obj.map _ bb - S.X₁.obj.map _ aa)
  erw [map_sub]
  rw [natf, natf, hbb, haa, map_sub, map_neg, resres, resres, hb']
  abel

end GlobalTheory.TwoOpens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureModuliFibreOfMonomialPeriodPreChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreDense

theorem isPrime_map_of_flat {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (φ : A →+* R) (hf : φ.Flat) (hm : (maximalIdeal A).map φ = maximalIdeal R) (I : Ideal A)
    [IsRegularLocalRing (A ⧸ I)] : (I.map φ).IsPrime := by
  let _ := φ.toAlgebra
  have : Module.Flat A R := hf
  have hI : I ≤ maximalIdeal A := le_maximalIdeal (Ideal.Quotient.nontrivial_iff.1 inferInstance)
  have hJ : I.map (algebraMap A R) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h.ge.trans ((Ideal.map_mono hI).trans hm.le)))
  have : Nontrivial (R ⧸ I.map (algebraMap A R)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : IsLocalRing (R ⧸ I.map (algebraMap A R)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : Module.Flat (A ⧸ I) (R ⧸ I.map (algebraMap A R)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R I).toLinearEquiv
  have hmap : (maximalIdeal (A ⧸ I)).map (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) = maximalIdeal _ := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← map_maximalIdeal_of_surjective (Ideal.Quotient.mk (I.map (algebraMap A R))) Ideal.Quotient.mk_surjective,
      ← hm, Ideal.map_map, Ideal.map_map]
    rfl
  have : IsLocalHom (algebraMap (A ⧸ I) (R ⧸ I.map (algebraMap A R))) :=
    ((local_hom_tfae _).out 1 3).2 hmap.le
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap
  have : IsDomain (R ⧸ I.map (algebraMap A R)) := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
  exact (Ideal.Quotient.isDomain_iff_prime _).1 this

theorem exists_toStalk (o : Type) [CommRing o] (x : Sp o) : ∃ τ : CommRingCat.of o ⟶ (Sp o).presheaf.stalk x,
    (Sp o).fromSpecStalk x = Spec.map τ ∧ x.asIdeal.map τ.hom = maximalIdeal ((Sp o).presheaf.stalk x) := by
  have := x.isPrime
  let _ : Algebra o ((Spec (CommRingCat.of o)).presheaf.stalk x) := (StructureSheaf.toStalk o x).hom.toAlgebra
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of o)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk o x
  exact ⟨StructureSheaf.toStalk o x, Spec.fromSpecStalk_eq' (CommRingCat.of o) x,
    IsLocalization.AtPrime.map_eq_maximalIdeal x.asIdeal ((Spec (CommRingCat.of o)).presheaf.stalk x)⟩

theorem isPrime_fibre {o : Type} [CommRing o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Smooth s] {R : Type} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (b : o →+* R) (ξ : Sp R ⟶ S) (hb : ξ ≫ s = spMap b)
    (he : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom) : (((maximalIdeal R).comap b).map b).IsPrime := by
  have hreg := GlobalTheory.FibreRegular.isRegularLocalRing_stalk_quot_maximalIdeal _ _ s (ξ (closedPoint R))
  have hp := isPrime_map_of_flat _ he.1 he.2.1
    ((maximalIdeal ((Sp o).presheaf.stalk (s (ξ (closedPoint R))))).map (s.stalkMap (ξ (closedPoint R))).hom)
  obtain ⟨τ, hτ, hmax⟩ := exists_toStalk o (s (ξ (closedPoint R)))
  have hc : τ ≫ s.stalkMap (ξ (closedPoint R)) ≫ Scheme.stalkClosedPointTo ξ = CommRingCat.ofHom b := by
    apply Spec.map_injective
    refine Eq.trans ?_ hb
    rw [Spec.map_comp, Spec.map_comp, Category.assoc, ← hτ, Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc]
    exact congrArg (· ≫ s) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) ξ)
  have hx : (s (ξ (closedPoint R))).asIdeal = (maximalIdeal R).comap b :=
    congrArg (fun f : Sp R ⟶ Sp o => (f (closedPoint R)).asIdeal) hb
  have hb' : (Scheme.stalkClosedPointTo ξ).hom.comp ((s.stalkMap (ξ (closedPoint R))).hom.comp τ.hom) = b :=
    congrArg (fun q => q.hom) hc
  rwa [← hmax, Ideal.map_map, Ideal.map_map, RingHom.comp_assoc, hb', hx] at hp

theorem mem_closure_fibre : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) [IsNoetherianRing o] [Smooth s], PreChart F s j φ BD d x → x ∈ closure (Set.range j ∩ s ⁻¹' {s x}) := by
  intro o _ ζ g n F S s j _ φ BD d x _ _ h
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, ⟨-, -, hb, rfl, he, -⟩, ⟨ht, -, hj⟩, -⟩ := h
  have hq := isPrime_fibre s b ξ hb he
  let q : Sp R := (⟨((maximalIdeal R).comap b).map b, hq⟩ : PrimeSpectrum R)
  have hs : ∀ p : Sp R, s (ξ p) = spMap b p := fun p => congrArg (fun f : Sp R ⟶ Sp o => f p) hb
  have h₁ : ξ q ∈ Set.range j := by
    refine (hj q).2 fun hmem => ?_
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hq)).1 hmem
    have := ht.2 (Pi.single i 1) (Ideal.mem_sup_right (by simpa [Pi.single_apply] using hi)) i
    simp at this
  have h₂ : s (ξ q) = s (ξ (closedPoint R)) := by
    refine (hs q).trans (Eq.trans (PrimeSpectrum.ext (le_antisymm ?_ ?_)) (hs (closedPoint R)).symm)
    · exact Ideal.comap_mono (f := b) (Ideal.map_comap_le (f := b) (K := maximalIdeal R))
    · exact Ideal.le_comap_map (f := b) (I := (maximalIdeal R).comap b)
  have h₃ : ξ q ⤳ ξ (closedPoint R) := (specializes_closedPoint (R := R) q).map ξ.continuous
  exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_inter h₁ h₂)) (specializes_iff_mem_closure.1 h₃)

end GlobalTheory.FibreDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O
open scoped NNReal

namespace GlobalTheory.VertForm

section Algebra

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {D : ℕ}


variable (E D) in
abbrev Form : Type u := (Π _ : Fin (D + 1), E) →ₘₗ[ℝ] ℝ

variable {num : Form E D} {G : Set E}

end Algebra

section Bundles

variable {k : Type} [CommRing k] {X X' : Scheme.{0}} {p : X ⟶ Sp k} {q : X' ⟶ Sp k}



def NefOver (L : HermLB p) (l : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [CharP κ l] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

theorem nefFib_iff (L : HermLB p) : NefFib L ↔ ∀ l : ℕ, l.Prime → NefOver L l :=
  ⟨fun h _ _ Z i _ _ κ _ _ _ _ hZ => h Z i κ hZ, fun h Z i _ _ κ _ _ _ hZ =>
    h (ringChar κ) (CharP.char_is_prime κ _) Z i κ hZ⟩

end Bundles

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Lies (V' V : Cover Y) (π : V'.X ⟶ V.X) : Prop := ∃ g : V'.G ⟶ V.G, g ≫ V.j = V'.j ≫ π ∧ g ≫ V.π = V'.π

end Covers

end GlobalTheory.VertForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffPointwiseCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)}

theorem existsUnique_pt_of_triv (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) :
    ∃! y : Pt X T.B, spMap T.π ≫ y.left = T.x := by
  have hb : Function.Bijective T.π :=
    ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ by simpa [hT] using (T.ker b).1 hb, T.surj⟩
  let e := RingEquiv.ofBijective T.π hb
  let ρ : T.B₀ →+* T.B := e.symm.toRingHom
  have h1 : ρ.comp T.π = RingHom.id _ := RingHom.ext e.symm_apply_apply
  have h2 : T.π.comp ρ = RingHom.id _ := RingHom.ext e.apply_symm_apply
  have k1 : spMap ρ ≫ spMap T.π = 𝟙 _ := by rw [← Cris.spMap_comp, h1, Cris.spMap_id]
  have k2 : spMap T.π ≫ spMap ρ = 𝟙 _ := by rw [← Cris.spMap_comp, h2, Cris.spMap_id]
  have hw : (spMap ρ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B) := by
    have : T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B)) :=
      (congrArg (T.x ≫ ·) (Category.comp_id X.hom)).symm.trans T.w
    rw [Category.assoc, this, Cris.spMap_comp, ← Category.assoc, k1, Category.id_comp]
  let point : Pt X T.B := Over.homMk (spMap ρ ≫ T.x) hw
  refine ⟨point, ?_, ?_⟩
  · change spMap T.π ≫ spMap ρ ≫ T.x = T.x
    rw [← Category.assoc, k2, Category.id_comp]
  · intro y hy
    apply Over.OverMorphism.ext
    change y.left = spMap ρ ≫ T.x
    rw [← hy, ← Category.assoc, k1]
    exact (Category.id_comp _).symm

def liftHom (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (y : Pt X T.B) (h : spMap T.π ≫ y.left = T.x) : trivAt y ⟶ T :=
  Thick.trivHom (AlgHom.id R T.B) h

private def trivObject {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) :
    (IsTriv (X.hom ≫ 𝟙 _)).FullSubcategory :=
  ⟨trivAt x, show (trivAt x).J = ⊥ from rfl⟩

theorem mem_hodgeFiltration_iff_pointwiseCoboundary (R : Type) [CommRing R] (X : Over (Sp R)) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) :
    CatCoh.H1.mk _ f ∈ F1 (X.hom ≫ 𝟙 _) ↔ ∃ k : Fn0 X, IsCob (whole X) (fv f) k := by
  rw [F1, LinearMap.mem_ker, toH1O, CoefMap.pullCohomologyOne_class, CatCoh.H1.mk_eq_zero]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun D _ _ x ↦ g (trivObject x), ?_⟩
    intro D _ _ D' _ _ φ x _
    let a : trivObject x ⟶ trivObject (spOver φ ≫ x) := ObjectProperty.homMk (trivMap φ x)
    exact (congrFun (congrFun (congrFun hg (trivObject x)) (trivObject (spOver φ ≫ x))) a).symm
  · rintro ⟨k, hk⟩
    choose y hy hu using existsUnique_pt_of_triv (R := R) (X := X)
    refine ⟨fun T ↦ (k T.obj.B (y T.obj T.property) +
      ev f (liftHom T.obj _ (hy T.obj T.property)) : T.obj.B), ?_⟩
    funext ⟨T, hT⟩ ⟨T', hT'⟩ ⟨φ⟩
    have h' : spMap T'.π ≫ (spOver φ.φ ≫ y T hT).left = T'.x := by
      change spMap T'.π ≫ spMap (φ.φ : T.B →+* T'.B) ≫ (y T hT).left = T'.x
      have hπ : T'.π.comp (φ.φ : T.B →+* T'.B) = φ.φ₀.comp T.π :=
        RingHom.ext fun b ↦ (φ.comm b).symm
      rw [← Category.assoc, ← Cris.spMap_comp, hπ, Cris.spMap_comp, Category.assoc, hy T hT, φ.pt]
    have key : ∀ (z : Pt X T'.B) (hz : spMap T'.π ≫ z.left = T'.x), spOver φ.φ ≫ y T hT = z →
        k T'.B z + ev f (liftHom T' z hz) - φ.φ (k T.B (y T hT) + ev f (liftHom T _ (hy T hT))) = ev f φ := by
      rintro _ hz rfl
      have e1 := ev_sq f (trivMap φ.φ (y T hT)) (liftHom T' _ hz) (liftHom T _ (hy T hT)) φ fun _ ↦ rfl
      have e2 := hk T.B T'.B φ.φ (y T hT) (sm_whole _)
      change fv f T.B T'.B φ.φ (y T hT) + _ = _ at e1
      rw [map_add φ.φ]
      linear_combination e1 - e2
    exact key _ (hy T' hT') (hu T' hT' _ h')

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOneIffIsIntegral
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.CMVal

namespace GlobalTheory.RoadE

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_isIntegral (a : E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : E) * a) := by
  have h : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩
  rw [zsmul_eq_mul] at hi
  rw [Nat.cast_natAbs]
  rcases abs_choice k with h | h <;> rw [h]
  · exact hi
  · push_cast; rw [neg_mul]; exact hi.neg

theorem mem_one_iff_isIntegral (a : maximalRealSubfield E) :
    a ∈ (1 : Submodule (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ↔ IsIntegral ℤ (a : E) := by
  rw [Submodule.mem_one]
  have e : IsIntegral ℤ (a : E) ↔ IsIntegral ℤ a :=
    isIntegral_algebraMap_iff (R := ℤ) (A := maximalRealSubfield E) (B := E) (x := a) 
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩

def passMul (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (n : ℕ) : GlobalTheory.HilbFam.Lat (maximalRealSubfield E) where
  carrier := {x | ∃ y' ∈ lattice c y, (n : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨u, hu, e⟩ ⟨u', hu', e'⟩ => ⟨u + u', (latticeSub c y).add_mem hu hu', by
    rw [mul_add, e, e']; simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨u, hu, e⟩ => ⟨algebraMap (OF E) E a * u, mul_mem_lattice (algebraMap_mem_orderC c a) hu, by
    rw [ptE_smul, ← e]; ring⟩

theorem exists_coord_integral [IsCMField E] {θ : E} (hθ : θ ∉ maximalRealSubfield E) :
    ∃ k : ℕ, 0 < k ∧ ∀ (z : E) (a b : maximalRealSubfield E), IsIntegral ℤ z → (k : E) * z = (a : E) * θ + b →
      IsIntegral ℤ (a : E) ∧ IsIntegral ℤ (b : E) := by
  set σ := IsCMField.complexConj E with hσ
  have hδ : θ - σ θ ≠ 0 := fun h => hθ ((IsCMField.complexConj_eq_self_iff E θ).1 (sub_eq_zero.1 h).symm)
  obtain ⟨k₁, h₁, i₁⟩ := exists_nat_mul_isIntegral (θ - σ θ)⁻¹
  obtain ⟨k₂, h₂, i₂⟩ := exists_nat_mul_isIntegral θ
  refine ⟨k₁ * k₂, Nat.mul_pos h₁ h₂, fun z a b hz e => ?_⟩
  have hσz : IsIntegral ℤ (σ z) := hz.map (σ : E →+* E).toIntAlgHom
  have ea : σ (a : E) = a := σ.commutes a
  have eb : σ (b : E) = b := σ.commutes b
  have e' : ((k₁ * k₂ : ℕ) : E) * σ z = (a : E) * σ θ + b := by
    have := congrArg σ e
    rwa [map_mul, map_add, map_mul, map_natCast, ea, eb] at this
  push_cast at e e'
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have ha : (a : E) = k₂ * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    field_simp
    linear_combination e' - e
  refine ⟨ha ▸ (hn k₂).mul (i₁.mul (hz.sub hσz)), ?_⟩
  have hb : (b : E) = k₁ * (k₂ * z) - (k₂ * θ) * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    linear_combination -e - θ * ha
  exact hb ▸ ((hn k₁).mul ((hn k₂).mul hz)).sub (i₂.mul (i₁.mul (hz.sub hσz)))

theorem exists_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N₀ : ℕ),
    c ≠ ⊥ → θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) → 0 < N₀ →
    ∃ (n N : ℕ) (L : GlobalTheory.HilbFam.Lat (maximalRealSubfield E)), 0 < n ∧ 0 < N ∧ N₀ ∣ N ∧ GlobalTheory.HilbFam.HasLevel N L ∧
      ∀ x : Fin 2 → maximalRealSubfield E, x ∈ L ↔ ∃ y' ∈ lattice c y,
        (n : E) * y' = ((x 0 : maximalRealSubfield E) : E) * θ + ((x 1 : maximalRealSubfield E) : E) := by
  intro E _ _ _ θ c y N₀ hc hθ hN₀
  obtain ⟨M, hM, hlo, hhi⟩ := GlobalTheory.CMVal.LatBound.lattice_between E c hc y
  obtain ⟨k, hk, hco⟩ := exists_coord_integral (θ := θ) fun h => hθ ⟨⟨θ, h⟩, rfl⟩
  obtain ⟨D, hD, iD⟩ := exists_nat_mul_isIntegral θ
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  refine ⟨k * M, N₀ * (k * M * M * D), passMul θ c y (k * M), by positivity, by positivity, dvd_mul_right _ _,
    ⟨fun x hx => ?_, fun x hx => ?_⟩, fun x => Iff.rfl⟩
  · have h0 := (mem_one_iff_isIntegral _).1 (hx 0 trivial)
    have h1 := (mem_one_iff_isIntegral _).1 (hx 1 trivial)
    have hi : IsIntegral ℤ ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E))) :=
      (hn N₀).mul ((h0.mul iD).add ((hn D).mul h1))
    refine ⟨_, hlo ⟨_, hi⟩, ?_⟩
    rw [ptE_smul, map_natCast]
    show ((k * M : ℕ) : E) * ((M : E) * ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E)))) = _
    simp only [ptE]
    push_cast
    ring
  · obtain ⟨u, hu, e⟩ := hx
    obtain ⟨h0, h1⟩ := hco (M * u) (x 0) (x 1) (hhi u hu) (by rw [← mul_assoc, ← Nat.cast_mul]; exact e)
    intro i _
    fin_cases i
    · exact (mem_one_iff_isIntegral _).2 h0
    · exact (mem_one_iff_isIntegral _).2 h1

end GlobalTheory.RoadE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAffinePointEqOfInverseMemIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

namespace GlobalTheory.Points

theorem eq_of_forall_mem_basicOpen_iff {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    {z z' : X} (hz : z ∈ U) (hz' : z' ∈ U)
    (h : ∀ f : Γ(X, U), z ∈ X.basicOpen f ↔ z' ∈ X.basicOpen f) : z = z' := by
  have key : ∀ (x : U) (f : Γ(X, U)),
      f ∉ (hU.primeIdealOf x).asIdeal ↔ x.1 ∈ X.basicOpen f := by
    intro x f
    have e1 := hU.fromSpec_primeIdealOf x
    have e2 := hU.fromSpec_preimage_basicOpen f
    have : hU.primeIdealOf x ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x.1 ∈ X.basicOpen f := by
      rw [← e1]; rfl
    rw [← this, e2]; rfl
  have e : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨z', hz'⟩ := by
    apply PrimeSpectrum.ext
    ext f
    rw [← not_iff_not, key, key]
    exact h f
  have e1 := hU.fromSpec_primeIdealOf ⟨z, hz⟩
  have e2 := hU.fromSpec_primeIdealOf ⟨z', hz'⟩
  rw [e] at e1
  exact e1.symm.trans e2

theorem point_eq_of_inv_mem_iff :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → ∀ z z' : M.Z, z ∈ U → z' ∈ U → (∀ a ∈ M.ringOn (U : Set M.Z), a ≠ 0 → (a⁻¹ ∈ M.O z ↔ a⁻¹ ∈ M.O z')) → z = z' := by
  intro o Ω _ _ _ M U hU z z' hz hz' h
  refine eq_of_forall_mem_basicOpen_iff hU hz hz' fun f => ?_
  have hne : (U : Set M.Z).Nonempty := ⟨z, hz⟩
  have ha : valF M.pt U f ∈ M.ringOn U := (mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩
  rw [← isUnit_valF_iff hz f, ← isUnit_valF_iff hz' f, isUnit_O_iff, isUnit_O_iff]
  exact and_congr_right fun h0 => h _ ha h0

end GlobalTheory.Points
end

