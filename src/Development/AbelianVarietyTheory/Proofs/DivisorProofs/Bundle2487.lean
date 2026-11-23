module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0047
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValGPtOfStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.Poinc.TestAtPt

theorem val_gPt_of_stalk : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (x : M.Z) (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsLocalHom j → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ c : M.O x, ((ev (j ((M.stalkEquiv x).symm c)) : OO p) : PadicAlgCl p) = M.val (gPt p ≫ y) (c : Ω) := by
  intro o Ω _ _ _ M x R _ _ j _ p _ y ev hy c
  have hsp : ∀ w, (spMap j ≫ M.Z.fromSpecStalk x) w ⤳ x := fun w => by
    have : M.Z.fromSpecStalk x (spMap j w) ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  obtain ⟨U, hx, f, hf⟩ := M.Z.presheaf.germ_exist ((M.stalkEquiv x).symm c)
  have hc : c = ⟨valF M.pt U f, RatModel.valF_mem_O hx f⟩ := by
    rw [← RatModel.stalkEquiv_germ hx, hf, RingEquiv.apply_symm_apply]
  have hU : ⊤ ≤ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹ᵁ U := fun w _ => (hsp w).mem_open U.isOpen hx
  have hU0 : ⊤ ≤ M.Z.fromSpecStalk x ⁻¹ᵁ U := fun w _ => by
    have : M.Z.fromSpecStalk x w ∈ Set.range (M.Z.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this.mem_open U.isOpen hx
  have hg : gPt p ≫ y = spMap ((OO p).subtype.comp ev) ≫ (spMap j ≫ M.Z.fromSpecStalk x) := by
    rw [← hy, ← Category.assoc]
    congr 1
    rw [gPt, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  have hU' : ⊤ ≤ (gPt p ≫ y) ⁻¹ᵁ U := by
    rw [hg]; exact fun w _ => hU (x := spMap ((OO p).subtype.comp ev) w) trivial
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hU') (f := f) (hc ▸ rfl), GlobalTheory.Points.valF_eq_valR, hg,
    GlobalTheory.Points.valR_spMap_comp _ _ U hU]
  have e1 : valR (spMap j ≫ M.Z.fromSpecStalk x) U f = j (valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f) :=
    GlobalTheory.Points.valR_spMap_comp (C := M.Z.presheaf.stalk x) j (M.Z.fromSpecStalk x) U hU0 f
  have e2 : valR (A := M.Z.presheaf.stalk x) (M.Z.fromSpecStalk x) U f = M.Z.presheaf.germ U x hx f := by
    have eA : (M.Z.fromSpecStalk x).appLE U ⊤ hU0 =
        M.Z.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (M.Z.presheaf.stalk x)).inv := by
      rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
      simp only [Category.assoc, ← Functor.map_comp]
      have e : ((homOfLE le_top).op ≫ (homOfLE hU0).op :
          Opposite.op (⊤ : (Spec (M.Z.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
      rw [e, CategoryTheory.Functor.map_id, Category.comp_id]
    unfold valR
    erw [dite_eq_left hU0, eA]
    simp only [CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
    rfl
  rw [e1]
  exact (congrArg (fun t => ((OO p).subtype.comp ev) (j t)) (e2.trans hf)).symm

end GlobalTheory.Poinc.TestAtPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueUnitSectionSmulGenericFibreSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UnitGen

def gv {A : Type} [CommRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (((Sp A).presheaf.map (homOfLE h).op).hom ((f.app V).hom c))

theorem gs_gv {A : Type} [CommRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V))
    (z : Sp A) : gs f z V c = stalkOf z (gv f V h c) := by
  rw [gs_eq f z V (h trivial)]
  simp only [stalkOf, gv, RingHom.comp_apply]
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

theorem gs_spMap_top {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) (e : Γ(Sp A, ⊤)) (z : Sp B) :
    gs (spMap ψ) z ⊤ e = stalkOf z (ψ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom e)) := by
  rw [gs_eq _ z ⊤ trivial]
  simp only [stalkOf, RingHom.comp_apply]
  have := congrArg (fun q => q.hom e) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [← this, Iso.hom_inv_id_apply]
  rfl

theorem gs_comp_gv {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V)) (z : Sp B) : gs (spMap ψ ≫ f) z V c = stalkOf z (ψ (gv f V h c)) := by
  rw [← gs_pull (spMap ψ) f z V (h trivial) c, ← gs_res (spMap ψ) z h trivial, gs_spMap_top]
  rfl

theorem sp_field_eq {F : Type} [Field F] (a b : Sp F) : a = b :=
  PrimeSpectrum.ext (by haveI := a.isPrime; haveI := b.isPrime; rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])

end GlobalTheory.Mum.UnitGen


open GlobalTheory.Mum.UnitGen in
theorem GlobalTheory.Mum.UnitGen.value_unit_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (s : SecK C.P.L.L C.α k), ∃ x y : R, y ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a : W) (σ : SecK C.P.L.L T.β k), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J) → ∀ J, Good C.P.L.L (cpt W) J → stalkOf (cpt W) (T.φ y) * sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (a * T.φ x) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ hB D C k s
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hrg : C.P.L.rig.IsGen := C.P.L.rigGen
  have hE : eSec C.A.A ≫ C.α = C.gp ≫ eSec C.G := GlobalTheory.ZJ.eSec_comp_of_isGrpPullback C.α_cart
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((C.gp ≫ eSec C.G) (cpt (FractionRing R)))
  have hs₀ : ⊤ ≤ (eSec C.A.A) ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hE]; exact hi₀)
  have hr₀ : ⊤ ≤ C.gp ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact hi₀)
  set cs : FractionRing R := gv (eSec C.A.A) _ hs₀ (s.f (fun _ => i₀)) with hcs
  set cr : FractionRing R := gv C.gp _ hr₀ (C.P.L.rig.s (fun _ => i₀)).val with hcr
  have hcr0 : IsUnit cr := ((((C.P.L.rig.s (fun _ => i₀)).isUnit.map (C.gp.app _).hom).map _).map _)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) (cs / cr ^ k)
  refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
  intro W _ _ _ T a σ hσ J hJ

  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp T.φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp T.inj
  obtain ⟨ga, hga, hgp⟩ := Modif.factor_gp R C.toModif (FractionRing W) ((algebraMap W _).comp T.φ) (jK W ≫ T.ξ) hinj (by
    rw [Category.assoc, T.ξ_π]
    exact (Spec.map_comp _ _).symm)
  have hjK : jK W = spMap (algebraMap W (FractionRing W)) := rfl
  have hU : unitW T.G ≫ T.β = T.ξ ≫ eSec C.G := GlobalTheory.ZJ.eSec_comp_of_isGrpPullback T.cart
  set g : Sp (FractionRing W) := cpt (FractionRing W)
  set p : Sp (FractionRing W) ⟶ T.G.left := jK W ≫ unitW T.G with hp
  set p' : Sp (FractionRing W) ⟶ C.A.A.left := spMap ga ≫ eSec C.A.A with hp'
  have hr : jK W ≫ T.ξ ≫ eSec C.G = spMap ga ≫ C.gp ≫ eSec C.G := by rw [← Category.assoc, hgp, Category.assoc]
  have hpp : p ≫ T.β = p' ≫ C.α := by
    rw [hp, hp', Category.assoc, Category.assoc, hU, hE, hr]
  set I := J (T.ξ ≫ eSec C.G) with hIdef
  have hI : (T.ξ ≫ eSec C.G) (cpt W) ∈ C.P.L.L.U I := hJ _
  have hItop : ⊤ ≤ (T.ξ ≫ eSec C.G) ⁻¹ᵁ C.P.L.L.U I := (top_le_iff_cpt _ _).2 hI
  have hpI : (p ≫ T.β) g ∈ C.P.L.L.U I := by
    rw [hp, Category.assoc, hU, Scheme.Hom.comp_apply]; exact hItop trivial
  have hpi₀ : (p ≫ T.β) g ∈ C.P.L.L.U i₀ := by
    rw [hp, Category.assoc, hU, ← Category.assoc, hgp, Category.assoc, Scheme.Hom.comp_apply,
      sp_field_eq ((spMap ga) g) (cpt (FractionRing R))]
    exact hi₀
  obtain ⟨J', hJ', hJ'e⟩ := exists_good C.P.L.L hL g (K := PUnit) (fun _ => p ≫ T.β) (fun _ => I) (fun _ _ _ => rfl)
    (fun _ => hpI)
  have e1 := hσ _ p p' hpp g J' hJ'
  rw [sval_of σ p g J' (fun _ => I) (fun _ => hJ'e ⟨⟩),
    sval_of s p' g J' (fun _ => I) (fun _ => by rw [← hpp]; exact hJ'e ⟨⟩)] at e1

  have hσtop : ⊤ ≤ unitW T.G ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hU]; exact hI)
  have hρtop : ⊤ ≤ T.ξ ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact hI)
  set σv : W := gv (unitW T.G) _ hσtop (σ.f (fun _ => I)) with hσv
  set ρv : W := gv T.ξ _ hρtop (C.P.L.rig.s (fun _ => I)).val with hρv
  have eσ : gs p g (LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I)) (σ.f (fun _ => I)) =
      stalkOf g (algebraMap W _ σv) := by
    rw [hp, hjK]; exact gs_comp_gv _ _ _ hσtop _ g
  have hu : unitW T.G ≫ T.G.hom = 𝟙 _ := by simpa [unitW, eSec] using Over.w (η[T.G])
  have ea : gs p g ⊤ (scal T.G.hom a) = stalkOf g (algebraMap W _ a) := by
    have h1 : p ≫ T.G.hom = spMap (algebraMap W (FractionRing W)) := by
      rw [hp, Category.assoc, hu, Category.comp_id]
    have h2 := gs_pull p T.G.hom g ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a)
    rw [h1, gs_spMap_top, Iso.inv_hom_id_apply] at h2
    exact h2

  have hrp : (jK W ≫ T.ξ) ≫ eSec C.G = p ≫ T.β := by rw [hp, Category.assoc, Category.assoc, hU]
  have hp'i₀ : p' g ∈ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hpp]; exact hpi₀
  have hp'I : p' g ∈ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => I) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hpp]; exact hpI
  have hri₀ : (jK W ≫ T.ξ) g ∈ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hrp]; exact hpi₀
  have hrI : (jK W ≫ T.ξ) g ∈ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hrp]; exact hpI
  have e2 := sec_trans s p' g hp'i₀ hp'I
  have orbitMap_conj_smul_zero : gs p' g (LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀)) (s.f (fun _ => i₀)) = stalkOf g (ga cs) := by
    rw [hp']; exact gs_comp_gv ga _ _ hs₀ _ g
  have e3 := gen_trans hrg (jK W ≫ T.ξ) g hri₀ hrI
  have eB0 : (gm (jK W ≫ T.ξ) g (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀)) (C.P.L.rig.s (fun _ => i₀))).val = stalkOf g (ga cr) := by
    refine (gs_unit (jK W ≫ T.ξ) g _ hri₀ _).symm.trans ?_
    rw [hgp]; exact gs_comp_gv ga _ _ hr₀ _ g
  have eB : (gm (jK W ≫ T.ξ) g (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I)) (C.P.L.rig.s (fun _ => I))).val = stalkOf g (algebraMap W _ ρv) := by
    refine (gs_unit (jK W ≫ T.ξ) g _ hrI _).symm.trans ?_
    rw [hjK]; exact gs_comp_gv _ _ _ hρtop _ g
  have et : trF (L := C.P.L.L) (fun _ : Fin 1 => C.α) (fun _ => ((k : ℕ) : ℤ)) p' g (fun _ => i₀) (fun _ => I) =
      (trF (L := C.P.L.L) (fun _ : PUnit => eSec C.G) (fun _ => 1) (jK W ≫ T.ξ) g (fun _ => i₀) (fun _ => I)) ^ k := by
    simp only [trF]
    rw [show p' ≫ C.α = (jK W ≫ T.ξ) ≫ eSec C.G from hpp.symm.trans hrp.symm]
    simp

  rw [eσ, ea] at e1
  rw [orbitMap_conj_smul_zero, et] at e2
  have e3v := congrArg Units.val e3
  rw [Units.val_mul, eB0, eB] at e3v
  have hy0 : algebraMap R (FractionRing R) y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hxy' : algebraMap R _ x * cr ^ k = cs * algebraMap R _ y := by
    rw [div_eq_div_iff hy0 (pow_ne_zero _ hcr0.ne_zero)] at hxy; exact hxy
  have hXY := congrArg (fun q => stalkOf g (ga q)) hxy'
  simp only [map_mul, map_pow, hga, RingHom.comp_apply] at hXY
  rw [e3v, e2, Units.val_pow_eq_pow_val] at hXY
  have hW : T.φ y * σv = a * T.φ x * ρv ^ k := by
    apply ((stalkOf_injective g).comp (IsFractionRing.injective W (FractionRing W)))
    simp only [Function.comp_apply, map_mul, map_pow]
    refine ((trF (L := C.P.L.L) (fun _ : PUnit => eSec C.G) (fun _ => 1) (jK W ≫ T.ξ) g (fun _ => i₀)
      (fun _ => I)).isUnit.pow k).mul_left_inj.1 ?_
    rw [e1]
    linear_combination (-(stalkOf g (algebraMap W (FractionRing W) a))) * hXY
  have eBc : (gm T.ξ (cpt W) (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I)) (C.P.L.rig.s (fun _ => I))).val = stalkOf (cpt W) ρv :=
    (gs_unit T.ξ (cpt W) _ (hρtop trivial) _).symm.trans (gs_gv _ _ hρtop _ _)
  have eσc : gs (unitW T.G) (cpt W) (LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I)) (σ.f (fun _ => I)) =
      stalkOf (cpt W) σv := gs_gv _ _ hσtop _ _
  rw [sval_of σ (unitW T.G) (cpt W) J (fun _ => I) (fun _ => by rw [hU])]
  erw [eσc]
  rw [val_of C.P.L.rig T.ξ (cpt W) J (fun _ => I) (fun _ => rfl), eBc, ← map_mul, ← map_pow, ← map_mul, hW]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedConvolutionCancelInjectiveLatticeHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.UT.CancelHom

section
variable {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)}

theorem coeff_mapDomain_mul {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    (a : AddMonoidAlgebra F X') (c : AddMonoidAlgebra F X)
    (T : Finset X') (hT : a.coeff.support ⊆ T) (α : X) :
    (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α = ∑ χ ∈ T, a.coeff χ * c.coeff (α - h χ) := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.coeff_mapDomain, Finsupp.sum_mapDomain_index (by simp) (by intros; rw [add_mul]),
    Finsupp.sum_of_support_subset _ hT _ (by simp)]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [neg_add_eq_sub]

theorem sumV_fibre {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X) (α : X)
    (f : X' → X → F) {s : F}
    (H : SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => f p.1.1 p.1.2) s) :
    SumV v (fun χ => f χ (α - h χ)) s := by
  classical
  let e : X' ≃ {p : X' × X // h p.1 + p.2 = α} :=
    { toFun := fun χ => ⟨(χ, α - h χ), by simp⟩
      invFun := fun p => p.1.1
      left_inv := fun χ => rfl
      right_inv := fun p => Subtype.ext (Prod.ext rfl (sub_eq_of_eq_add' p.2.symm)) }
  intro q
  obtain ⟨S, hS⟩ := H q
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have := hS (T.map e.toEmbedding) (fun p hp => by
    rw [Finset.mem_map_equiv]
    exact hT (Finset.mem_map_of_mem _ hp))
  rw [Finset.sum_map] at this
  exact this

theorem val_sum_sub_coeff {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    {A : X' → F} {C : X → F}
    {a : AddMonoidAlgebra F X'} {c : AddMonoidAlgebra F X} {M N : ℚ}
    (hA : ∀ χ, (M : WithTop ℚ) ≤ v (A χ)) (hC : ∀ χ, (M : WithTop ℚ) ≤ v (C χ))
    (ha : ∀ χ, (N : WithTop ℚ) ≤ v (A χ - a.coeff χ)) (ha' : ∀ χ, v (A χ) ≤ v (a.coeff χ))
    (hc : ∀ χ, (N : WithTop ℚ) ≤ v (C χ - c.coeff χ))
    (T : Finset X') (hT : a.coeff.support ⊆ T) (α : X) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v (∑ χ ∈ T, A χ * C (α - h χ) -
      (AddMonoidAlgebra.mapDomainRingHom F h a * c).coeff α) := by
  rw [coeff_mapDomain_mul h a c T hT, ← Finset.sum_sub_distrib]
  exact v.map_le_sum fun χ _ => val_mul_sub_mul (ha _) (hc _) (hC _) ((hA _).trans (ha' _))

theorem val_coeff_of_sumV {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' →+ X)
    {A₁ A₂ : X' → F} {C₁ C₂ : X → F}
    {a₁ a₂ : AddMonoidAlgebra F X'} {c₁ c₂ : AddMonoidAlgebra F X} {M N : ℚ}
    (hA₁ : ∀ χ, (M : WithTop ℚ) ≤ v (A₁ χ)) (hA₂ : ∀ χ, (M : WithTop ℚ) ≤ v (A₂ χ))
    (hC₁ : ∀ χ, (M : WithTop ℚ) ≤ v (C₁ χ)) (hC₂ : ∀ χ, (M : WithTop ℚ) ≤ v (C₂ χ))
    (ha₁ : ∀ χ, (N : WithTop ℚ) ≤ v (A₁ χ - a₁.coeff χ)) (ha₁' : ∀ χ, v (A₁ χ) ≤ v (a₁.coeff χ))
    (ha₂ : ∀ χ, (N : WithTop ℚ) ≤ v (A₂ χ - a₂.coeff χ)) (ha₂' : ∀ χ, v (A₂ χ) ≤ v (a₂.coeff χ))
    (hc₁ : ∀ χ, (N : WithTop ℚ) ≤ v (C₁ χ - c₁.coeff χ))
    (hc₂ : ∀ χ, (N : WithTop ℚ) ≤ v (C₂ χ - c₂.coeff χ)) (α : X)
    (H : SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) :
    ((N + M : ℚ) : WithTop ℚ) ≤ v ((AddMonoidAlgebra.mapDomainRingHom F h a₁ * c₂ -
      AddMonoidAlgebra.mapDomainRingHom F h a₂ * c₁).coeff α) := by
  classical
  obtain ⟨S, hS⟩ := sumV_fibre h α (fun x y => A₁ x * C₂ y - A₂ x * C₁ y) H (N + M)
  have h0 := hS (S ∪ (a₁.coeff.support ∪ a₂.coeff.support)) Finset.subset_union_left
  have h1 := val_sum_sub_coeff h hA₁ hC₂ ha₁ ha₁' hc₂ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_left.trans Finset.subset_union_right) α
  have h2 := val_sum_sub_coeff h hA₂ hC₁ ha₂ ha₂' hc₁ (S ∪ (a₁.coeff.support ∪ a₂.coeff.support))
    (Finset.subset_union_right.trans Finset.subset_union_right) α
  have h3 := v.map_le_sub (v.map_le_sub h2 h1) h0
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring
end

end GlobalTheory.UT.CancelHom

namespace GlobalTheory.UT

theorem sumV_cancel_hom : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (h : X' →+ X), Function.Injective h → ∀ (A₁ A₂ B₁ B₂ : X' → F) (C₁ C₂ : X → F), NullV v A₁ → NullV v A₂ → NullV v B₁ → NullV v B₂ → NullV v C₁ → NullV v C₂ → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => A₁ p.1.1 * C₂ p.1.2 - A₂ p.1.1 * C₁ p.1.2) 0) → (∀ α, SumV v (fun p : {p : X' × X // h p.1 + p.2 = α} => B₁ p.1.1 * C₂ p.1.2 - B₂ p.1.1 * C₁ p.1.2) 0) → C₂ ≠ 0 → ∀ α, SumV v (fun χ : X' => B₁ χ * A₂ (α - χ) - B₂ χ * A₁ (α - χ)) 0 := by
  classical
  intro F _ v X X' _ _ _ _ _ _ h hinj A₁ A₂ B₁ B₂ C₁ C₂ nA₁ nA₂ nB₁ nB₂ nC₁ nC₂ HA HB hC α q
  obtain ⟨w, hw⟩ := exists_addGauss v X
  obtain ⟨χ₀, hχ₀⟩ := Function.ne_iff.mp hC
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (fun e => hχ₀ (v.top_iff.mp e) : v (C₂ χ₀) ≠ ⊤)
  obtain ⟨M₁, hM₁⟩ := nA₁.exists_lower
  obtain ⟨M₂, hM₂⟩ := nA₂.exists_lower
  obtain ⟨M₃, hM₃⟩ := nB₁.exists_lower
  obtain ⟨M₄, hM₄⟩ := nB₂.exists_lower
  obtain ⟨M₅, hM₅⟩ := nC₁.exists_lower
  obtain ⟨M₆, hM₆⟩ := nC₂.exists_lower
  obtain ⟨M, l1, l2, l3, l4, l5, l6⟩ : ∃ M : ℚ, M ≤ M₁ ∧ M ≤ M₂ ∧ M ≤ M₃ ∧ M ≤ M₄ ∧ M ≤ M₅ ∧ M ≤ M₆ :=
    ⟨min M₁ (min M₂ (min M₃ (min M₄ (min M₅ M₆)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  replace hM₁ := hM₁ M l1
  replace hM₂ := hM₂ M l2
  replace hM₃ := hM₃ M l3
  replace hM₄ := hM₄ M l4
  replace hM₅ := hM₅ M l5
  replace hM₆ := hM₆ M l6
  obtain ⟨N, n1, n2, n3⟩ : ∃ N : ℚ, m < N ∧ q + m ≤ M + (N + M) ∧ q ≤ N + M := by
    refine ⟨max (m + 1) (max (q + m - M - M) (q - M)), ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · have := (le_max_left (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
    · have := (le_max_right (q + m - M - M) (q - M)).trans (le_max_right (m + 1) _)
      linarith
  obtain ⟨a₁, ha₁, ha₁', -⟩ := nA₁.exists_trunc N
  obtain ⟨a₂, ha₂, ha₂', -⟩ := nA₂.exists_trunc N
  obtain ⟨b₁, hb₁, hb₁', -⟩ := nB₁.exists_trunc N
  obtain ⟨b₂, hb₂, hb₂', -⟩ := nB₂.exists_trunc N
  obtain ⟨c₁, hc₁, -, -⟩ := nC₁.exists_trunc N
  obtain ⟨c₂, hc₂, -, hc₂'⟩ := nC₂.exists_trunc N
  have EA := (hw _ _).mpr fun β =>
    CancelHom.val_coeff_of_sumV h hM₁ hM₂ hM₅ hM₆ ha₁ ha₁' ha₂ ha₂' hc₁ hc₂ β (HA β)
  have EB := (hw _ _).mpr fun β =>
    CancelHom.val_coeff_of_sumV h hM₃ hM₄ hM₅ hM₆ hb₁ hb₁' hb₂ hb₂' hc₁ hc₂ β (HB β)
  have push : ∀ (d : AddMonoidAlgebra F X') (g : WithTop ℚ),
      g ≤ w (AddMonoidAlgebra.mapDomainRingHom F h d) ↔ ∀ χ, g ≤ v (d.coeff χ) := by
    intro d g
    rw [hw, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.coeff_mapDomain]
    refine ⟨fun H χ => ?_, fun H β => ?_⟩
    · have := H (h χ)
      rwa [Finsupp.mapDomain_apply_of_injective hinj] at this
    · by_cases hβ : β ∈ Set.range h
      · obtain ⟨χ, rfl⟩ := hβ
        rw [Finsupp.mapDomain_apply_of_injective hinj]
        exact H χ
      · rw [Finsupp.mapDomain_of_notMem_range _ _ hβ, v.map_zero]
        exact le_top
  set P := AddMonoidAlgebra.mapDomainRingHom F h with hP
  have key : ((q + m : ℚ) : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) + w c₂ := by
    have e : P (b₁ * a₂ - b₂ * a₁) * c₂ =
        P a₂ * (P b₁ * c₂ - P b₂ * c₁) - P b₂ * (P a₁ * c₂ - P a₂ * c₁) := by
      rw [map_sub, map_mul, map_mul]; ring
    rw [← w.map_mul, e]
    refine (WithTop.coe_le_coe.mpr n2).trans ?_
    rw [WithTop.coe_add]
    refine w.map_le_sub ?_ ?_ <;> rw [w.map_mul]
    · exact add_le_add ((push _ _).mpr fun χ => (hM₂ χ).trans (ha₂' χ)) EB
    · exact add_le_add ((push _ _).mpr fun χ => (hM₄ χ).trans (hb₂' χ)) EA
  have hc : w c₂ ≤ (m : WithTop ℚ) := by
    have := (hw c₂ _).mp le_rfl χ₀
    rwa [hc₂' χ₀ (by rw [← hm]; exact WithTop.coe_lt_coe.mpr n1), ← hm] at this
  have key2 : (q : WithTop ℚ) ≤ w (P (b₁ * a₂ - b₂ * a₁)) := by
    have := key.trans (add_le_add le_rfl hc)
    rw [WithTop.coe_add] at this
    exact (WithTop.add_le_add_iff_right WithTop.coe_ne_top).mp this
  have key3 := (push _ _).mp key2 α
  refine ⟨b₁.coeff.support ∪ b₂.coeff.support, fun T hT => ?_⟩
  have h1 := CancelHom.val_sum_sub_coeff (AddMonoidHom.id X') hM₃ hM₂ hb₁ hb₁' ha₂ T
    (Finset.subset_union_left.trans hT) α
  have h2 := CancelHom.val_sum_sub_coeff (AddMonoidHom.id X') hM₄ hM₁ hb₂ hb₂' ha₁ T
    (Finset.subset_union_right.trans hT) α
  rw [AddMonoidAlgebra.mapDomainRingHom_id] at h1 h2
  simp only [RingHom.id_apply, AddMonoidHom.id_apply] at h1 h2
  have h3 := v.map_le_sub (v.map_le_sub ((WithTop.coe_le_coe.mpr n3).trans h2)
    ((WithTop.coe_le_coe.mpr n3).trans h1)) key3
  convert h3 using 2
  rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Finset.sum_sub_distrib]
  ring

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeComplexPointsProperClosedChartField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

noncomputable section

namespace GlobalTheory.ChernNull

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem chart_null_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ c : AlgChart p σ D, volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  intro k _ X _ p σ D Z hZ hgen c
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ σ.injective (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

end GlobalTheory.ChernNull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingMumfordLambdaSquareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_mumfordLambda_square : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ) (T : Over S) (x₁ x₂ y₁ y₂ : T ⟶ P.A), x₁ ^ n = 1 → x₂ ^ n = 1 → y₁ ^ n = 1 → y₂ ^ n = 1 → ∀ (c₁ c₂ : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L n x₁ y₂ c₁ → WeilIs P.A P.L n x₂ y₁ c₂ → WeilIs (G2 P.A) (abelian₂ P.A P.L) n (lift x₁ x₂) (lift y₁ y₂) (c₁ * c₂) := by
  first | exact @GlobalTheory.LamPairing.weilIs_lam | exact GlobalTheory.LamPairing.weilIs_lam | (intros; apply GlobalTheory.LamPairing.weilIs_lam <;> assumption)
end

