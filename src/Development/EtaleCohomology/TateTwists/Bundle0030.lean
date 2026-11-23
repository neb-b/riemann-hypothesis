module

public import Development.EtaleCohomology.TateTwists.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0011
public import Development.EtaleCohomology.TateTwists.Bundle0019
public import Development.EtaleCohomology.TateTwists.Bundle0005
public import Development.EtaleCohomology.TateTwists.Bundle0024

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.TtTensPrePf
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations
namespace TTP

variable {R : Type} [CommRing R]

noncomputable section

abbrev dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) : Sec (I.X s) U →ₗ[ULift.{1} R] Sec (I.X (s + 1)) U :=
  ((I.d s (s + 1)).hom.app (op U)).hom

theorem dI_dI (I : Cx R) (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U) : dI I U (s + 1) (dI I U s a) = 0 := by
  have h := congrArg (fun f => ((f.hom.app (op U)).hom a)) (I.d_comp_d s (s + 1) (s + 1 + 1))
  exact h.trans (by simp)

theorem dI_res (I : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s : ℤ) (a : Sec (I.X s) U) :
    dI I V s (((I.X s).obj.map g.op).hom a) = ((I.X (s + 1)).obj.map g.op).hom (dI I U s a) := by
  have h := congrArg (fun f => ModuleCat.Hom.hom f a) ((I.d s (s + 1)).hom.naturality g.op)
  exact h

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map (dI I U p.1.1) LinearMap.id) +
    ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) {q : ℤ × ℤ // q.1 + q.2 = w + 1}
        (fun q => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id (dI J U p.1.2)))

theorem dT_of (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s + 1, t), by omega⟩ (dI I U s a ⊗ₜ b) +
    (s.negOnePow : ℤ) • DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t + 1), by omega⟩ (a ⊗ₜ dI J U t b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), dT, DirectSum.toModule_lof]
  simp [DirectSum.lof_eq_of]

theorem dT_dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : (dT I J U (w + 1)).comp (dT I J U w) = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.zero_apply]
  rw [dT_of, map_add (f := _), map_zsmul, dT_of, dT_of]
  simp [dI_dI, Int.negOnePow_succ]

theorem res_of (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Tens.res (I := I) (J := J) g w (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) V ⊗[ULift.{1} R] Sec (J.X q.1.2) V)
      ⟨(s, t), h⟩ (((I.X s).obj.map g.op).hom a ⊗ₜ ((J.X t).obj.map g.op).hom b) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R), Tens.res, DirectSum.lmap_lof, TensorProduct.map_tmul, DirectSum.lof_eq_of]

theorem res_id (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens.res (I := I) (J := J) (𝟙 U) w = LinearMap.id := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, LinearMap.id_apply]
  rw [res_of]
  simp

theorem res_comp (I J : Cx R) {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (w : ℤ) :
    Tens.res (I := I) (J := J) (f ≫ g) w = Tens.res f w ∘ₗ Tens.res g w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, res_of, res_of]
  simp

theorem dT_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
  rw [res_of, dT_of, dT_of, map_add (f := _), map_zsmul, res_of, res_of, dI_res, dI_res]

def PF (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    apply ModuleCat.hom_ext
    simp only [unop_id, ModuleCat.hom_ofHom, ModuleCat.hom_id]
    exact res_id I J U.unop w
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp only [unop_comp, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact res_comp I J g.unop f.unop w

def dN (I J : Cx R) (w : ℤ) : PF I J w ⟶ PF I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := by
    apply ModuleCat.hom_ext
    simp only [PF, ModuleCat.hom_ofHom, ModuleCat.hom_comp]
    exact dT_res I J g.unop w

theorem dN_dN (I J : Cx R) (w : ℤ) : dN I J w ≫ dN I J (w + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext
  simp only [NatTrans.comp_app, dN, NatTrans.app_zero, ModuleCat.hom_zero]
  exact dT_dT I J U.unop w

def PC (I J : Cx R) : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (fun w => PF I J w) (fun w => dN I J w) (fun w => dN_dN I J w)

def tensPre (I J : Cx R) : TensPre I J where
  P := PC I J
  e U w := LinearEquiv.refl (ULift.{1} R) (Tens I J U w)
  nat g w x := rfl
  leibniz U s t w h a b := by
    simp only [PC]
    rw [CochainComplex.of_d]
    exact (dT_of I J U s t w h a b).trans (congrArg (HAdd.hAdd _) (Units.smul_def _ _).symm)

end

end TTP

theorem tt_tens_pre_of : tt_tens_pre := fun _ _ I J => ⟨TTP.tensPre I J⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TwpairTensUnivPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem secmap_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := rfl

theorem secmap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun k => k.hom x) (φ.hom.naturality g.op)
  exact this.symm

noncomputable def pairPost {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ ((u.f w).hom.app (op U)).hom
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    rw [← μ.nat g s t w h a b]
    exact secmap_res (u.f w) g _
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply]
    have hc : Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) =
        Sec.map (u.f (w + 1)) (Sec.map (K.d w (w + 1)) (μ.mul U s t w h a b)) := by
      rw [secmap_comp, secmap_comp, u.comm]
    show Sec.map (K'.d w (w + 1)) (Sec.map (u.f w) (μ.mul U s t w h a b)) = _
    rw [hc, μ.leibniz U s t w h a b]
    show Sec.map (u.f (w + 1)) _ = Sec.map (u.f (w + 1)) _ + _ • Sec.map (u.f (w + 1)) _
    rw [Sec.map, map_add (f := _), map_zsmul_unit]

def twpair_tens_univ_uniq : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K'), τ.Compat ν f g u → τ.Compat ν f g u' → u = u'

def twpair_tens_univ_ex : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃ u : K ⟶ K', τ.Compat ν f g u

def twpair_tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0

theorem pairPost_compat {R : Type} [CommRing R] {I J K K' : Cx R} (μ : Pair I J K) (u : K ⟶ K') :
    μ.Compat (pairPost μ u) (𝟙 I) (𝟙 J) u := by
  intro U s t w h a b
  rfl

theorem lift_comp_eq {R : Type} [CommRing R] {I J K I' J' K' : Cx R} (τ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u u' : K ⟶ K')
    (hu : τ.Compat ν f g u) (hu' : τ.Compat ν f g u') (V : Scheme.{0}) (w : ℤ) (x : Tens I J V w) :
    Sec.map (u.f w) (τ.lift V w x) = Sec.map (u'.f w) (τ.lift V w x) := by
  classical
  have key : ((u.f w).hom.app (op V)).hom ∘ₗ τ.lift V w = ((u'.f w).hom.app (op V)).hom ∘ₗ τ.lift V w := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    exact (hu V _ _ _ p.2 a b).trans (hu' V _ _ _ p.2 a b).symm
  exact congrArg (fun k => k x) key

theorem tens_univ_uniq_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_uniq := by
  intro R _ I J K τ hτ I' J' K' ν f g u u' hu hu'
  ext w U y
  apply hsep R (K'.X w) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop w y) ?_
  rintro V r ⟨x, hx⟩
  rw [secmap_res, secmap_res, ← hx]
  exact lift_comp_eq τ ν f g u u' hu hu' V w x

theorem sec_zero_of_isZero {R : Type} [CommRing R] {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h := hF.eq_of_src (𝟙 F) 0
  have : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [h]
  exact this

theorem isZero_of_sec {R : Type} [CommRing R] {F : Shv R} (h : ∀ (U : Scheme.{0}) (x : Sec F U), x = 0) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U y
  exact (h U.unop y).trans (h U.unop _).symm

theorem tens_univ_ge_of (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) : twpair_tens_univ_ge := by
  intro R _ I J K τ hτ hI hJ
  have hK : ∀ w : ℤ, w < 0 → IsZero (K.X w) := by
    intro w hw
    apply isZero_of_sec
    intro U y
    apply hsep R (K.X w) U
    refine TensLocbij.loc_mono (hτ.1 U w y) ?_
    rintro V r ⟨x, hx⟩
    rw [← hx]
    classical
    have hl : τ.lift V w = 0 := by
      apply DirectSum.linearMap_ext
      intro p
      apply TensorProduct.ext'
      intro a b
      simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.zero_apply]
      rcases lt_or_ge p.1.1 0 with hs | hs
      · rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE I 0 p.1.1 hs) a, map_zero, LinearMap.zero_apply]
      · have ht : p.1.2 < 0 := by have := p.2; omega
        rw [sec_zero_of_isZero (CochainComplex.isZero_of_isStrictlyGE J 0 p.1.2 ht) b, map_zero]
    rw [hl, LinearMap.zero_apply]
    exact (map_zero _).symm
  exact ⟨fun i hi => hK i ((ComplexShape.notMem_range_embeddingUpIntGE_iff (p := 0) i).1 hi)⟩

theorem etale_sheaf_sections_separated_holds : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep := by
  intro R _ F U a b hab
  obtain ⟨S, hS, hP⟩ := hab
  have h1 : Presheaf.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property
  have h2 := (isSheaf_iff_isSheaf_of_type _ _).1 h1
  exact (h2 S hS).isSeparatedFor.ext fun V g hg => hP V g hg

def twpair_tens_univ_exdeg : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → ∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (w : ℤ), ∃ φ : K.X w ⟶ K'.X w, ∀ (U : Scheme.{0}) (s t : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map φ (τ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

theorem tens_univ_ex_of (hdeg : twpair_tens_univ_exdeg) : twpair_tens_univ_ex := by
  intro R _ I J K τ hτ I' J' K' ν f g
  choose φ hφ using hdeg R τ hτ ν f g
  have hsep := etale_sheaf_sections_separated_holds
  refine ⟨⟨φ, ?_⟩, fun U s t w h a b => hφ w U s t h a b⟩
  rintro i j (hij : i + 1 = j)
  subst hij
  ext U y
  apply hsep R (K'.X (i + 1)) U.unop
  refine TensLocbij.loc_mono (hτ.1 U.unop i y) ?_
  rintro V r ⟨x, hx⟩
  show Sec.res r (Sec.map (φ i ≫ K'.d i (i + 1)) y) = Sec.res r (Sec.map (K.d i (i + 1) ≫ φ (i + 1)) y)
  rw [secmap_res, secmap_res, ← hx]
  classical
  have key : ((K.d i (i + 1) ≫ φ (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i =
      ((φ i ≫ K'.d i (i + 1)).hom.app (op V)).hom ∘ₗ τ.lift V i := by
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    have e1 : Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (φ (i + 1)) (Sec.map (K.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    have e2 : Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) =
        Sec.map (K'.d i (i + 1)) (Sec.map (φ i) (τ.mul V p.1.1 p.1.2 i p.2 a b)) := rfl
    change Sec.map (K.d i (i + 1) ≫ φ (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b) = Sec.map (φ i ≫ K'.d i (i + 1)) (τ.mul V p.1.1 p.1.2 i p.2 a b)
    have h1 := hφ (i + 1) V (p.1.1 + 1) p.1.2 (by have := p.2; omega) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) b
    have h2 := hφ (i + 1) V p.1.1 (p.1.2 + 1) (by have := p.2; omega) a (Sec.map (J.d p.1.2 (p.1.2 + 1)) b)
    have hf : Sec.map (I'.d p.1.1 (p.1.1 + 1)) (Sec.map (f.f p.1.1) a) = Sec.map (f.f (p.1.1 + 1)) (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) := by
      rw [secmap_comp, secmap_comp, f.comm]
    have hg : Sec.map (J'.d p.1.2 (p.1.2 + 1)) (Sec.map (g.f p.1.2) b) = Sec.map (g.f (p.1.2 + 1)) (Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
      rw [secmap_comp, secmap_comp, g.comm]
    rw [e1, e2, τ.leibniz, hφ i, ν.leibniz, hf, hg]
    simp only [Sec.map, map_add (f := _), map_zsmul_unit] at h1 h2 ⊢
    rw [h1, h2]
  exact (congrArg (fun k => k x) key).symm

theorem twpair_tens_univ_of (hdeg : twpair_tens_univ_exdeg) :
    LateralTheory.EtaleFoundations.twpair_tens_univ := by
  have hsep := etale_sheaf_sections_separated_holds
  have hex := tens_univ_ex_of hdeg
  intro R _ I J K τ hτ
  refine ⟨?_, tens_univ_ge_of hsep R τ hτ, fun u => ⟨pairPost τ u, pairPost_compat τ u⟩⟩
  intro I' J' K' ν f g
  obtain ⟨u, hu⟩ := hex R τ hτ ν f g
  exact ⟨u, hu, fun u' hu' => tens_univ_uniq_of hsep R τ hτ ν f g u' u hu' hu⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.acycIffPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.acycIffPf

variable {R : Type} [CommRing R]

abbrev ev (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U)

theorem app_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) (U : Scheme.{0}) (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun f => f.hom x) (φ.hom.naturality g.op)

theorem iCycles_inj (S : ShortComplex (Shv R)) (U : Scheme.{0}) :
    Function.Injective (Sec.map S.iCycles (U := U)) := by
  have : Mono ((ev U).map S.iCycles) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem iCycles_surj (S : ShortComplex (Shv R)) (U : Scheme.{0}) (z : Sec S.X₂ U) (hz : Sec.map S.g z = 0) :
    ∃ c : Sec S.cycles U, Sec.map S.iCycles c = z := by
  let S' : ShortComplex (Shv R) := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hS' : S'.Exact := S'.exact_of_f_is_kernel S.cyclesIsKernel
  have hE : (S'.map (ev U)).Exact := hS'.map_of_mono_of_preservesKernel (ev U) (inferInstanceAs (Mono S.iCycles)) inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).1 hE z hz

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔
    ∀ (U : Scheme.{0}) (z : Sec S.X₂ U), Sec.map S.g z = 0 →
      Loc U fun V g => ∃ y : Sec S.X₁ V, Sec.map S.f y = Sec.res g z := by
  rw [S.exact_iff_epi_toCycles, ← Sheaf.isLocallySurjective_iff_epi' _ S.toCycles]
  constructor
  · intro h U z hz
    obtain ⟨c, rfl⟩ := iCycles_surj S U z hz
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} S.toCycles.hom (U := op U) c, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h1 : Sec.map S.f t = Sec.map S.iCycles (Sec.map S.toCycles t) := by
      rw [← app_comp, S.toCycles_i]
    rw [h1, ← map_res]
    exact congrArg _ ht
  · intro h
    constructor
    intro U c
    obtain ⟨Sv, hSv, hP⟩ := h U (Sec.map S.iCycles c) (by rw [← app_comp, S.iCycles_g]; rfl)
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hSv
    intro V g hg
    obtain ⟨y, hy⟩ := hP V g hg
    refine ⟨y, iCycles_inj S V ?_⟩
    change Sec.map S.iCycles (Sec.map S.toCycles y) = Sec.map S.iCycles (Sec.res g c)
    rw [← app_comp, S.toCycles_i, hy, map_res]

end LateralTheory.EtaleFoundations.acycIffPf

open LateralTheory.EtaleFoundations.acycIffPf in
theorem LateralTheory.EtaleFoundations.acyc.acycIff_of : LateralTheory.EtaleFoundations.acyc.acycIff := by
  intro R _ C
  unfold LateralTheory.EtaleFoundations.acyc.LocAcyc
  constructor
  · intro h U n z hz
    have := (HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)).1 (h n)
    exact (exact_iff _).1 this U z hz
  · intro h n
    rw [HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)]
    exact (exact_iff _).2 fun U z hz => h U n z hz
end

-- bundled from Development.EtaleCohomology.TateTwists.columnPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

theorem loc_top (U : Scheme.{0}) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) :
    Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h1 : Loc U P) (h2 : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := h1
  obtain ⟨T, hT, hQ⟩ := h2
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  choose T hT hQ using hPQ
  refine ⟨Sieve.bind S.arrows fun V g hg => T V g (hP V g hg), Scheme.etaleTopology.bind_covering hS
    (fun V g hg => hT V g (hP V g hg)), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact hQ V g (hP V g hg) W k hk

theorem loc_finset {ι : Type*} (s : Finset ι) {U : Scheme.{0}} {P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ i ∈ s, Loc U (P i)) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_top U (by simp)
  | insert a s ha ih =>
    have := loc_and (h a (by simp)) (ih fun i hi => h i (by simp [hi]))
    exact loc_mono this fun V g ⟨h1, h2⟩ i hi => by
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact h1
      · exact h2 i hi

theorem loc_empty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun _ _ h => h.elim⟩

def lift : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) →
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) →
    ∀ (F G : Shv R) (δ : F ⟶ G) (U : Scheme.{0}) (x : Sec F U ⊗[ULift.{1} R] Sec M U),
      TensorProduct.map (δ.hom.app (op U)).hom LinearMap.id x = 0 →
      Loc U fun V g => ∃ x' : Sec F V ⊗[ULift.{1} R] P.obj (op V),
        TensorProduct.map (δ.hom.app (op V)).hom LinearMap.id x' = 0 ∧
        TensorProduct.map LinearMap.id (φ.app (op V)).hom x' = TensorProduct.map (F.obj.map g.op).hom (M.obj.map g.op).hom x

def kill : Prop :=
  ∀ (R : Type) [CommRing R] (C : Cx R) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)),
    LateralTheory.EtaleFoundations.acyc.LocAcyc C → ∀ (V : Scheme.{0}) (s : ℤ) (x' : Sec (C.X s) V ⊗[ULift.{1} R] P.obj (op V)),
      Module.Flat (ULift.{1} R) (P.obj (op V)) →
      TensorProduct.map ((C.d s (s + 1)).hom.app (op V)).hom LinearMap.id x' = 0 →
      Loc V fun W k => ∃ y : Sec (C.X (s - 1)) W ⊗[ULift.{1} R] P.obj (op W),
        TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id y =
          TensorProduct.map ((C.X s).obj.map k.op).hom (P.map k.op).hom x'

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.acyc.column_of_cut (hL : lift) (hK : kill) : LateralTheory.EtaleFoundations.acyc.column := by
  intro R _ C J hJ hC U s t x hx
  obtain ⟨P, φ, hsurj, hker, hflat⟩ := hJ t
  refine loc_bind (hL R (J.X t) P φ hsurj hker (C.X s) (C.X (s + 1)) (C.d s (s + 1)) U x hx) ?_
  rintro V g ⟨x', hx'0, hx'⟩
  by_cases hV : Nonempty V
  · refine loc_mono (hK R C P hC V s x' (hflat V hV) hx'0) ?_
    rintro W k ⟨y, hy⟩
    refine ⟨TensorProduct.map LinearMap.id (φ.app (op W)).hom y, ?_⟩
    have e1 : TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id
        (TensorProduct.map LinearMap.id (φ.app (op W)).hom y) =
        TensorProduct.map LinearMap.id (φ.app (op W)).hom
          (TensorProduct.map ((C.d (s - 1) s).hom.app (op W)).hom LinearMap.id y) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
      rfl
    rw [e1, hy, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have e2 : (TensorProduct.map ((C.X s).obj.map (k ≫ g).op).hom ((J.X t).obj.map (k ≫ g).op).hom) x =
        TensorProduct.map ((C.X s).obj.map k.op).hom ((J.X t).obj.map k.op).hom
          (TensorProduct.map ((C.X s).obj.map g.op).hom ((J.X t).obj.map g.op).hom x) := by
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, op_comp, Functor.map_comp, Functor.map_comp]
      rfl
    rw [e2, ← hx', ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    congr 2
    have := φ.naturality k.op
    exact congrArg ModuleCat.Hom.hom this
  · have : IsEmpty V := not_nonempty_iff.1 hV
    exact loc_empty V _

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.kill_of : kill := by
  classical
  intro R _ C P hC V s x' hflat hx'
  set d := ((C.d s (s + 1)).hom.app (op V)).hom
  have hex := Module.Flat.rTensor_exact (M := P.obj (op V)) (LinearMap.exact_subtype_ker_map d)
  obtain ⟨w, hw⟩ := (hex x').1 hx'
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset w
  have hloc : ∀ i ∈ S, Loc V fun W k => ∃ y : Sec (C.X (s - 1)) W,
      Sec.map (C.d (s - 1) s) y = Sec.res k (i.1 : Sec (C.X s) V) := fun i _ =>
    hC V s (i.1 : Sec (C.X s) V) i.1.2
  refine loc_mono (loc_finset S hloc) ?_
  intro W k hk
  choose y hy using hk
  refine ⟨∑ i ∈ S.attach, y i.1 i.2 ⊗ₜ (P.map k.op).hom i.1.2, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← hw, hS, map_sum, map_sum]
  rw [← Finset.sum_attach S]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.id_apply]
  congr 1
  exact hy i.1 i.2
end

