module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.res_lof {I J : _root_.GlobalTheory.EtC.Cx R} {V U : Scheme.{0}}
    (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U) (b : _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U) :
    _root_.GlobalTheory.EtC.Tens.res g w
      (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U)
        p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) V ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) V) p
        (_root_.GlobalTheory.EtC.Sec.res g a ⊗ₜ _root_.GlobalTheory.EtC.Sec.res g b) := by
  unfold _root_.GlobalTheory.EtC.Tens.res
  rw [DirectSum.lmap_lof, TensorProduct.map_tmul]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.sres_id {F : _root_.GlobalTheory.EtC.Shv R} {U : Scheme.{0}}
    (a : _root_.GlobalTheory.EtC.Sec F U) : _root_.GlobalTheory.EtC.Sec.res (𝟙 U) a = a := by
  unfold _root_.GlobalTheory.EtC.Sec.res
  simp

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.sres_comp {F : _root_.GlobalTheory.EtC.Shv R} {W V U : Scheme.{0}}
    (g : W ⟶ V) (f : V ⟶ U) (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res (g ≫ f) a =
      _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.res f a) := by
  unfold _root_.GlobalTheory.EtC.Sec.res
  simp

def pre (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_)
    simp [res_lof, sres_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_)
    simp [res_lof, sres_comp]

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.smap_res {F G : _root_.GlobalTheory.EtC.Shv R} (φ : F ⟶ G)
    {V U : Scheme.{0}} (g : V ⟶ U) (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.map φ a) =
      _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.Sec.res g a) := by
  unfold _root_.GlobalTheory.EtC.Sec.res _root_.GlobalTheory.EtC.Sec.map
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp; omega⟩ ∘ₗ
      TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id) +
    ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.dT_lof {I J : _root_.GlobalTheory.EtC.Cx R} (U : Scheme.{0})
    (s t w : ℤ) (h : s + t = w) (a : _root_.GlobalTheory.EtC.Sec (I.X s) U)
    (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.TensEx.dT I J U w (DirectSum.lof (ULift.{1} R) _
      (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U)
        ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
        ⟨(s + 1, t), by simp; omega⟩
        (_root_.GlobalTheory.EtC.Sec.map (I.d s (s + 1)) a ⊗ₜ b) +
    (s.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
        ⟨(s, t + 1), by simp; omega⟩
        (a ⊗ₜ _root_.GlobalTheory.EtC.Sec.map (J.d t (t + 1)) b) := by
  unfold _root_.GlobalTheory.EtC.TensEx.dT
  rw [DirectSum.toModule_lof]
  rfl

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def D (I J : Cx R) (w : ℤ) : pre I J w ⟶ pre I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_)
    simp only [pre, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    rw [res_lof, dT_lof, dT_lof, map_add (f := _), map_zsmul, res_lof, res_lof, smap_res, smap_res]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem sec_map_d_map_d_eq_zero (K : _root_.GlobalTheory.EtC.Cx R) {U : Scheme.{0}}
    (i j k : ℤ) (a : _root_.GlobalTheory.EtC.Sec (K.X i) U) :
    _root_.GlobalTheory.EtC.Sec.map (K.d j k) (_root_.GlobalTheory.EtC.Sec.map (K.d i j) a) = 0 := by
  have key := congrArg (fun f : K.X i ⟶ K.X k => (f.hom.app (op U)).hom a) (K.d_comp_d i j k)
  exact key

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.D_comp (I J : _root_.GlobalTheory.EtC.Cx R) (w : ℤ) :
    _root_.GlobalTheory.EtC.TensEx.D I J w ≫
      _root_.GlobalTheory.EtC.TensEx.D I J (w + 1) = 0 := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (DirectSum.linearMap_ext _
    fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  show _root_.GlobalTheory.EtC.TensEx.dT I J U.unop (w + 1) (_root_.GlobalTheory.EtC.TensEx.dT I J U.unop w
    (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U.unop ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U.unop)
      ⟨(s, t), h⟩ (a ⊗ₜ b))) = 0
  rw [_root_.GlobalTheory.EtC.TensEx.dT_lof, map_add (f := _), map_zsmul, _root_.GlobalTheory.EtC.TensEx.dT_lof,
    _root_.GlobalTheory.EtC.TensEx.dT_lof, sec_map_d_map_d_eq_zero, sec_map_d_map_d_eq_zero,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, map_zero]
  simp [Int.negOnePow_succ, smul_add]

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def cx (I J : Cx R) : Cx R :=
  CochainComplex.of (fun w => (presheafToSheaf Scheme.etaleTopology _).obj (pre I J w))
    (fun w => (presheafToSheaf Scheme.etaleTopology _).map (D I J w))
    (fun w => by rw [← Functor.map_comp, D_comp, Functor.map_zero])

def toS (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((cx I J).X w) U :=
  ((toSheafify Scheme.etaleTopology (pre I J w)).app (op U)).hom

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.toS_res (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}}
    (g : V ⟶ U) (w : ℤ) (x : _root_.GlobalTheory.EtC.Tens I J U w) :
    _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.TensEx.toS I J U w x) =
      _root_.GlobalTheory.EtC.TensEx.toS I J V w (_root_.GlobalTheory.EtC.Tens.res g w x) := by
  have key := congrArg (fun f => ModuleCat.Hom.hom f x)
    ((toSheafify Scheme.etaleTopology (_root_.GlobalTheory.EtC.TensEx.pre I J w)).naturality g.op)
  exact key.symm

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.d_toS (I J : _root_.GlobalTheory.EtC.Cx R)
    (U : Scheme.{0}) (w : ℤ) (x : _root_.GlobalTheory.EtC.Tens I J U w) :
    _root_.GlobalTheory.EtC.Sec.map ((_root_.GlobalTheory.EtC.TensEx.cx I J).d w (w + 1))
        (_root_.GlobalTheory.EtC.TensEx.toS I J U w x) =
      _root_.GlobalTheory.EtC.TensEx.toS I J U (w + 1) (_root_.GlobalTheory.EtC.TensEx.dT I J U w x) := by
  have hd : (_root_.GlobalTheory.EtC.TensEx.cx I J).d w (w + 1) = (presheafToSheaf Scheme.etaleTopology _).map
      (_root_.GlobalTheory.EtC.TensEx.D I J w) := by
    unfold _root_.GlobalTheory.EtC.TensEx.cx
    simp
  have key := congrArg (fun f => ModuleCat.Hom.hom (f.app (op U)) x)
    (toSheafify_naturality Scheme.etaleTopology (_root_.GlobalTheory.EtC.TensEx.D I J w))
  rw [hd]
  exact key.symm

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def pair (I J : Cx R) : Pair I J (cx I J) where
  mul U s t w h := (TensorProduct.mk (ULift.{1} R) _ _).compr₂ (toS I J U w ∘ₗ
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [toS_res, res_lof]
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [d_toS, dT_lof, map_add (f := _), map_zsmul, Units.smul_def]

end GlobalTheory.EtC.TensEx


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
theorem _root_.GlobalTheory.EtC.tensor_exists :
    ∀ (R : Type) [CommRing R] (I J : _root_.GlobalTheory.EtC.Cx R),
      ∃ (K : _root_.GlobalTheory.EtC.Cx R) (τ : _root_.GlobalTheory.EtC.Pair I J K), τ.IsTensor := by
  intro R _ I J
  refine ⟨_root_.GlobalTheory.EtC.TensEx.cx I J, _root_.GlobalTheory.EtC.TensEx.pair I J, ?_⟩
  have hlift : ∀ (U : Scheme.{0}) (w : ℤ),
      (_root_.GlobalTheory.EtC.TensEx.pair I J).lift U w =
        _root_.GlobalTheory.EtC.TensEx.toS I J U w := by
    intro U w
    refine DirectSum.linearMap_ext _ fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_
    unfold _root_.GlobalTheory.EtC.Pair.lift
    rw [LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    rfl
  unfold _root_.GlobalTheory.EtC.Pair.IsTensor
  simp only [hlift]
  exact ⟨fun U w y =>
      (_root_.GlobalTheory.EtC.toSheafify_loc_bij_lift R (_root_.GlobalTheory.EtC.TensEx.pre I J w)).1 U y,
    fun U w x hx =>
      (_root_.GlobalTheory.EtC.toSheafify_loc_bij_lift R (_root_.GlobalTheory.EtC.TensEx.pre I J w)).2.1 U x hx⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeMapModOfPerfectAlternating
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Module

theorem exists_lattice_map_of_symplecticBasis {La : Type} [AddCommGroup La] {g : ℕ}
    (EF : LinearMap.BilinForm ℤ La) (hB : EF.IsAlt) (b : Basis (Fin g ⊕ Fin g) ℤ La)
    (d : Fin g → ℤ) (hb : IsSymplecticBasisOfType EF b d) (M : ℕ) (u t : Fin g → ℤ)
    (ht : ∀ i, u i * d i = 1 + (M : ℤ) * t i) :
    ∃ L : (Fin g ⊕ Fin g → ℤ) →+ La,
      (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
      ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  classical
  let w : Fin g ⊕ Fin g → ℤ := Sum.elim u 1
  have hw : ∀ j, IsCoprime (w j) (M : ℤ) := by
    rintro (i | i)
    · exact ⟨d i, -t i, by simp only [w, Sum.elim_inl]; linear_combination ht i⟩
    · exact isCoprime_one_left
  let S : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] (Fin g ⊕ Fin g → ℤ) :=
    { toFun := fun a j => w j * a j
      map_add' := fun a c => by funext j; simp [mul_add]
      map_smul' := fun r a => by funext j; simp; ring }
  let L : (Fin g ⊕ Fin g → ℤ) →+ La := (b.equivFun.symm.toLinearMap ∘ₗ S).toAddMonoidHom
  have hrepr : ∀ v j, b.repr (b.equivFun.symm v) j = v j := fun v j => by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hL : ∀ a j, b.repr (L a) j = w j * a j := fun a j => hrepr (S a) j
  refine ⟨L, fun a => ⟨?_, ?_⟩, fun x => ?_, fun a c => ?_⟩
  · rintro ⟨y, hy⟩
    have hdiv : ∀ j, (M : ℤ) ∣ a j := by
      intro j
      have := hL a j
      rw [hy, map_nsmul] at this
      have h2 : (M : ℤ) ∣ w j * a j := ⟨b.repr y j, by rw [← this]; simp⟩
      exact (hw j).symm.dvd_of_dvd_mul_left h2
    choose c hc using hdiv
    exact ⟨c, funext fun j => by simp [hc j]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨L c, map_nsmul L M c⟩
  · refine ⟨Sum.elim (fun i => d i * b.repr x (Sum.inl i)) (fun i => b.repr x (Sum.inr i)),
      b.equivFun.symm (Sum.elim (fun i => -(t i * b.repr x (Sum.inl i))) 0), ?_⟩
    apply b.repr.injective
    ext j
    rw [map_add (f := _), Finsupp.add_apply, hL, map_nsmul, Finsupp.smul_apply]
    rcases j with i | i
    · simp only [w, Sum.elim_inl, hrepr, nsmul_eq_mul]
      linear_combination (-(b.repr x (Sum.inl i))) * ht i
    · simp [w, hrepr]
  · refine ⟨∑ i, t i * (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)), ?_⟩
    rw [hb.apply_eq_sum hB, omegaStd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hL, w, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_mul]
    linear_combination (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)) * ht i

theorem exists_lattice_map_mod_of_perfect : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La),
  (∀ x, EF x x = 0) → Function.Injective EF → ∀ (e M : ℕ), (∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f) → M.Coprime e →
  ∃ L : (Fin (Module.finrank ℤ La / 2) ⊕ Fin (Module.finrank ℤ La / 2) → ℤ) →+ La,
    (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
    ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  intro La _ _ _ EF halt hinj e M hperf hcop
  have hB : EF.IsAlt := halt
  obtain ⟨g, b, d, hb, -, -⟩ := exists_isSymplecticBasisOfType_pos hB hinj
  have hg : Module.finrank ℤ La / 2 = g := by
    rw [IsSymplecticBasisOfType.finrank_eq b, Fintype.card_fin]; omega
  rw [hg]
  have hde : ∀ i, d i ∣ (e : ℤ) := by
    intro i
    obtain ⟨x, hx⟩ := hperf (b.coord (Sum.inr i))
    have h1 := hb.apply_right x i
    rw [hx] at h1
    simp only [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      nsmul_eq_mul, mul_one] at h1
    exact ⟨b.repr x (Sum.inl i), by rw [h1, mul_comm]⟩
  have hc : ∀ i, IsCoprime (M : ℤ) (d i) := fun i =>
    (Nat.isCoprime_iff_coprime.2 hcop).of_isCoprime_of_dvd_right (hde i)
  choose p u hpu using hc
  exact exists_lattice_map_of_symplecticBasis EF hB b d hb M u (fun i => -p i)
    (fun i => by linear_combination hpu i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentConstantTermFormFunctionField
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
private theorem linearIndependent_laurentMonomials {k F ι : Type} [Field k] [Field F] [Algebra k F]
    [Fintype ι] (y : ι → F) (hy : AlgebraicIndependent k y) (hy0 : ∀ i, y i ≠ 0) :
    LinearIndependent k (fun n : ι → ℤ => ∏ i, y i ^ n i) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg n hn
  set B : ℤ := ∑ m ∈ s, ∑ i, |m i| with hBdef
  have hB : ∀ m ∈ s, ∀ i, 0 ≤ m i + B := by
    intro m hm i
    have h1 : |m i| ≤ ∑ i, |m i| :=
      Finset.single_le_sum (f := fun i => |m i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i, |m i| ≤ B :=
      Finset.single_le_sum (f := fun m : ι → ℤ => ∑ i, |m i|)
        (fun m _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hm
    linarith [neg_abs_le (m i)]
  let e : (ι → ℤ) → (ι →₀ ℕ) := fun m => Finsupp.equivFunOnFinite.symm (fun i => (m i + B).toNat)
  have he : Set.InjOn e s := by
    intro m hm m' hm' h
    funext i
    have h' := congrArg (fun f : ι →₀ ℕ => f i) h
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h'
    have := Int.toNat_of_nonneg (hB m hm i)
    have := Int.toNat_of_nonneg (hB m' hm' i)
    omega
  set P : F := ∏ i, y i ^ B with hPdef
  have hkey : ∀ m ∈ s, MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k)) =
      P * ∏ i, y i ^ m i := by
    intro m hm
    rw [MvPolynomial.aeval_monomial, map_one, one_mul,
      Finsupp.prod_fintype _ _ (fun i => pow_zero _), hPdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_add₀ (hy0 i), ← zpow_natCast]
    congr 1
    simp only [e, Finsupp.coe_equivFunOnFinite_symm]
    rw [Int.toNat_of_nonneg (hB m hm i)]
    ring
  have hw : LinearIndependent k (fun a : ι →₀ ℕ => MvPolynomial.aeval y (MvPolynomial.monomial a (1 : k))) := by
    have := (MvPolynomial.basisMonomials ι k).linearIndependent.map'
      (MvPolynomial.aeval y).toLinearMap (LinearMap.ker_eq_bot.mpr hy)
    simpa only [MvPolynomial.coe_basisMonomials, Function.comp_def, AlgHom.toLinearMap_apply] using this
  have hws : LinearIndependent k
      (fun m : s => MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))) :=
    hw.comp (fun m : s => e m) (fun a b h => Subtype.ext (he a.2 b.2 h))
  rw [Fintype.linearIndependent_iff] at hws
  refine hws (fun m => g m) ?_ ⟨n, hn⟩
  calc ∑ m : s, g m • MvPolynomial.aeval y (MvPolynomial.monomial (e m) (1 : k))
      = ∑ m : s, P * (g m • ∏ i, y i ^ (m : ι → ℤ) i) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hkey m m.2, mul_smul_comm]
    _ = P * ∑ m ∈ s, g m • ∏ i, y i ^ m i := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort s (fun m => g m • ∏ i, y i ^ m i)]
    _ = 0 := by rw [hg, mul_zero]

open KaehlerDifferential in
private theorem prod_zpow_eq_prod_div_zpow_of_sum_eq_zero {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → F)
    (hx : ∀ i, x i ≠ 0) (m : Fin (d + 1) → ℤ) (hm : ∑ j, m j = 0) :
    ∏ j, x j ^ m j = ∏ i : Fin d, (x i.succ / x 0) ^ m i.succ := by
  have h0 : m 0 = -∑ i : Fin d, m i.succ := by
    rw [Fin.sum_univ_succ] at hm
    linarith
  have hpow : ∀ s : Finset (Fin d), ∏ i ∈ s, x 0 ^ m i.succ = x 0 ^ ∑ i ∈ s, m i.succ := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (hx 0)]
  rw [Fin.prod_univ_succ, h0]
  simp_rw [div_zpow]
  rw [Finset.prod_div_distrib, hpow, zpow_neg, div_eq_mul_inv, mul_comm]


open KaehlerDifferential in
theorem _root_.GlobalTheory.exists_isRes : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F),
    _root_.GlobalTheory.PD.IsPd k x → ∃ ρ : F →ₗ[k] k, _root_.GlobalTheory.PD.IsRes k x ρ := by
  intro k _ F _ _ d x hx
  classical
  let v : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} → F := fun m => ∏ j, x j ^ m.1 j
  have hv : LinearIndependent k v := by
    have hL := linearIndependent_laurentMonomials (k := k) (fun i : Fin d => x i.succ / x 0)
      hx.indep
      (fun i => div_ne_zero (hx.ne _) (hx.ne 0))
    have hinj : Function.Injective
        (fun m : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} => fun i : Fin d => m.1 i.succ) := by
      intro a b h
      apply Subtype.ext
      have hs : ∀ i : Fin d, a.1 i.succ = b.1 i.succ := fun i => congrFun h i
      have ha := a.2
      have hb := b.2
      rw [Fin.sum_univ_succ] at ha hb
      have hsum : ∑ i : Fin d, a.1 i.succ = ∑ i : Fin d, b.1 i.succ :=
        Finset.sum_congr rfl fun i _ => hs i
      funext j
      refine Fin.cases ?_ (fun i => hs i) j
      linarith
    have := hL.comp _ hinj
    convert this using 1
    funext m
    exact prod_zpow_eq_prod_div_zpow_of_sum_eq_zero x hx.ne m.1 m.2
  let z₀ : {m : Fin (d + 1) → ℤ // ∑ j, m j = 0} := ⟨0, by simp⟩
  have h1 : v z₀ = 1 := by simp [v, z₀]
  have hnot := hv.notMem_span_image (s := {z | z ≠ z₀}) (x := z₀) (by simp)
  rw [h1] at hnot
  obtain ⟨f, hf1, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨(f 1)⁻¹ • f, ?_⟩
  delta _root_.GlobalTheory.PD.IsRes
  refine ⟨?_, ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf1]
  · intro m hm hm0
    have hmem : ∏ j, x j ^ m j ∈ Submodule.span k (v '' {z | z ≠ z₀}) :=
      Submodule.subset_span ⟨⟨m, hm⟩, fun h => hm0 (congrArg Subtype.val h), rfl⟩
    have hzero : f (∏ j, x j ^ m j) = 0 := by
      exact LinearMap.mem_ker.mp ((LinearMap.le_ker_iff_map.mpr hf) hmem)
    rw [LinearMap.smul_apply, hzero, smul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalBetweenStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_local_between_alt : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i →
    ∀ (L : Type) [Field L] [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
      [Algebra.IsSeparable (FractionRing A) L],
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp j = i ∧
      ∃ κ : L →+* FractionRing A₁,
        κ.comp ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))) =
          (algebraMap A₁ (FractionRing A₁)).comp j := by
  first | (exact @GlobalTheory.LocAcycEmbed.exists_normal_local_between) | (exact GlobalTheory.LocAcycEmbed.exists_normal_local_between) | (intros; apply GlobalTheory.LocAcycEmbed.exists_normal_local_between  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePlaceOrdEqOneStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (x : L), Transcendental k x → k⟮x⟯ = ⊤ → ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  first | exact @GlobalTheory.Nef.exists_unique_place_ord_eq_one | exact GlobalTheory.Nef.exists_unique_place_ord_eq_one | (intros; apply GlobalTheory.Nef.exists_unique_place_ord_eq_one <;> assumption)
end

