module

public import Development.EtaleCohomology.TateTwists.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0023

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.TPaPrecompPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem pa_sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)
  simpa using this.symm

theorem pa_sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem t_pa_precomp_of : t_pa_precomp := by
  intro R _ I I' J K u μ
  refine ⟨⟨fun U s t w h => (μ.mul U s t w h).comp ((u.f s).hom.app (op U)).hom, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    simp only [LinearMap.comp_apply]
    exact (μ.nat g s t w h _ b).trans (by rw [pa_sec_res_map])
  · intro U s t w h a b
    simp only [LinearMap.comp_apply]
    rw [μ.leibniz]
    congr 2
    rw [← pa_sec_map_comp, u.comm]; rfl
  · intro U s t w h a b
    rfl

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TPaTensExPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensEx
variable {R : Type} [CommRing R]

abbrev Jt := Scheme.etaleTopology.{0}
abbrev MC (R : Type) [CommRing R] := ModuleCat.{1} (ULift.{1} R)
abbrev Ix (w : ℤ) := {p : ℤ × ℤ // p.1 + p.2 = w}

theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) :=
  congrArg (fun f => ModuleCat.Hom.hom f a) (φ.hom.naturality g.op)

theorem tres_lof (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : Ix w)
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res (I := I) (J := J) g w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ _ p (Sec.res g a ⊗ₜ Sec.res g b) := by
  simp [Tens.res, DirectSum.lmap_lof]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ MC R where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    apply ModuleCat.hom_ext; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, unop_id, tres_lof, ModuleCat.hom_id, LinearMap.id_apply]
    simp [Sec.res]
  map_comp f g := by
    apply ModuleCat.hom_ext; apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [ModuleCat.hom_ofHom, LinearMap.comp_apply, unop_comp, tres_lof, ModuleCat.hom_comp]
    simp [Sec.res]

def dc (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : Ix w) :
    Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only; omega⟩ ∘ₗ
    TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
  ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
      ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only; omega⟩ ∘ₗ
    TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ (dc I J U w)

theorem dT_lof (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : Ix w) (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    dT I J U w (DirectSum.lof (ULift.{1} R) _ _ p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only; omega⟩ (Sec.map (I.d p.1.1 (p.1.1 + 1)) a ⊗ₜ b) +
      (p.1.1.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _ (fun q : Ix (w + 1) => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
        ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only; omega⟩ (a ⊗ₜ Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
  simp [dT, dc, DirectSum.toModule_lof]

theorem dT_res (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
    apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
    simp only [LinearMap.comp_apply]
    rw [tres_lof, dT_lof, dT_lof, map_add (f := _), map_zsmul, tres_lof, tres_lof, sec_nat, sec_nat]

def dP (I J : Cx R) (w : ℤ) : TP I J w ⟶ TP I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := ModuleCat.hom_ext (dT_res I J g.unop w)

end LateralTheory.EtaleFoundations.TensEx

namespace LateralTheory.EtaleFoundations.TensEx
variable {R : Type} [CommRing R]

theorem sec_dd (K : Cx R) (h i j : ℤ) {U : Scheme.{0}} (a : Sec (K.X h) U) :
    Sec.map (K.d i j) (Sec.map (K.d h i) a) = 0 := by
  change Sec.map (K.d h i ≫ K.d i j) a = 0
  rw [K.d_comp_d]
  rfl

theorem dT_dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    dT I J U (w + 1) (dT I J U w x) = 0 := by
  rw [← LinearMap.comp_apply (f := dT I J U (w + 1))]
  suffices h : dT I J U (w + 1) ∘ₗ dT I J U w = 0 by rw [h]; rfl
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [dT_lof, map_add (f := _), map_zsmul, dT_lof, dT_lof]
  simp only [sec_dd, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, add_zero, smul_add,
    smul_zero, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_smul]
  exact neg_add_cancel _

theorem tensorDifferential_comp_eq_zero (I J : Cx R) (w : ℤ) : dP I J w ≫ dP I J (w + 1) = 0 := by
  ext U : 2
  apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
  exact dT_dT I J U.unop w x

def T (I J : Cx R) : Cx R :=
  CochainComplex.of (fun w => (presheafToSheaf Jt (MC R)).obj (TP I J w))
    (fun w => (presheafToSheaf Jt (MC R)).map (dP I J w))
    (fun w => by rw [← Functor.map_comp, tensorDifferential_comp_eq_zero, Functor.map_zero])

theorem T_d (I J : Cx R) (w : ℤ) : (T I J).d w (w + 1) = (presheafToSheaf Jt (MC R)).map (dP I J w) :=
  by unfold T; simp [CochainComplex.of]

theorem toS_res (P : Scheme.{0}ᵒᵖ ⥤ MC R) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    ((sheafify Jt P).map g.op).hom (((toSheafify Jt P).app (op U)).hom x) =
      ((toSheafify Jt P).app (op V)).hom ((P.map g.op).hom x) :=
  (congrArg (fun f => ModuleCat.Hom.hom f x) ((toSheafify Jt P).naturality g.op)).symm

theorem toS_map {P Q : Scheme.{0}ᵒᵖ ⥤ MC R} (η : P ⟶ Q) {U : Scheme.{0}} (x : P.obj (op U)) :
    ((sheafifyMap Jt η).app (op U)).hom (((toSheafify Jt P).app (op U)).hom x) =
      ((toSheafify Jt Q).app (op U)).hom ((η.app (op U)).hom x) :=
  (congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) x) (toSheafify_naturality Jt η)).symm

def tS (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((T I J).X w) U :=
  ((toSheafify Jt (TP I J w)).app (op U)).hom

def mulT (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec ((T I J).X w) U :=
  (TensorProduct.mk (ULift.{1} R) _ _).compr₂
    (tS I J U w ∘ₗ
      DirectSum.lof (ULift.{1} R) (Ix w) (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)

theorem mulT_apply (I J : Cx R) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) a b :
    mulT I J U s t w h a b = tS I J U w
      (DirectSum.lof (ULift.{1} R) (Ix w) (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩ (a ⊗ₜ b)) :=
  rfl

def tau (I J : Cx R) : Pair I J (T I J) where
  mul := mulT I J
  nat g s t w h a b := by
    rw [mulT_apply, mulT_apply]
    exact (toS_res (TP I J w) g _).trans (congrArg _ (tres_lof I J g w ⟨(s, t), h⟩ a b))
  leibniz U s t w h a b := by
    rw [mulT_apply, mulT_apply, mulT_apply, T_d]
    refine Eq.trans (toS_map (dP I J w) _) ?_
    show tS I J U (w + 1) (dT I J U w _) = tS I J U (w + 1) _ + s.negOnePow • tS I J U (w + 1) _
    rw [dT_lof, map_add (f := _), map_zsmul, Units.smul_def]

theorem tau_lift (I J : Cx R) (U : Scheme.{0}) (w : ℤ) :
    (tau I J).lift U w = tS I J U w := by
  apply DirectSum.linearMap_ext; intro p; apply TensorProduct.ext'; intro a b
  simp only [Pair.lift, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
  rfl

theorem tau_isTensor (I J : Cx R) : (tau I J).IsTensor := by
  constructor
  · intro U w y
    refine ⟨_, Presheaf.imageSieve_mem Jt (toSheafify Jt (TP I J w)) (U := op U) y, ?_⟩
    intro V g hg
    obtain ⟨x, hx⟩ := hg
    exact ⟨x, by rw [tau_lift]; exact hx⟩
  · intro U w x hx
    rw [tau_lift] at hx
    refine ⟨_, Presheaf.equalizerSieve_mem Jt (toSheafify Jt (TP I J w)) (X := op U) x 0
      (by rw [map_zero]; exact hx), ?_⟩
    intro V g hg
    have : (TP I J w).map g.op x = (TP I J w).map g.op 0 := hg
    rw [map_zero] at this
    exact this

end LateralTheory.EtaleFoundations.TensEx

namespace LateralTheory.EtaleFoundations

theorem t_pa_tens_ex_of : t_pa_tens_ex := by
  intro R _ I J
  exact ⟨TensEx.T I J, TensEx.tau I J, TensEx.tau_isTensor I J⟩

end LateralTheory.EtaleFoundations
end
end

-- bundled from Development.EtaleCohomology.TateTwists.TPaTensUnivPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

abbrev tl {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) : Tens I J U w :=
  DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)

theorem tu_ext {I J : Cx R} {U : Scheme.{0}} {w : ℤ} {M : Type 1} [AddCommGroup M] [Module (ULift.{1} R) M]
    {f g : Tens I J U w →ₗ[ULift.{1} R] M}
    (h : ∀ p a b, f (tl p a b) = g (tl p a b)) : f = g :=
  DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => h p a b

theorem tu_res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (tl p a b) = tl p (Sec.res g a) (Sec.res g b) := by
  simp [tl, Tens.res, DirectSum.lmap_lof]

theorem tu_lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (tl p a b) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [tl, Pair.lift, DirectSum.toModule_lof]

theorem tu_sec_res_id {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

theorem tu_sec_res_comp {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (f ≫ g) a = Sec.res f (Sec.res g a) := by
  simp [Sec.res]

def TP (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (tu_ext fun p a b => ?_)
    simp only [ModuleCat.hom_ofHom, unop_id, ModuleCat.hom_id, LinearMap.id_apply]
    rw [tu_res_lof, tu_sec_res_id, tu_sec_res_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (tu_ext fun p a b => ?_)
    simp only [ModuleCat.hom_ofHom, unop_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [tu_res_lof, tu_res_lof, tu_res_lof, tu_sec_res_comp, tu_sec_res_comp]

theorem tu_lift_nat {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  have : (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w) := by
    refine tu_ext fun p a b => ?_
    simp only [LinearMap.comp_apply]
    rw [tu_res_lof, tu_lift_lof, tu_lift_lof, ← μ.nat]
  exact LinearMap.congr_fun this x

def Lf {I J K : Cx R} (μ : Pair I J K) (w : ℤ) : TP I J w ⟶ (K.X w).obj where
  app U := ModuleCat.ofHom (μ.lift U.unop w)
  naturality V U g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact tu_lift_nat μ g.unop w x

theorem tu_locInj {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (Lf τ w) := by
  constructor
  intro U x' y' hxy
  let x : Tens I J U.unop w := x'
  let y : Tens I J U.unop w := y'
  have hxy' : τ.lift U.unop w x = τ.lift U.unop w y := hxy
  have h0 : τ.lift U.unop w (x - y) = 0 := by
    rw [map_sub]; exact sub_eq_zero.mpr hxy'
  obtain ⟨S, hS, hP⟩ := hτ.2 U.unop w (x - y) h0
  refine Scheme.etaleTopology.superset_covering ?_ hS
  intro V g hg
  have h1 : Tens.res g w (x - y) = 0 := hP V g hg
  rw [map_sub, sub_eq_zero] at h1
  exact h1

theorem tu_locSurj {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Lf τ w) := by
  constructor
  intro U y
  obtain ⟨S, hS, hP⟩ := hτ.1 U w y
  refine Scheme.etaleTopology.superset_covering ?_ hS
  intro V g hg
  obtain ⟨x, hx⟩ := hP V g hg
  exact ⟨x, hx⟩

theorem etaleTensorPairingLift_isSheafifyLocalIso {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) :
    Scheme.etaleTopology.{0}.W (Lf τ w) := by
  have := tu_locInj τ hτ w
  have := tu_locSurj τ hτ w
  exact GrothendieckTopology.W_of_isLocallyBijective _ _

def uf {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) : (T.X w).obj ⟶ (K.X w).obj :=
  ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ w) _ (K.X w).property).2 (Lf μ w) |>.choose

theorem uf_spec {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) :
    Lf τ w ≫ uf τ hτ μ w = Lf μ w :=
  ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ w) _ (K.X w).property).2 (Lf μ w) |>.choose_spec

theorem uf_lift {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (w : ℤ) (U : Scheme.{0})
    (x : Tens I J U w) : ((uf τ hτ μ w).app (op U)).hom (τ.lift U w x) = μ.lift U w x := by
  have := congrArg (fun φ => (φ.app (op U)).hom x) (uf_spec τ hτ μ w)
  exact this

theorem uf_mul {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (U : Scheme.{0})
    (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    ((uf τ hτ μ w).app (op U)).hom (τ.mul U s t w h a b) = μ.mul U s t w h a b := by
  have := uf_lift τ hτ μ w U (tl (w := w) ⟨(s, t), h⟩ a b)
  rwa [tu_lift_lof, tu_lift_lof] at this

theorem uf_comm {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) (i : ℤ) :
    uf τ hτ μ i ≫ (K.d i (i + 1)).hom = (T.d i (i + 1)).hom ≫ uf τ hτ μ (i + 1) := by
  apply ((etaleTensorPairingLift_isSheafifyLocalIso τ hτ i) _ (K.X (i + 1)).property).1
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (tu_ext fun p a b => ?_))
  obtain ⟨⟨s, t⟩, h⟩ := p
  simp only [NatTrans.comp_app, ModuleCat.hom_comp]
  change ((K.d i (i + 1)).hom.app U).hom (((uf τ hτ μ i).app (op U.unop)).hom (τ.lift U.unop i (tl _ a b))) =
    ((uf τ hτ μ (i + 1)).app (op U.unop)).hom (((T.d i (i + 1)).hom.app U).hom (τ.lift U.unop i (tl _ a b)))
  rw [tu_lift_lof, uf_mul]
  have l1 := μ.leibniz U.unop s t i h a b
  have l2 := τ.leibniz U.unop s t i h a b
  simp only [Sec.map] at l1 l2
  rw [l1, l2, map_add (f := _), Units.smul_def, Units.smul_def, map_zsmul, uf_mul, uf_mul]

def uc {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (μ : Pair I J K) : T ⟶ K where
  f w := ⟨uf τ hτ μ w⟩
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    ext1
    exact uf_comm τ hτ μ i

theorem t_pa_tens_univ_of : t_pa_tens_univ := by
  intro R _ I J T K τ hτ μ
  refine ⟨uc τ hτ μ, fun U s t w h a b => ?_⟩
  simp only [HomologicalComplex.id_f, pa_sec_map_id]
  exact uf_mul τ hτ μ U s t w h a b

end LateralTheory.EtaleFoundations
end
end

-- bundled from Development.EtaleCohomology.TateTwists.TtTensExPfLoc
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

variable {R : Type} [CommRing R]

theorem tt_sheafify_locSurj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (y : ((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.obj (op U)) :
    Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology.{0} P).app (op V)).hom x =
      (((presheafToSheaf Scheme.etaleTopology.{0} _).obj P).obj.map g.op).hom y :=
  ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) y,
    fun _ _ ⟨x, hx⟩ => ⟨x, hx⟩⟩

theorem tt_sheafify_locInj (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0})
    (x : P.obj (op U)) (hx : ((toSheafify Scheme.etaleTopology.{0} P).app (op U)).hom x = 0) :
    Loc U fun _ g => (P.map g.op).hom x = 0 := by
  refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} P) x 0
    (by simpa using hx), fun _ _ h => ?_⟩
  simpa using h

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.TwSecLocPfZarR
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct GlobalTheory.EtC GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

namespace LateralTheory.EtaleFoundations.TwSecLocPf

def AlgPow : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ζ ξ : Prim q A),
  ∃ s : Set A, Ideal.span s = ⊤ ∧ ∀ f ∈ s, ∃ (a : (ZMod q)ˣ) (n : ℕ), f ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) = 0

theorem ZarPow_of (hA : AlgPow) : ZarPow := by
  intro q _ V ζ ξ
  obtain ⟨s, hs, hf⟩ := hA q Γ(V, ⊤) ζ ξ
  let U : s → V.Opens := fun f => V.basicOpen f.1
  have hU : TopologicalSpace.IsOpenCover U := by
    unfold TopologicalSpace.IsOpenCover
    have h := iSup_basicOpen_of_span_eq_top ⊤ s hs
    show ⨆ f : s, V.basicOpen f.1 = ⊤
    rw [iSup_subtype]
    exact h
  let 𝒰 := V.openCoverOfIsOpenCover U hU
  refine ⟨Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f),
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩), ?_⟩
  rintro W g ⟨Y, h, _, ⟨i⟩, rfl⟩
  obtain ⟨a, n, hn⟩ := hf i.1 i.2
  refine ⟨a, ?_⟩
  have hle : (U i).ι ''ᵁ ⊤ ≤ V.basicOpen i.1 := by simp [U]
  have hu : IsUnit ((U i).ι.appTop.hom i.1) := by
    have := (V.toRingedSpace.isUnit_res_basicOpen i.1).map (V.presheaf.map (homOfLE hle).op).hom
    have e : V.presheaf.map (homOfLE (x := (U i).ι ''ᵁ ⊤) (y := ⊤) le_top).op =
        V.presheaf.map (homOfLE (V.basicOpen_le i.1)).op ≫ V.presheaf.map (homOfLE hle).op := by
      rw [← Functor.map_comp]; rfl
    rw [Scheme.Opens.ι_appTop, e]
    exact this
  have key : (U i).ι.appTop.hom ξ.1 = ((U i).ι.appTop.hom ζ.1) ^ (a : ZMod q).val := by
    have h0 : (U i).ι.appTop.hom (i.1 ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) = 0 := by rw [hn, map_zero]
    rw [map_mul, map_pow, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.pow n).mul_right_eq_zero.1 h0)
  have hc : ∀ x, (h ≫ (U i).ι).appTop.hom x = h.appTop.hom ((U i).ι.appTop.hom x) := fun x => by
    rfl
  show (h ≫ (U i).ι).appTop.hom ξ.1 = ((h ≫ (U i).ι).appTop.hom ζ.1) ^ _
  rw [hc, hc, key]
  exact map_pow _ _ _

theorem TwSecLoc_of_alg (hA : AlgPow) : LateralTheory.EtaleFoundations.TwLocPf.TwSecLoc := TwSecLoc_of (ZarPow_of hA)

end LateralTheory.EtaleFoundations.TwSecLocPf
end
end

