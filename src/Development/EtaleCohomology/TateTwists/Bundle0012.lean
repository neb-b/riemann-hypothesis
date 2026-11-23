module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0003
public import Development.EtaleCohomology.TateTwists.Bundle0002
public import Development.EtaleCohomology.TateTwists.Bundle0004

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistTensorIsoOfGeneratorMapIso
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TwMulPf

variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using this.symm

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := by
  simp [Sec.map]

theorem sec_map_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := by
  simp [Sec.map]

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

def secL {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Sec F U →ₗ[ULift.{1} R] Sec G U :=
  (φ.hom.app (op U)).hom

def transp {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ (secL (ψ.hom.f w) U)
  nat g s t w h a b := by
    change Sec.res g (Sec.map (ψ.hom.f w) _) = Sec.map (ψ.hom.f w) _
    rw [sec_res_map, μ.nat]
  leibniz U s t w h a b := by
    change Sec.map (K'.d w (w + 1)) (Sec.map (ψ.hom.f w) _) =
      Sec.map (ψ.hom.f (w + 1)) _ + s.negOnePow • Sec.map (ψ.hom.f (w + 1)) _
    rw [sec_map_comp, ψ.hom.comm w (w + 1), ← sec_map_comp, μ.leibniz]
    simp only [Sec.map, map_add (f := _), map_zsmul_unit]

theorem transp_lift {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (U : Scheme.{0}) (w : ℤ)
    (x : Tens I J U w) : (transp μ ψ).lift U w x = Sec.map (ψ.hom.f w) (μ.lift U w x) := by
  classical
  change _ = secL (ψ.hom.f w) U (μ.lift U w x)
  rw [← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp [Pair.lift, transp]

theorem transp_isTensor {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (hμ : μ.IsTensor) :
    (transp μ ψ).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine loc_mono (hμ.1 U w (Sec.map (ψ.inv.f w) y)) fun V g ⟨x, hx⟩ => ⟨x, ?_⟩
    rw [transp_lift, hx, ← sec_res_map, sec_map_comp, ← HomologicalComplex.comp_f, ψ.inv_hom_id,
      HomologicalComplex.id_f, sec_map_id]
  · refine hμ.2 U w x ?_
    rw [transp_lift] at hx
    have := congrArg (Sec.map (ψ.inv.f w)) hx
    rw [sec_map_comp, ← HomologicalComplex.comp_f, ψ.hom_inv_id, HomologicalComplex.id_f, sec_map_id] at this
    rw [this]
    exact map_zero _

theorem sgl_map_f_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0) (Sec.map (sglι F) x) =
      Sec.map (sglι G) (Sec.map φ x) := by
  rw [sec_map_comp, sec_map_comp]
  congr 1

end LateralTheory.EtaleFoundations.TwMulPf


open LateralTheory.EtaleFoundations.TwMulPf in
def LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), ∃ (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)), μ.IsTensor

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∃ φ : tw q k ⟶ T, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → IsIso φ

open LateralTheory.EtaleFoundations.TwMulPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_tensor_iso_of_generator_map_iso (h1 : LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists)
    (h2 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists) (h3 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso) :
    LateralTheory.EtaleFoundations.EtaleTateTwistSingletonTensorGenMul := by
  intro q _ i j k hk
  obtain ⟨T, μ, hμ⟩ := h1 q i j
  obtain ⟨φ, hφ⟩ := h2 q i j k T μ hμ hk
  have := h3 q i j k T μ hμ hk φ hφ
  let ψ : sgl T ≅ sgl (tw q k) := (CochainComplex.singleFunctor (Shv (ZMod q)) 0).mapIso (asIso φ).symm
  refine ⟨transp μ ψ, transp_isTensor μ ψ hμ, fun U ζ => ?_⟩
  change Sec.map (ψ.hom.f 0) (μ.mul U 0 0 0 (add_zero 0) _ _) = _
  rw [← hφ U ζ]
  change Sec.map (((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map (inv φ)).f 0) _ = _
  rw [sgl_map_f_zero, sec_map_comp, sec_map_comp, IsIso.hom_inv_id_assoc]
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorComplexExistsOfSheafTensorComplex
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section

namespace LateralTheory.EtaleFoundations

def tensPure {R : Type} [CommRing R] {I J : Cx R} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : Tens I J U w :=
  DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
    (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩ (a ⊗ₜ b)

def EtaleSheafTensorComplexExists : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R)
    (φ : ∀ (U : Scheme.{0}) (w : ℤ), Tens I J U w →ₗ[ULift.{1} R] Sec (K.X w) U),
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w),
      Sec.res g (φ U w x) = φ V w (Tens.res g w x)) ∧
    (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (K.d w (w + 1)) (φ U w (tensPure s t w h a b)) =
        φ U (w + 1) (tensPure (s + 1) t (w + 1) (by omega) (Sec.map (I.d s (s + 1)) a) b) +
        s.negOnePow • φ U (w + 1) (tensPure s (t + 1) (w + 1) (by omega) a (Sec.map (J.d t (t + 1)) b))) ∧
    (∀ (U : Scheme.{0}) (w : ℤ) (y : Sec (K.X w) U), Loc U fun V g => ∃ x, φ V w x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), φ U w x = 0 → Loc U fun _ g => Tens.res g w x = 0)

theorem etale_tensor_complex_exists_of_sheaf_tensor_complex (hS : EtaleSheafTensorComplexExists) : EtaleComplexTensorPairingExists := by
  intro R _ I J
  obtain ⟨K, φ, hnat, hd, hsurj, hinj⟩ := hS R I J
  let μ : Pair I J K :=
    { mul := fun U s t w h => (TensorProduct.mk (ULift.{1} R) _ _).compr₂
          ((φ U w).comp (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
            (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩))
      nat := by
        intro V U g s t w h a b
        have := hnat g w (tensPure s t w h a b)
        simpa [tensPure, Tens.res, DirectSum.lmap_lof] using this
      leibniz := by
        intro U s t w h a b
        simpa [tensPure] using hd U s t w h a b }
  have hlift : ∀ U w, μ.lift U w = φ U w := by
    intro U w
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp [Pair.lift, μ]
  refine ⟨K, μ, ?_, ?_⟩
  · intro U w y
    simpa [hlift] using hsurj U w y
  · intro U w x hx
    exact hinj U w x (by simpa [hlift] using hx)

end LateralTheory.EtaleFoundations
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorHomDescendsAlongTensorPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TensFam

theorem res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res h (Sec.res g y) = Sec.res (h ≫ g) y := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h1⟩ := hP
  obtain ⟨T, hT, h2⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT, fun V g hg => ⟨h1 V g hg.1, h2 V g hg.2⟩⟩

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem sep {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (s s' : Sec M U)
    (h : Loc U fun V g => Sec.res g s = Sec.res g s') : s = s' := by
  obtain ⟨T, hT, h1⟩ := h
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  exact (hM T hT).isSeparatedFor.ext fun V g hg => h1 V g hg

theorem glue {S : Type} [CommRing S] (M : Shv S) {U : Scheme.{0}} (T : Sieve U) (hT : T ∈ Scheme.etaleTopology U)
    (t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V)
    (ht : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : T.arrows g),
      t W (k ≫ g) (T.downward_closed hg k) = Sec.res k (t V g hg)) :
    ∃ s : Sec M U, ∀ V g (hg : T.arrows g), Sec.res g s = t V g hg := by
  have hM := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology M.obj (forget _)).mp M.2)
  let x : Presieve.FamilyOfElements (M.obj ⋙ forget _) T.arrows := fun V g hg => t V g hg
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g k hg
    exact ht V W g k hg
  exact ⟨(hM T hT).amalgamate x hx, fun V g hg => (hM T hT).valid_glue hx g hg⟩

theorem lift_res {R : Type} [CommRing R] {I J K : Cx R} (τ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ)
    (x : Tens I J U w) : Sec.res g (τ.lift U w x) = τ.lift V w (Tens.res g w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [Sec.res, map_add (f := _)] at *; rw [ha, hb]
  | of i z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [Sec.res, map_add (f := _)] at *; rw [ha, hb]
    | tmul a c =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [Pair.lift, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.lift.tmul, TensorProduct.map_tmul]
      exact τ.nat g _ _ w _ a c

theorem res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a c : Sec F U) :
    Sec.res g (a + c) = Sec.res g a + Sec.res g c := map_add _ _ _

section Main
variable {R S : Type} [CommRing R] [CommRing S] {I J K : Cx R}

def Good (τ : Pair I J K) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
    (U : Scheme.{0}) (y : Sec (K.X w) U) (s : Sec M U) : Prop :=
  Loc U fun V g => ∃ x, τ.lift V w x = Sec.res g y ∧ Sec.res g s = b V x

variable (τ : Pair I J K) (hτ : τ.IsTensor) (w : ℤ) (M : Shv S) (b : ∀ U : Scheme.{0}, Tens I J U w →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V (Tens.res g w x))
include hτ hb

theorem key {U : Scheme.{0}} (x1 x2 : Tens I J U w) (h : τ.lift U w x1 = τ.lift U w x2) : b U x1 = b U x2 := by
  have h0 : τ.lift U w (x1 - x2) = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨T, hT, hT'⟩ := hτ.2 U w _ h0
  apply sep M
  refine ⟨T, hT, fun V g hg => ?_⟩
  have h1 : Tens.res g w (x1 - x2) = 0 := hT' V g hg
  rw [map_sub, sub_eq_zero] at h1
  show Sec.res g (b U x1) = Sec.res g (b U x2)
  rw [hb, hb, h1]

theorem uniq {U : Scheme.{0}} {y : Sec (K.X w) U} {s s' : Sec M U}
    (h1 : Good τ w M b U y s) (h2 : Good τ w M b U y s') : s = s' := by
  apply sep M
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  rw [hs, hs']
  exact key τ hτ w M b hb x x' (hx.trans hx'.symm)

theorem good_exists (U : Scheme.{0}) (y : Sec (K.X w) U) : ∃ s, Good τ w M b U y s := by
  obtain ⟨T, hT, hc⟩ := hτ.1 U w y
  let t : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V := fun V g hg => b V (hc V g hg).choose
  obtain ⟨s, hs⟩ := glue M T hT t (by
    intro V W g k hg
    simp only [t]
    rw [hb]
    apply key τ hτ w M b hb
    rw [(hc W (k ≫ g) (T.downward_closed hg k)).choose_spec, ← lift_res, (hc V g hg).choose_spec, res_res])
  exact ⟨s, T, hT, fun V g hg => ⟨(hc V g hg).choose, (hc V g hg).choose_spec, hs V g hg⟩⟩

omit hτ in
theorem good_add {U : Scheme.{0}} {y1 y2 : Sec (K.X w) U} {s1 s2 : Sec M U}
    (h1 : Good τ w M b U y1 s1) (h2 : Good τ w M b U y2 s2) : Good τ w M b U (y1 + y2) (s1 + s2) := by
  obtain ⟨T, hT, h⟩ := loc_and h1 h2
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨⟨x, hx, hs⟩, ⟨x', hx', hs'⟩⟩ := h V g hg
  exact ⟨x + x', by rw [map_add (f := _), hx, hx', res_add], by rw [res_add, hs, hs', map_add (f := _)]⟩

omit hτ hb in
theorem good_zero (U : Scheme.{0}) : Good τ w M b U 0 0 :=
  loc_top fun V g => ⟨0, by simp, by simp⟩

omit hτ in
theorem good_nat {V U : Scheme.{0}} (g : V ⟶ U) {y : Sec (K.X w) U} {s : Sec M U}
    (h : Good τ w M b U y s) : Good τ w M b V (Sec.res g y) (Sec.res g s) := by
  obtain ⟨T, hT, h1⟩ := h
  refine ⟨T.pullback g, (Scheme.etaleTopology).pullback_stable g hT, fun W k hk => ?_⟩
  obtain ⟨x, hx, hs⟩ := h1 W (k ≫ g) hk
  exact ⟨x, by rw [res_res, hx], by rw [res_res, hs]⟩

omit hτ in
theorem good_lift (U : Scheme.{0}) (x : Tens I J U w) : Good τ w M b U (τ.lift U w x) (b U x) :=
  loc_top fun V g => ⟨Tens.res g w x, (lift_res τ g w x).symm, hb V U g x⟩

end Main

end LateralTheory.EtaleFoundations.TensFam

open LateralTheory.EtaleFoundations.TensFam in
theorem LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing : LateralTheory.EtaleFoundations.EtaleTensorComplexDescendsNaturalFamily := by
  intro R S _ _ I J K τ hτ w M b hb
  have ex := good_exists τ hτ w M b hb
  let φ : ∀ U : Scheme.{0}, Sec (K.X w) U →+ Sec M U := fun U =>
    { toFun := fun y => (ex U y).choose
      map_zero' := uniq τ hτ w M b hb (ex U 0).choose_spec (good_zero τ w M b U)
      map_add' := fun y1 y2 => uniq τ hτ w M b hb (ex U _).choose_spec
        (good_add τ w M b hb (ex U y1).choose_spec (ex U y2).choose_spec) }
  refine ⟨φ, fun V U g y => ?_, fun U x => ?_⟩
  · exact uniq τ hτ w M b hb (good_nat τ w M b hb g (ex U y).choose_spec) (ex V _).choose_spec
  · exact uniq τ hτ w M b hb (ex U _).choose_spec (good_lift τ w M b hb U x)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorPreservesQuasiIsoOfAcyclicAndCone
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.tqis

def acyc : Prop :=
  ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T),
    τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic

def cone : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T'),
    τ.IsTensor → τ'.IsTensor → τ.Compat τ' f (𝟙 J) u → ∃ σ : Pair (mappingCone f) J (mappingCone u), σ.IsTensor

end LateralTheory.EtaleFoundations.tqis

theorem qis_iff_cone {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) : QuasiIso f ↔ (mappingCone f).Acyclic := by
  have h : HomotopyCategory.quasiIso (Shv R) (ComplexShape.up ℤ) ((HomotopyCategory.quotient _ _).map f) ↔ (HomotopyCategory.subcategoryAcyclic (Shv R)).trW ((HomotopyCategory.quotient _ _).map f) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at h
  change HomologicalComplex.quasiIso (Shv R) (ComplexShape.up ℤ) f ↔ _
  exact h.trans ((ObjectProperty.trW_iff_of_distinguished (HomotopyCategory.subcategoryAcyclic (Shv R)) _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _))

theorem cone_ge {R : Type} [CommRing R] {I I' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] (f : I ⟶ I') :
    (mappingCone f).IsStrictlyGE (-1) :=
  CochainComplex.isStrictlyGE_mappingCone f 0 0 (-1)

theorem LateralTheory.EtaleFoundations.etale_tensor_preserves_quasiIso_of_acyclic_and_cone (hA : LateralTheory.EtaleFoundations.tqis.acyc) (hC : LateralTheory.EtaleFoundations.tqis.cone) :
    LateralTheory.EtaleFoundations.EtaleTensorPairQuasiIsoOfFlatQuasiIso := by
  intro R _ I I' J T T' _ _ _ τ τ' hτ hτ' hJ f _ u hc
  obtain ⟨σ, hσ⟩ := hC R τ τ' f u hτ hτ' hc
  have := cone_ge f
  rw [qis_iff_cone]
  exact hA R (-1) 0 σ hσ hJ ((qis_iff_cone f).1 inferInstance)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductOfFamilyAndLeibniz
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L),
    ∃ m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U,
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) ∧
      ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)

def LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K T : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U),
      (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.res g (m U s t w h a b) = m V s t w h (Sec.res g a) (Sec.res g b)) →
      (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) →
      ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (T.X s) U) (b : Sec (K.X t) U),
        Sec.map (L.d w (w + 1)) (m U s t w h a b) = m U (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) a) b +
          s.negOnePow • m U s (t + 1) (w + 1) (by omega) a (Sec.map (K.d t (t + 1)) b)

theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_of_family_and_leibniz (hfam : LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists)
    (hleib : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz) : LateralTheory.EtaleFoundations.EtaleTensorPairProductAssociative := by
  intro R _ I J K T T3 τ τ' hτ _ M L μ' ν'
  obtain ⟨m, hnat, heq⟩ := hfam R τ hτ μ' ν'
  refine ⟨⟨m, hnat, hleib R τ hτ μ' ν' m hnat heq⟩, ?_⟩
  intro U s t u st tu w h1 h2 h3 h4 a b c
  exact heq U s t u st tu w h1 h2 h3 h4 a b c
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorTwistedResolutionOfExistenceBoundAndS
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tt_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

def tt_tens_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → μ.IsTensor →
    K.IsStrictlyGE 0

def tt_twist_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {J M : Cx (ZMod q)}
    (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q j J e' → (∀ t, FlatS (J.X t)) →
    ∀ σ : Pair (sgl (tw q i)) J M, σ.IsTensor →
      IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ)

def tt_res_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) {I J M T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U),
    IsTwRes q i I e → J.IsStrictlyGE 0 → (∀ t, FlatS (J.X t)) →
    ∀ (σ : Pair (sgl (tw q i)) J M) (τ : Pair I J T), σ.IsTensor → τ.IsTensor →
      ∃ m : M ⟶ T, QuasiIso m ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec (J.X 0) U),
        Sec.map (m.f 0) (σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) b) =
          τ.mul U 0 0 0 (add_zero 0) (e U ζ) b

theorem etale_tensor_twisted_resolution_of_existence_bound_and_sides (hex : tt_tens_ex) (hge : tt_tens_ge) (htw : tt_twist_side) (hres : tt_res_side) :
    EtaleTensorPairTwistResolutionMul := by
  intro q _ i j k hk I J T e e' hI hJ hflat τ hτ
  obtain ⟨M, σ, hσ⟩ := hex (ZMod q) (sgl (tw q i)) J
  obtain ⟨-, ε₁, hε₁, hgen₁⟩ := htw q i j k hk e' hJ hflat σ hσ
  obtain ⟨m, hm, hgen⟩ := hres q i e hI hJ.1 hflat σ τ hσ hτ
  refine ⟨hge (ZMod q) τ hI.1 hJ.1 hτ, ε₁ ≫ m, inferInstance, fun U ζ => ?_⟩
  refine Eq.trans ?_ (hgen U ζ (e' U ζ))
  refine Eq.trans ?_ (congrArg (Sec.map (m.f 0)) (hgen₁ U ζ))
  rfl

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTwistExtendsThroughMonoToResolutionZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

def EtaleKummerSectionsIntoTwistEmbeddingExist : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

def EtaleTwistExtendsThroughMonoToResolutionZero : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j →
    ∃ e : M ⟶ (res _ (tw q 1)).X 0, j ≫ e = resι _ (tw q 1)

theorem etale_kummer_torsor_class_exists_of_tors_and_ext (h1 : EtaleKummerSectionsIntoTwistEmbeddingExist) (h2 : EtaleTwistExtendsThroughMonoToResolutionZero) : EtaleKummerTriangleExists := by
  intro q _
  apply pick_spec
  obtain ⟨M, j, hj, s, hs1, hs2⟩ := h1 q
  obtain ⟨e, he⟩ := h2 q M j hj
  refine ⟨fun U v => Sec.map e (s U v), ?_, ?_⟩
  · intro V U g v hq
    show Sec.res g (Sec.map e (s U v)) = Sec.map e (s V _)
    rw [← hs1 V U g v hq]
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (e.hom.naturality g.op)) (s U v)).symm
  · intro U ζ v w h
    show Sec.map e (s U w) = Sec.map e (s U v) + _
    rw [hs2 U ζ v w h]
    show (e.hom.app (op U)).hom (_ + _) = _
    rw [map_add (f := _)]
    congr 1
    unfold resGen
    rw [← he]
    rfl
end LateralTheory.EtaleFoundations
end

