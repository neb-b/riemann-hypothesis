module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0431

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallyInjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TwMulInj

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose R hR hRQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h V g (hSP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg), ?_, ?_⟩
  · exact (Scheme.etaleTopology).bind_covering hS (fun V g hg => hR V g hg)
  · rintro W _ ⟨V, k, g, hg, hk, rfl⟩
    exact hRQ V g hg W k hk

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem loc_empty {U : Scheme.{0}} [IsEmpty U] {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology (P := @Etale) U, fun _ _ hg => hg.elim⟩

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun f => f.hom x) (φ.hom.naturality g.op)

theorem sglι_left {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom (Sec.map (sglι F) x) = x := by
  have h := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv_hom_id
  exact (congrArg (fun f : F ⟶ F => (f.hom.app (op U)).hom x) h).trans rfl

theorem nsmul_eq_zero_of_dvd {q : ℕ} {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M] {c : ℕ} (h : q ∣ c)
    (x : M) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((c : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp only [ULift.down_natCast, ULift.zero_down]
    exact (CharP.cast_eq_zero_iff (ZMod q) q c).2 h
  rw [this, zero_smul]

theorem res_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res (F := F) g 0 = 0 :=
  map_zero _

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x :=
  map_nsmul _ _ _

theorem map_nsmul' {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x :=
  map_nsmul _ _ _

end GlobalTheory.EtC.TwMulInj

namespace GlobalTheory.EtC.TwMulInj
variable {R : Type} [CommRing R]

theorem tmap_nsmul {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module (ULift.{1} R) M] [Module (ULift.{1} R) N] [Module (ULift.{1} R) M'] [Module (ULift.{1} R) N']
    (f : M →ₗ[ULift.{1} R] M') (g : N →ₗ[ULift.{1} R] N') (c : ℕ) (s : M) (t : N) :
    TensorProduct.map f g (c • (s ⊗ₜ[ULift.{1} R] t)) = c • (f s ⊗ₜ g t) := by
  rw [map_nsmul, TensorProduct.map_tmul]

theorem tens_res_lof {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (s : Sec (I.X p.1.1) U) (t : Sec (J.X p.1.2) U) (c : ℕ) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (c • (s ⊗ₜ t))) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (c • (Sec.res g s ⊗ₜ Sec.res g t)) := by
  classical
  unfold Tens.res
  rw [DirectSum.lmap_lof, tmap_nsmul]

theorem lift_lof {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (s : Sec (I.X p.1.1) U) (t : Sec (J.X p.1.2) U) (c : ℕ) :
    μ.lift U w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (c • (s ⊗ₜ t))) = c • μ.mul U p.1.1 p.1.2 w p.2 s t := by
  classical
  unfold Pair.lift
  rw [DirectSum.toModule_lof, map_nsmul, TensorProduct.lift.tmul]

theorem lof_eq_zero {ι : Type*} [DecidableEq ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module (ULift.{1} R) (M i)]
    (i : ι) (x : M i) (h : DirectSum.lof (ULift.{1} R) ι M i x = 0) : x = 0 :=
  DirectSum.of_injective (β := M) i (h.trans (map_zero _).symm)

end GlobalTheory.EtC.TwMulInj

namespace GlobalTheory.EtC.TwMulInj

theorem tw_mul_loc_injective : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → (∀ (W : Scheme.{0}) (ζ : Prim q Γ(W, ⊤)) (c : ℕ), c • (twGen i ζ ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ) = 0 → Loc W fun V _ => Nonempty V → q ∣ c) → ∀ {K : Cx (ZMod q)} (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) = τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → ∀ (U : Scheme.{0}) (a : Sec (tw q k) U), Sec.map φ a = 0 → Loc U fun _ g => Sec.res g a = 0 := by
  intro q _ i j k hk hyp K τ hτ φ hφ U a ha
  have Tk := GlobalTheory.T.tateTwist_sections_locally_generated q k
  have Ti := GlobalTheory.T.tateTwist_sections_locally_generated q i
  have Tj := GlobalTheory.T.tateTwist_sections_locally_generated q j
  refine loc_bind (Tk.1 U a) ?_
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · exact loc_top fun W k' => by rw [res_comp, h0, res_zero]
  ·
    have hres : ∀ (W : Scheme.{0}) (h : W ⟶ V), Sec.res (h ≫ g) a = c • Sec.res h (twGen k ζ) := by
      intro W h
      rw [res_comp, hc, res_nsmul]
    set A := Sec.map (sglι (tw q i)) (twGen i ζ) with hA
    set B := Sec.map (sglι (tw q j)) (twGen j ζ) with hB
    have h1 : c • τ.mul V 0 0 0 (add_zero 0) A B = 0 := by
      rw [← hφ V ζ, ← map_nsmul', ← hc, map_res, ha, res_zero]
    classical
    let x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0 :=
      DirectSum.lof (ULift.{1} (ZMod q)) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = 0} =>
        Sec ((sgl (tw q i)).X p.1.1) V ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) V) ⟨(0, 0), by simp⟩ (c • (A ⊗ₜ B))
    have hx : τ.lift V 0 x = 0 := (lift_lof τ V 0 ⟨(0, 0), by simp⟩ A B c).trans h1
    refine loc_bind (hτ.2 V 0 x hx) ?_
    intro V' g' hx'

    set ζ' := ζ.map g'.appTop.hom with hζ'
    have h2 : c • (twGen i ζ' ⊗ₜ[ULift.{1} (ZMod q)] twGen j ζ') = 0 := by
      have e2 := lof_eq_zero _ _ _ ((tens_res_lof g' 0 ⟨(0, 0), by simp⟩ A B c).symm.trans hx')
      have e3 : c • (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          (Sec.res g' A) ⊗ₜ[ULift.{1} (ZMod q)]
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom (Sec.res g' B)) = 0 :=
        (tmap_nsmul _ _ c _ _).symm.trans ((congrArg (TensorProduct.map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom) e2).trans (map_zero _))
      have ei : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom
          (Sec.res g' A) = twGen i ζ' := by
        have h := (map_res (sglι (tw q i)) g' (twGen i ζ)).symm
        rw [Ti.2.2.2.1 V' V g' ζ] at h
        exact (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom.hom.app (op V')).hom h).trans
          (sglι_left _ _)
      have ej : ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom
          (Sec.res g' B) = twGen j ζ' := by
        have h := (map_res (sglι (tw q j)) g' (twGen j ζ)).symm
        rw [Tj.2.2.2.1 V' V g' ζ] at h
        exact (congrArg ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom.hom.app (op V')).hom h).trans
          (sglι_left _ _)
      rw [ei, ej] at e3
      exact e3
    refine loc_bind (hyp V' ζ' c h2) ?_
    intro V'' g'' hq
    rcases isEmpty_or_nonempty V'' with hV | hV
    · exact loc_empty
    · have hqc := hq hV
      exact loc_top fun W h => by
        rw [hres, nsmul_eq_zero_of_dvd hqc]

end GlobalTheory.EtC.TwMulInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulDegreeZeroLocallySurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.TwMulSurj

variable {R : Type} [CommRing R]

theorem loc_top (U : Scheme.{0}) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : ∀ V g, P V g → P' V g) :
    Loc U P' := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => h' V g (hP V g hg)⟩

theorem loc_and {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : Loc U P') :
    Loc U fun V g => P V g ∧ P' V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hP'⟩ := h'
  exact ⟨S ⊓ S', GrothendieckTopology.intersection_covering _ hS hS', fun V g hg => ⟨hP V g hg.1, hP' V g hg.2⟩⟩

theorem loc_bind {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} {P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (h' : ∀ V g, P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let Rs : ∀ ⦃V : Scheme.{0}⦄ ⦃g : V ⟶ U⦄, S.arrows g → Sieve V := fun V g hg => (h' V g (hP V g hg)).choose
  refine ⟨Sieve.bind S.arrows Rs, Scheme.etaleTopology.bind_covering hS fun V g hg => (h' V g (hP V g hg)).choose_spec.1, ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact (h' V g (hP V g hg)).choose_spec.2 W k hk

theorem map_comp_apply {F G H : Shv R} (f : F ⟶ G) (g : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem map_id_apply {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem res_map {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map f x) = Sec.map f (Sec.res g x) := by
  have := congrArg (fun m => m.hom x) (f.hom.naturality g.op)
  simpa using this.symm

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

theorem smap_add {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map f (x + y) = Sec.map f x + Sec.map f y := map_add _ x y

theorem sres_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ x y

theorem smap_nsmul {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map f (n • x) = n • Sec.map f x := map_nsmul _ n x

theorem sres_nsmul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ n x

theorem smap_zero {F G : Shv R} (f : F ⟶ G) {U : Scheme.{0}} : Sec.map f (0 : Sec F U) = 0 := map_zero _

theorem map_zero_hom {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := by
  rfl

theorem eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  rw [← map_id_apply x, hF.eq_of_src (𝟙 F) 0, map_zero_hom]

def Good {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) (x : Sec G U) : Prop :=
  Loc U fun V g => ∃ z : Sec F V, Sec.map φ z = Sec.res g x

theorem good_of {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {x : Sec G U} (h : ∃ z, Sec.map φ z = x) : Good φ U x := by
  obtain ⟨z, rfl⟩ := h
  exact loc_top U fun V g => ⟨Sec.res g z, (res_map φ g z).symm⟩

theorem good_bind {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec G U) {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : Loc U P) (h : ∀ V g, P V g → Good φ V (Sec.res g x)) : Good φ U x := by
  refine loc_bind hP fun V g hg => ?_
  obtain ⟨S, hS, hS'⟩ := h V g hg
  exact ⟨S, hS, fun W k hk => by obtain ⟨z, hz⟩ := hS' W k hk; exact ⟨z, by rw [hz, res_comp]⟩⟩

theorem good_add {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} {x x' : Sec G U} (h : Good φ U x) (h' : Good φ U x') :
    Good φ U (x + x') :=
  loc_mono (loc_and h h') fun _ g ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩ => ⟨z + z', by rw [smap_add, sres_add, hz, hz']⟩

theorem good_zero {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Good φ U 0 := good_of φ ⟨0, smap_zero _⟩

end GlobalTheory.EtC.TwMulSurj

namespace GlobalTheory.EtC


open TwMulSurj in
theorem tw_mul_locSurj : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {K : Cx (ZMod q)}
    (τ : Pair (sgl (tw q i)) (sgl (tw q j)) K), τ.IsTensor → ∀ φ : tw q k ⟶ K.X 0,
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen k ζ) =
      τ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) →
    ∀ (U : Scheme.{0}) (y : Sec (K.X 0) U), Loc U fun V g => ∃ z : Sec (tw q k) V, Sec.map φ z = Sec.res g y := by
  intro q _ i j k hk K τ hτ φ hφ
  have hT := GlobalTheory.T.tateTwist_sections_locally_generated
  have key_gen : ∀ V (a : Sec (tw q i) V) (b : Sec (tw q j) V),
      Good φ V (τ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) a) (Sec.map (sglι _) b)) := by
    intro V a b
    refine good_bind φ _ ((hT q i).1 V a) ?_
    rintro W g (ha | ⟨ζ, c, ha⟩)
    · apply good_of
      refine ⟨0, ?_⟩
      rw [smap_zero, τ.nat, res_map, res_map, ha, smap_zero]
      simp
    · refine good_bind φ _ ((hT q j).2.1 W ζ (Sec.res g b)) ?_
      rintro W' g' ⟨c', hb⟩
      apply good_of
      refine ⟨(c * c') • twGen k (ζ.map g'.appTop.hom), ?_⟩
      rw [smap_nsmul, hφ, τ.nat, τ.nat, res_map, res_map, res_map, res_map, ha, hb, sres_nsmul, (hT q i).2.2.2.1, smap_nsmul, smap_nsmul]
      simp [mul_comm, mul_smul]
  have key : ∀ V (x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0), Good φ V (τ.lift V 0 x) := by
    intro V x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact good_zero φ V
    | of p t =>
      obtain ⟨⟨s, t'⟩, hst⟩ := p
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact good_zero φ V
      | add u u' hu hu' => rw [map_add (f := _), map_add (f := _)]; exact good_add φ hu hu'
      | tmul a b =>
        have hlift : τ.lift V 0 (DirectSum.of _ ⟨(s, t'), hst⟩ (a ⊗ₜ b)) = τ.mul V s t' 0 hst a b := by
          unfold Pair.lift
          erw [DirectSum.toModule_lof]
          rfl
        rw [hlift]
        by_cases hs : s = 0
        · subst hs
          obtain rfl : t' = 0 := by omega
          have ea : Sec.map (sglι _) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)).hom a) = a := by
            refine (map_comp_apply _ (sglι _) a).symm.trans ?_
            simp [sglι]; rfl
          have eb : Sec.map (sglι _) (Sec.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q j)).hom b) = b := by
            refine (map_comp_apply _ (sglι _) b).symm.trans ?_
            simp [sglι]; rfl
          rw [← ea, ← eb]
          exact key_gen V _ _
        · have h0 : τ.mul V s t' 0 hst a b = 0 := by
            rw [eq_zero_of_isZero (F := (sgl (tw q i)).X s) (HomologicalComplex.isZero_single_obj_X _ _ _ _ hs) a]
            simp
          rw [h0]
          exact good_zero φ V
    | add x x' hx hx' => rw [map_add (f := _)]; exact good_add φ hx hx'
  intro U y
  exact good_bind φ y (hτ.1 U 0 y) fun V g ⟨x, hx⟩ => hx ▸ key V x

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

noncomputable section
namespace GlobalTheory.EtC.MuTw

theorem appTop_comp_apply' {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Γ(U, ⊤)) :
    (k ≫ g).appTop.hom a = k.appTop.hom (g.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem isUnit_natCast_of_hom {V U : Scheme.{0}} (g : V ⟶ U) (q : ℕ) (hq : IsUnit (q : Γ(U, ⊤))) :
    IsUnit (q : Γ(V, ⊤)) := by
  have := hq.map g.appTop.hom
  rwa [map_natCast] at this

theorem muVal_pow (q : ℕ) [NeZero q] {U : Scheme.{0}} (y : Sec (muS q) U) : muVal q y ^ q = 1 := by
  have hr := (mem_rootsOfUnity q _).1 (Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(U, ⊤))) y)).2
  change (( _ : Γ(U, ⊤)ˣ) : Γ(U, ⊤)) ^ q = 1
  rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]

theorem etaS_lift_pow (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (z : Sec (muS q) V) (a : ℕ)
    (h : muVal q z = ζ.1 ^ a) :
    Sec.map (etaS q) (ofRings.sec (twF q 1) V
      (Submodule.Quotient.mk (Finsupp.single ζ (ULift.up (a : ZMod q))))) = z := by
  refine (etaS_sec q V _).trans ((eta_mk q Γ(V, ⊤) ζ _).trans ?_)
  apply muVal_injective q V
  rw [h]
  change (((Additive.toMul (((a : ZMod q)) • Additive.ofMul (root q ζ)) : rootsOfUnity q Γ(V, ⊤)) :
    Γ(V, ⊤)ˣ) : Γ(V, ⊤)) = _
  rw [smul_eq, toMul_nsmul, toMul_ofMul, root_pow_coe, ZMod.val_natCast]
  exact (pow_eq_pow_mod a (prim_pow q ζ)).symm

end GlobalTheory.EtC.MuTw

namespace GlobalTheory.EtC.MuTw

theorem etaS_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Function.Surjective ((etaS q).hom.app (op U)).hom := by
  intro q _ U hq y
  have hloc : Loc U fun V g => ∃ s : Sec (tw q 1) V, Sec.map (etaS q) s = Sec.res g y := by
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.1 U _ ?_
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq) ?_
    rintro V g ⟨ζ⟩
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _
      ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ (muVal q (Sec.res g y)) (muVal_pow q _)) ?_
    rintro W k ⟨a, ha⟩
    refine ⟨_, etaS_lift_pow q W (Prim.map k.appTop.hom ζ) (Sec.res (k ≫ g) y) a ?_⟩
    rw [muVal_res, appTop_comp_apply', ← muVal_res, ha]
    rfl
  obtain ⟨S, hS, hSy⟩ := hloc
  choose s hs using hSy
  have hsh := (tw q 1).property
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsh
  let fam : Presieve.FamilyOfElements ((tw q 1).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows :=
    fun V g hg => s V g hg
  have hfam : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    apply GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q Z (isUnit_natCast_of_hom (g₁ ≫ f₁) q hq)
    change Sec.map (etaS q) (Sec.res g₁ (s _ f₁ h₁)) = Sec.map (etaS q) (Sec.res g₂ (s _ f₂ h₂))
    rw [etaS_res, etaS_res, hs, hs]
    apply muVal_injective q Z
    simp only [muVal_res]
    rw [← appTop_comp_apply', ← appTop_comp_apply', e]
  obtain ⟨x, hx, -⟩ := hsh S hS fam hfam
  refine ⟨x, ?_⟩
  have hsep := (muS q).property
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsep
  refine (hsep S hS).isSeparatedFor.ext (fun V g hg => ?_)
  change Sec.res g (Sec.map (etaS q) x) = Sec.res g y
  rw [← etaS_res]
  have h1 : Sec.res g x = s V g hg := hx g hg
  rw [h1, hs]

end GlobalTheory.EtC.MuTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionMapExistsUniqueHomotopy
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.TwResExt

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (f : F ⟶ G) (g : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem twRes_ext : ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧
    (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
    IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧
    ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u') := by
  intro q _ i
  obtain ⟨hKI, hInj, hGE, hQI, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (tw q i)
  refine ⟨⟨hGE, resAug _, hQI, fun _ _ => rfl⟩, fun t => ?_, ?_⟩
  · haveI := hInj t
    exact (GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf q ((res _ (tw q i)).X t)).2
  intro T e ⟨_, ε, hε, he⟩
  have hext := GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) (tw q i) T (res _ (tw q i)) ε
  refine ⟨?_, fun u u' huu => ?_⟩
  · obtain ⟨m, hm⟩ := hext.1 (resAug _)
    refine ⟨m, fun U ζ => ?_⟩
    rw [← he U ζ, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]
    rfl
  · refine hext.2 u u' ?_
    have htw := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2
    obtain ⟨hres, hrel, huniq⟩ := htw
    let ψ : (T ⟶ res _ (tw q i)) → (tw q i ⟶ (res _ (tw q i)).X 0) := fun v => sglι (tw q i) ≫ (ε ≫ v).f 0
    have key : ∀ v : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (ψ v) (twGen i ζ) = Sec.map (v.f 0) (e U ζ) := by
      intro v U ζ
      rw [← he U ζ]
      rfl
    have hnat : ∀ v : T ⟶ res _ (tw q i), ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
        Sec.res g (Sec.map (ψ v) (twGen i ζ)) = Sec.map (ψ v) (twGen i (ζ.map g.appTop.hom)) := by
      intro v V U g ζ
      rw [← hres V U g ζ]
      exact (congrArg (fun f => f.hom (twGen i ζ)) ((ψ v).hom.naturality g.op)).symm
    have hrl : ∀ v : T ⟶ res _ (tw q i), ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ),
        ξ.1 = ζ.1 ^ (a : ZMod q).val →
        Sec.map (ψ v) (twGen i ξ) = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • Sec.map (ψ v) (twGen i ζ) := by
      intro v U ζ ξ a h
      rw [hrel U ζ ξ a h]
      exact map_nsmul _ _ _
    obtain ⟨φ, -, hφ⟩ := huniq ((res _ (tw q i)).X 0) (fun U ζ => Sec.map (ψ u) (twGen i ζ)) (hnat u) (hrl u)
    have h1 := hφ (ψ u) fun U ζ => rfl
    have h2 := hφ (ψ u') fun U ζ => by rw [key, key, huu]
    have h12 : ψ u = ψ u' := h2.symm ▸ h1 ▸ rfl
    apply HomologicalComplex.from_single_hom_ext
    exact (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)) _ _).1 h12

end GlobalTheory.EtC.TwResExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSheafIsLocallyFlatStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistSheaf_isLocallyFlat : ∀ (q : ℕ) [NeZero q] (i : ℤ), FlatS (tw q i) := by
  first | (exact @GlobalTheory.EtC.flatS_tw) | (exact GlobalTheory.EtC.flatS_tw) | (intros; apply GlobalTheory.EtC.flatS_tw  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatEtaleSheafPreservesLocalExactnessStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_flat_etaleSheaf_preserves_local_exactness : ∀ (R : Type) [CommRing R] (M : Shv R), FlatS M → ∀ {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C), f ≫ g = 0 → (∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b) → ∀ U (x : TensorProduct (ULift.{1} R) (Sec B U) (Sec M U)), (Loc U fun V k => LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) = 0) → Loc U fun V k => ∃ y : TensorProduct (ULift.{1} R) (Sec A V) (Sec M V), LinearMap.rTensor _ (f.hom.app (op V)).hom y = TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x := by
  first | (exact @GlobalTheory.EtC.tensor_flat_loc_exact) | (exact GlobalTheory.EtC.tensor_flat_loc_exact) | (intros; apply GlobalTheory.EtC.tensor_flat_loc_exact  <;> assumption)
end

