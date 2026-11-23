module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0012
public import Development.EtaleCohomology.TateTwists.Bundle0010
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.TateTwists.Bundle0008

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductFamilyOfGluing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensTriFamPf

def SecGlue : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

variable {R : Type} [CommRing R]

lemma res_id {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

lemma res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

lemma res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add _ _ _

lemma res_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift.{1} R) (a : Sec F U) :
    Sec.res g (r • a) = r • Sec.res g a := map_smul _ _ _

lemma loc_inter {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨S', hS', hSQ⟩ := hQ
  exact ⟨S ⊓ S', Scheme.etaleTopology.intersection_covering hS hS', fun V g hg => ⟨hSP V g hg.1, hSQ V g hg.2⟩⟩

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

lemma loc_pull {U V : Scheme.{0}} (k : V ⟶ U) {P : ∀ W : Scheme.{0}, (W ⟶ U) → Prop} (hP : Loc U P) :
    Loc V fun W h => P W (h ≫ k) := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S.pullback k, Scheme.etaleTopology.pullback_stable k hS, fun W h hh => hSP W _ hh⟩

section
variable {I J K T M L : Cx R}

lemma lift_res (τ : Pair I J T) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    τ.lift V w (Tens.res g w x) = Sec.res g (τ.lift U w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [Pair.lift, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.map_tmul,
        TensorProduct.lift.tmul]
      exact (τ.nat g _ _ _ _ a b).symm
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
  | add x x' hx hx' => simp only [map_add (f := _), hx, hx']

lemma lift_single (τ : Pair I J T) (U : Scheme.{0}) (s t st : ℤ) (h1 : s + t = st) (a : Sec (I.X s) U)
    (b : Sec (J.X t) U) :
    τ.lift U st (DirectSum.of _ (⟨(s, t), h1⟩ : {p : ℤ × ℤ // p.1 + p.2 = st}) (a ⊗ₜ[ULift.{1} R] b)) =
      τ.mul U s t st h1 a b := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]

noncomputable def Bp (μ' : Pair J K M) (ν' : Pair I M L) (V : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w)
    (p : {p : ℤ × ℤ // p.1 + p.2 = st}) :
    Sec (I.X p.1.1) V →ₗ[ULift.{1} R] Sec (J.X p.1.2) V →ₗ[ULift.{1} R] (Sec (K.X u) V →ₗ[ULift.{1} R] Sec (L.X w) V) :=
  LinearMap.mk₂ (ULift.{1} R)
    (fun a b => (ν'.mul V p.1.1 (p.1.2 + u) w (by have := p.2; omega) a) ∘ₗ (μ'.mul V p.1.2 u (p.1.2 + u) rfl b))
    (fun a a' b => LinearMap.ext fun c => by simp)
    (fun r a b => LinearMap.ext fun c => by simp)
    (fun a b b' => LinearMap.ext fun c => by simp)
    (fun r a b => LinearMap.ext fun c => by simp)

noncomputable def B (μ' : Pair J K M) (ν' : Pair I M L) (V : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) :
    Tens I J V st →ₗ[ULift.{1} R] (Sec (K.X u) V →ₗ[ULift.{1} R] Sec (L.X w) V) :=
  DirectSum.toModule _ _ _ fun p => TensorProduct.lift (Bp μ' ν' V st u w h2 p)

lemma B_single (μ' : Pair J K M) (ν' : Pair I M L) (V : Scheme.{0}) (s t st u w : ℤ) (h1 : s + t = st)
    (h2 : st + u = w) (a : Sec (I.X s) V) (b : Sec (J.X t) V) (c : Sec (K.X u) V) :
    B μ' ν' V st u w h2 (DirectSum.of _ (⟨(s, t), h1⟩ : {p : ℤ × ℤ // p.1 + p.2 = st}) (a ⊗ₜ[ULift.{1} R] b)) c =
      ν'.mul V s (t + u) w (by omega) a (μ'.mul V t u (t + u) rfl b c) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [B, Bp, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.mk₂_apply, LinearMap.comp_apply]

lemma B_res (μ' : Pair J K M) (ν' : Pair I M L) {W V : Scheme.{0}} (k : W ⟶ V) (st u w : ℤ) (h2 : st + u = w)
    (x : Tens I J V st) (c : Sec (K.X u) V) :
    Sec.res k (B μ' ν' V st u w h2 x c) = B μ' ν' W st u w h2 (Tens.res k st x) (Sec.res k c) := by
  induction x using DirectSum.induction_on with
  | zero => simp [Sec.res]
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp [Sec.res]
    | tmul a b =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [B, Bp, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.map_tmul,
        TensorProduct.lift.tmul, LinearMap.mk₂_apply, LinearMap.comp_apply]
      rw [ν'.nat, μ'.nat]
    | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy']
  | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx']

end

section
variable {I J K T M L : Cx R}

lemma B_wd (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)
    {V : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} {x y : Tens I J V st} (c : Sec (K.X u) V)
    (h : τ.lift V st x = τ.lift V st y) : B μ' ν' V st u w h2 x c = B μ' ν' V st u w h2 y c := by
  have h0 : τ.lift V st (x - y) = 0 := by rw [map_sub, h, sub_self]
  refine (hg R (L.X w) V).1 _ _ (loc_mono (hτ.2 V st (x - y) h0) fun W k hk => ?_)
  rw [map_sub, sub_eq_zero] at hk
  rw [B_res, B_res, hk]

lemma exists_m (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)
    (U : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    ∃ m0 : Sec (L.X w) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : Tens I J V st), τ.lift V st x = Sec.res g a →
      Sec.res g m0 = B μ' ν' V st u w h2 x (Sec.res g c) := by
  obtain ⟨S, hS, hP⟩ := hτ.1 U st a
  obtain ⟨m0, hm0⟩ := (hg R (L.X w) U).2 S hS
    (fun V g hg' => B μ' ν' V st u w h2 (hP V g hg').choose (Sec.res g c)) (by
      intro V W g k hg'
      rw [B_res, res_comp k g c]
      apply B_wd hg τ hτ μ' ν'
      rw [lift_res, (hP V g hg').choose_spec, (hP W (k ≫ g) (S.downward_closed hg' k)).choose_spec, res_comp])
  refine ⟨m0, fun V g x hx => ?_⟩
  apply (hg R (L.X w) V).1
  refine loc_mono (loc_pull g (P := fun W h => S.arrows h) ⟨S, hS, fun _ _ h => h⟩) fun W k hk => ?_
  rw [← res_comp, hm0 W (k ≫ g) hk, B_res, ← res_comp]
  apply B_wd hg τ hτ μ' ν'
  rw [lift_res, (hP W (k ≫ g) hk).choose_spec, hx, res_comp]

noncomputable def mraw (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)
    (U : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) (a : Sec (T.X st) U) (c : Sec (K.X u) U) : Sec (L.X w) U :=
  (exists_m hg τ hτ μ' ν' U st u w h2 a c).choose

variable (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)

lemma res_mraw_eq_of_lift {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (a : Sec (T.X st) U) (c : Sec (K.X u) U)
    {V : Scheme.{0}} (g : V ⟶ U) (x : Tens I J V st) (hx : τ.lift V st x = Sec.res g a) :
    Sec.res g (mraw hg τ hτ μ' ν' U st u w h2 a c) = B μ' ν' V st u w h2 x (Sec.res g c) :=
  (exists_m hg τ hτ μ' ν' U st u w h2 a c).choose_spec V g x hx

lemma mraw_add_a {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (a a' : Sec (T.X st) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 (a + a') c = mraw hg τ hτ μ' ν' U st u w h2 a c + mraw hg τ hτ μ' ν' U st u w h2 a' c := by
  apply (hg R (L.X w) U).1
  refine loc_mono (loc_inter (hτ.1 U st a) (hτ.1 U st a')) fun V g hV => ?_
  obtain ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ := hV
  rw [res_add, res_mraw_eq_of_lift hg τ hτ μ' ν' (a + a') c g (x + x') (by rw [map_add (f := _), hx, hx', res_add]),
    res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx, res_mraw_eq_of_lift hg τ hτ μ' ν' a' c g x' hx', map_add, LinearMap.add_apply]

lemma mraw_smul_a {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (r : ULift.{1} R) (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 (r • a) c = r • mraw hg τ hτ μ' ν' U st u w h2 a c := by
  apply (hg R (L.X w) U).1
  refine loc_mono (hτ.1 U st a) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  rw [res_smul, res_mraw_eq_of_lift hg τ hτ μ' ν' (r • a) c g (r • x) (by rw [map_smul, hx, res_smul]),
    res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx, map_smul, LinearMap.smul_apply]

lemma mraw_add_c {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (a : Sec (T.X st) U) (c c' : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 a (c + c') = mraw hg τ hτ μ' ν' U st u w h2 a c + mraw hg τ hτ μ' ν' U st u w h2 a c' := by
  apply (hg R (L.X w) U).1
  refine loc_mono (hτ.1 U st a) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  rw [res_add, res_mraw_eq_of_lift hg τ hτ μ' ν' a (c + c') g x hx, res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx,
    res_mraw_eq_of_lift hg τ hτ μ' ν' a c' g x hx, res_add, map_add]

lemma mraw_smul_c {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (r : ULift.{1} R) (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 a (r • c) = r • mraw hg τ hτ μ' ν' U st u w h2 a c := by
  apply (hg R (L.X w) U).1
  refine loc_mono (hτ.1 U st a) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  rw [res_smul, res_mraw_eq_of_lift hg τ hτ μ' ν' a (r • c) g x hx, res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx, res_smul, map_smul]

lemma mraw_nat {V U : Scheme.{0}} (g' : V ⟶ U) {st u w : ℤ} {h2 : st + u = w} (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    Sec.res g' (mraw hg τ hτ μ' ν' U st u w h2 a c) = mraw hg τ hτ μ' ν' V st u w h2 (Sec.res g' a) (Sec.res g' c) := by
  apply (hg R (L.X w) V).1
  refine loc_mono (hτ.1 V st (Sec.res g' a)) fun W k hW => ?_
  obtain ⟨x, hx⟩ := hW
  rw [← res_comp, res_mraw_eq_of_lift hg τ hτ μ' ν' a c (k ≫ g') x (by rw [hx, res_comp]),
    res_mraw_eq_of_lift hg τ hτ μ' ν' (Sec.res g' a) (Sec.res g' c) k x hx, res_comp]

lemma mraw_eq (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu)
    (h4 : s + tu = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c) := by
  subst h3
  have h := res_mraw_eq_of_lift hg τ hτ μ' ν' (h2 := h2) (τ.mul U s t st h1 a b) c (𝟙 U)
    (DirectSum.of _ (⟨(s, t), h1⟩ : {p : ℤ × ℤ // p.1 + p.2 = st}) (a ⊗ₜ[ULift.{1} R] b))
    (by rw [lift_single, res_id])
  rw [res_id, res_id] at h
  rw [h, B_single]

noncomputable def mfam (U : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) :
    Sec (T.X st) U →ₗ[ULift.{1} R] Sec (K.X u) U →ₗ[ULift.{1} R] Sec (L.X w) U :=
  LinearMap.mk₂ (ULift.{1} R) (mraw hg τ hτ μ' ν' U st u w h2)
    (mraw_add_a hg τ hτ μ' ν') (mraw_smul_a hg τ hτ μ' ν') (mraw_add_c hg τ hτ μ' ν') (mraw_smul_c hg τ hτ μ' ν')

end

end LateralTheory.EtaleFoundations.TensTriFamPf


open LateralTheory.EtaleFoundations.TensTriFamPf in
theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_family_of_gluing (hglue : SecGlue) : LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists := by
  intro R _ I J K T τ hτ M L μ' ν'
  refine ⟨fun U st u w h2 => mfam hglue τ hτ μ' ν' U st u w h2, ?_, ?_⟩
  · intro V U g s t w h a b
    exact mraw_nat hglue τ hτ μ' ν' g a b
  · intro U s t u st tu w h1 h2 h3 h4 a b c
    exact mraw_eq hglue τ hτ μ' ν' U s t u st tu w h1 h2 h3 h4 a b c
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductLeibnizOfSeparated
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

def SecSep : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U),
    (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b

lemma res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  exact congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op).symm

lemma res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ x y

lemma res_usmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (x : Sec F U) :
    Sec.res g (u • x) = u • Sec.res g x := by
  simp only [Units.smul_def]; exact map_zsmul _ _ x

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hP V g hg)⟩

lemma leib_lift {R : Type} [CommRing R] {I J K T M L : Cx R} (τ : Pair I J T) (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U)
    (heq : ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c))
    (V : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (x : Tens I J V s) (b : Sec (K.X t) V) :
    Sec.map (L.d w (w + 1)) (m V s t w h (τ.lift V s x) b) = m V (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) (τ.lift V s x)) b +
          s.negOnePow • m V s (t + 1) (w + 1) (by omega) (τ.lift V s x) (Sec.map (K.d t (t + 1)) b) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
    rw [hx, hy]; abel
  | of p z =>
    obtain ⟨⟨s1, t1⟩, hp⟩ := p
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add (f := _), LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
      rw [hx, hy]; abel
    | tmul a1 b1 =>
      have hl : τ.lift V s (DirectSum.of _ ⟨(s1, t1), hp⟩ (a1 ⊗ₜ b1)) = τ.mul V s1 t1 s hp a1 b1 := by
        unfold Pair.lift
        rw [← DirectSum.lof_eq_of (ULift.{1} R), DirectSum.toModule_lof, TensorProduct.lift.tmul]
      simp only at hp
      rw [hl, τ.leibniz V s1 t1 s hp a1 b1]
      rw [heq V s1 t1 t s (t1 + t) w hp h (by omega) (by omega)]
      rw [ν'.leibniz V s1 (t1 + t) w (by omega), μ'.leibniz V t1 t (t1 + t) rfl]
      simp only [map_add (f := _), LinearMap.add_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]
      rw [heq V (s1 + 1) t1 t (s + 1) (t1 + t) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 (t1 + 1) t (s + 1) (t1 + t + 1) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 t1 (t + 1) s (t1 + t + 1) (w + 1) hp (by omega) (by omega) (by omega)]
      have hs : ((s.negOnePow : ℤˣ) : ℤ) = (s1.negOnePow : ℤ) * (t1.negOnePow : ℤ) := by
        rw [← Units.val_mul, ← Int.negOnePow_add, hp]
      rw [hs, mul_smul, smul_add]
      abel

end LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

open LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated in
theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_leibniz_of_separated (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) :
    LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz := by
  intro R _ I J K T τ hτ M L μ' ν' m hnat heq U s t w h a b
  apply hsep R (L.X (w + 1)) U
  refine loc_mono (hτ.1 U s a) ?_
  rintro V g ⟨x, hx⟩
  rw [res_map, hnat, res_add, res_usmul, hnat, hnat, res_map, res_map, ← hx, leib_lift τ μ' ν' m heq]
end

-- bundled from Development.EtaleCohomology.TateTwists.ExactLocPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExactLocPf

variable {R : Type} [CommRing R]

lemma kernel_lift_sec (S : ShortComplex (Shv R)) (U : Scheme.{0}) (b : Sec S.X₂ U)
    (hb : Sec.map S.g b = 0) : ∃ k : Sec (kernel S.g) U, Sec.map (kernel.ι S.g) k = b := by
  let T : ShortComplex (Shv R) := ShortComplex.mk (kernel.ι S.g) S.g (kernel.condition _)
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel S.g)
  have : Mono T.f := by dsimp [T]; infer_instance
  have hE : (T.map (LateralTheory.EtaleFoundations.ResSecPf.secF R U)).Exact :=
    hT.map_of_mono_of_preservesKernel _ this inferInstance
  rw [ShortComplex.moduleCat_exact_iff] at hE
  exact hE b hb

lemma epi_lift (S : ShortComplex (Shv R)) (hS : S.Exact) :
    Epi (kernel.lift S.g S.f S.zero) := by
  exact hS.epi_kernelLift

end LateralTheory.EtaleFoundations.ExactLocPf

open LateralTheory.EtaleFoundations.ExactLocPf in
theorem LateralTheory.EtaleFoundations.ResSecPf.exact_loc_of : LateralTheory.EtaleFoundations.ResSecPf.exact_loc := by
  intro R _ S hS U b hb
  obtain ⟨k, hk⟩ := kernel_lift_sec S U b hb
  let p := kernel.lift S.g S.f S.zero
  have : Epi p := epi_lift S hS
  have hls : Sheaf.IsLocallySurjective p := (Sheaf.isLocallySurjective_iff_epi' (φ := p)).2 this
  refine ⟨Presheaf.imageSieve p.hom k, Presheaf.imageSieve_mem Scheme.etaleTopology p.hom (U := op U) k, ?_⟩
  rintro V g ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have e1 : S.f = p ≫ kernel.ι S.g := (kernel.lift_ι _ _ _).symm
  have e2 : Sec.map S.f a = Sec.map (kernel.ι S.g) (Sec.map p a) := by
    rw [e1]; rfl
  rw [e2, ← hk]
  change Sec.map (kernel.ι S.g) ((p.hom.app _).hom a) = _
  have ha' : (p.hom.app (op V)).hom a = ((kernel S.g).obj.map g.op).hom k := ha
  rw [ha']
  exact congrArg (fun f => f.hom k) ((kernel.ι S.g).hom.naturality g.op)
end

-- bundled from Development.EtaleCohomology.TateTwists.ExistsEtaleMonoMuTwistIntoTorsorSheafOfMuQuotien
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.EtaleFoundations

noncomputable def twGenR {q : ℕ} (A : CommRingCat.{0}) (ζ : Prim q A) : (twF q 1).obj A :=
  Submodule.Quotient.mk (Finsupp.single ζ 1)

def ExistsEtaleMonoMuTwistKillingRootRelations : Prop :=
  ∀ (q : ℕ) [NeZero q], ∃ (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) ∧
    ∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0

def EtaleMuTwistMonoExtendsToTorsorSheaf : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} (ZMod q))) (τ : twF q 1 ⟶ T),
    Mono ((presheafToSheaf Scheme.etaleTopology _).map (Functor.whiskerLeft Scheme.Γ τ)) →
    (∀ (A : CommRingCat.{0}) (l : List (Prim q A)), (l.map fun ζ => ζ.1).prod = 1 →
      (l.map fun ζ => (τ.app A).hom (twGenR A ζ)).sum = 0) →
    ∃ (M : Shv (ZMod q)) (j : tw q 1 ⟶ M), Mono j ∧
    ∃ s : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec M U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (q : Γ(U, ⊤)) →
        Sec.res g (s U v) = s V (Units.map g.appTop.hom.toMonoidHom v)) ∧
      ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 * v →
        s U w = s U v + Sec.map j (twGen 1 ζ)

theorem exists_etale_mono_muTwist_into_torsorSheaf (h1 : ExistsEtaleMonoMuTwistKillingRootRelations) (h2 : EtaleMuTwistMonoExtendsToTorsorSheaf) :
    EtaleKummerSectionsIntoTwistEmbeddingExist := by
  intro q _
  obtain ⟨T, τ, hm, hl⟩ := h1 q
  exact h2 q T τ hm hl
end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.FreeExt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwExPf

variable {R : Type} [CommRing R]

theorem free_ext (P : PSh) (F : Shv R) (φ ψ : (free R).obj P ⟶ F)
    (h : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  let φ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := φ
  let ψ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := ψ
  change φ' = ψ'
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine NatTrans.ext (funext fun U => ModuleCat.free_hom_ext fun x => ?_)
  exact h U.unop x.down

theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  refine Cochain.ext _ _ (fun i j hij => ?_)
  by_cases hi : 0 ≤ -i
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ _ _ fun U x => h p j hij U x
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i' hi'
    change -(i' : ℤ) = i at hi'
    omega

end LateralTheory.EtaleFoundations.AwExPf
end

-- bundled from Development.EtaleCohomology.TateTwists.KumAddPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def IsKumCoc (q : ℕ) [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ)
    (γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) : Prop :=
  (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
  ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
    ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def kum_uniq : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∀ γ γ' : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q u γ → IsKumCoc q u γ' → CohomologyClass.mk γ = CohomologyClass.mk γ'

def kum_mul_coc : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∀ γu γv : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q u γu → IsKumCoc q v γv →
      ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
        IsKumCoc q (u * v) γ ∧ CohomologyClass.mk γ = CohomologyClass.mk γu + CohomologyClass.mk γv

def kum_pow_coc : Prop :=
  ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    ∃ γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      IsKumCoc q (u ^ q) γ ∧ CohomologyClass.mk γ = 0

theorem kum_add_of (he : kum_exists) (hu : kum_uniq) (hm : kum_mul_coc) (hp : kum_pow_coc) : kum_add := by
  intro q _ X u v hq
  obtain ⟨γu, eu, ku⟩ := kum_spec_of_exists he q X u hq
  obtain ⟨γv, ev', kv⟩ := kum_spec_of_exists he q X v hq
  obtain ⟨γuv, euv, kuv⟩ := kum_spec_of_exists he q X (u * v) hq
  obtain ⟨γp, epw, kpw⟩ := kum_spec_of_exists he q X (u ^ q) hq
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ, hsum⟩ := hm q X u v hq γu γv ku kv
    rw [← euv, ← eu, ← ev', ← hsum]
    exact hu q X (u * v) hq γuv γ kuv hγ
  · obtain ⟨γ, hγ, h0⟩ := hp q X u hq
    rw [← epw, ← h0]
    exact hu q X (u ^ q) hq γp γ kpw hγ

end LateralTheory.EtaleFoundations
end

