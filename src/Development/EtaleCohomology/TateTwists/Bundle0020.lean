module

public import Development.EtaleCohomology.TateTwists.Bundle0013
public import Development.EtaleCohomology.TateTwists.Bundle0002
public import Development.EtaleCohomology.TateTwists.Bundle0003
public import Development.EtaleCohomology.TateTwists.Bundle0008
public import Development.EtaleCohomology.TateTwists.Bundle0009
public import Development.EtaleCohomology.KummerTheory.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.V1

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Loc V (fun W k => Q W (k ≫ g))) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let R : ∀ ⦃Y⦄ ⦃f : Y ⟶ U⦄, S.arrows f → Sieve Y := fun Y f H => (hPQ Y f (hP Y f H)).choose
  refine ⟨Sieve.bind S.arrows R, Scheme.etaleTopology.bind_covering hS
    (fun Y f H => (hPQ Y f (hP Y f H)).choose_spec.1), ?_⟩
  rintro W _ ⟨Y, k, f, H, hk, rfl⟩
  exact (hPQ Y f (hP Y f H)).choose_spec.2 W k hk

theorem sec_res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (s : Sec F U) : Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sec_res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (s : Sec F U) :
    Sec.res (𝟙 U) s = s := by
  simp only [Sec.res, op_id, CategoryTheory.Functor.map_id]; rfl

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (s : Sec F U) : Sec.res g (Sec.map φ s) = Sec.map φ (Sec.res g s) := by
  simp only [Sec.res, Sec.map]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    φ.hom.naturality]

theorem sx_res_comp {E : Spc} {p : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sx E p U) :
    (x.res g).res k = x.res (k ≫ g) := by
  simp only [Sx.res, op_comp, CategoryTheory.Functor.map_comp_apply]

theorem sx_res_id {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : x.res (𝟙 U) = x := by
  simp only [Sx.res, op_id, CategoryTheory.Functor.map_id_apply]

theorem units_map_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) =
      Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  ext; simp [Scheme.Hom.comp_appTop]; rfl

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (s : Sec F U) : Sec.map ψ (Sec.map φ s) = Sec.map (φ ≫ ψ) s := rfl

theorem d_resGen (q : ℕ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    Sec.map ((res _ (tw q 1)).d 0 1) (resGen 1 ζ) = 0 := by
  have h : resι _ (tw q 1) ≫ (res _ (tw q 1)).d 0 1 = 0 := by
    have hc : (injectiveResolution (tw q 1)).ι'.f 0 ≫ (injectiveResolution (tw q 1)).cochainComplex.d 0 1 = 0 := by
      rw [(injectiveResolution (tw q 1)).ι'.comm 0 1]; simp
    exact (Category.assoc _ _ _).trans ((congrArg (fun f => _ ≫ f) hc).trans Limits.comp_zero)
  rw [resGen, sec_map_comp, h]
  simp [Sec.map]

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  simp only [lineUnit, Sx.res]
  rw [NatTrans.naturality_apply]
  change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map g.appTop.hom (glMat ((L.app _).app (op U) x))) = _
  ext
  simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]

noncomputable abbrev dkT (q : ℕ) (V : Scheme.{0}) (v : (Γ(V, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 1) V :=
  Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V v)

theorem isUnit_res {q : ℕ} {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hU.map g.appTop.hom

theorem kT_nat {q : ℕ} (hk : IsKum q (kumT q)) {V U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (g : V ⟶ U)
    (v : (Γ(U, ⊤))ˣ) : Sec.res g (dkT q U v) = dkT q V (Units.map g.appTop.hom.toMonoidHom v) := by
  rw [dkT, sec_res_map, hk.1 V U g v hU]

theorem kT_pow {q : ℕ} (hk : IsKum q (kumT q)) {W : Scheme.{0}} (ζ : Prim q Γ(W, ⊤)) (w : (Γ(W, ⊤))ˣ) (a : ℕ) :
    ∀ w' : (Γ(W, ⊤))ˣ, (w' : Γ(W, ⊤)) = ζ.1 ^ a * w → dkT q W w' = dkT q W w := by
  induction a with
  | zero => intro w' h; have : w' = w := Units.ext (by simpa using h); subst this; rfl
  | succ n ih =>
    intro w' h
    have hu : IsUnit (ζ.1 ^ n * (w : Γ(W, ⊤))) :=
      isUnit_of_mul_isUnit_right (x := ζ.1) (by rw [← mul_assoc, ← pow_succ', ← h]; exact w'.isUnit)
    have e : (w' : Γ(W, ⊤)) = ζ.1 * (hu.unit : Γ(W, ⊤)) := by rw [IsUnit.unit_spec, h, pow_succ', mul_assoc]
    rw [dkT, hk.2 W ζ hu.unit w' e]
    simp only [Sec.map, map_add (f := _)]
    have h0 := d_resGen q ζ
    simp only [Sec.map] at h0
    rw [h0, add_zero]
    exact ih hu.unit (IsUnit.unit_spec hu)

theorem indep {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : IsKum q (kumT q))
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) {V : Scheme.{0}} (hV : IsUnit (q : Γ(V, ⊤))) (v v' : (Γ(V, ⊤))ˣ)
    (h : v ^ q = v' ^ q) : dkT q V v = dkT q V v' := by
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) V).1
  refine loc_bind ((hp q V).1 hV) ?_
  rintro W g ⟨ζ⟩
  have h1 : (v' * v⁻¹) ^ q = 1 := by rw [mul_pow, inv_pow, ← h, mul_inv_cancel]
  have hx : ((Units.map g.appTop.hom.toMonoidHom (v' * v⁻¹) : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, map_one, Units.val_one]
  refine loc_mono ((hp q W).2.2.1 ζ _ hx) ?_
  rintro W' k ⟨a, ha⟩
  rw [kT_nat hk hV, kT_nat hk hV]
  have hx' : ((Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom (v' * v⁻¹)) : (Γ(W', ⊤))ˣ) : Γ(W', ⊤))
      = (Prim.map k.appTop.hom ζ).1 ^ a := ha
  have e : ((Units.map (k ≫ g).appTop.hom.toMonoidHom v' : (Γ(W', ⊤))ˣ) : Γ(W', ⊤)) =
      (Prim.map k.appTop.hom ζ).1 ^ a * (Units.map (k ≫ g).appTop.hom.toMonoidHom v : (Γ(W', ⊤))ˣ) := by
    rw [← units_map_comp, ← units_map_comp, ← hx', ← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel_right]
  exact (kT_pow hk _ _ a _ e).symm

def Q (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 1 U) (s : Sec ((res _ (tw q 1)).X 1) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = lineUnit L (x.res g) → Sec.res g s = dkT q V v

theorem Q_res {q : ℕ} {E : Spc} {L : E ⟶ ofCat (glCat 1)} {V U : Scheme.{0}} {x : Sx E 1 U} {s} (hQ : Q q L x s)
    (g : V ⟶ U) : Q q L (x.res g) (Sec.res g s) := by
  intro W k v hv
  rw [sec_res_comp]
  exact hQ W (k ≫ g) v (by rwa [← sx_res_comp])

theorem Q_uniq {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue)
    {E : Spc} {L : E ⟶ ofCat (glCat 1)} {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) {x : Sx E 1 U} {s s'}
    (hQ : Q q L x s) (hQ' : Q q L x s') : s = s' := by
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) U).1
  refine loc_mono ((hp q U).2.2.2 hU (lineUnit L x)) ?_
  rintro V g ⟨v, hv⟩
  have hv' : v ^ q = lineUnit L (x.res g) := by rw [lineUnit_res]; exact hv
  rw [hQ V g v hv', hQ' V g v hv']

theorem Q_ex {q : ℕ} [NeZero q] (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : IsKum q (kumT q))
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue)
    {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (hU : IsUnit (q : Γ(U, ⊤))) (x : Sx E 1 U) :
    ∃ s, Q q L x s := by
  obtain ⟨S, hS, hr⟩ := (hp q U).2.2.2 hU (lineUnit L x)
  choose vs hvs using hr
  obtain ⟨s, hs'⟩ := (hs (ZMod q) ((res _ (tw q 1)).X 1) U).2 S hS (fun V g hg => dkT q V (vs V g hg)) (by
    intro V W g k hg
    rw [kT_nat hk (isUnit_res hU g)]
    apply indep hp hk hs (isUnit_res hU (k ≫ g))
    rw [← map_pow, hvs V g hg, units_map_comp, hvs W (k ≫ g) _])
  refine ⟨s, fun V g v hv => ?_⟩
  apply (hs (ZMod q) ((res _ (tw q 1)).X 1) V).1
  refine loc_mono (P := fun W h => S.arrows (h ≫ g))
    ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W h hh => hh⟩ ?_
  intro W h hh
  rw [sec_res_comp, hs' W (h ≫ g) hh, kT_nat hk (isUnit_res hU g)]
  apply indep hp hk hs (isUnit_res hU (h ≫ g))
  rw [hvs, ← map_pow, hv, lineUnit_res, units_map_comp]

end LateralTheory.EtaleFoundations.V1

open LateralTheory.EtaleFoundations.V1 in
theorem LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_one_value_of_roots_kummer_gluing (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (hk : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists)
    (hs : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) : LateralTheory.EtaleFoundations.ExistsNaturalEtaleKummerChernClassDegreeOneValue := by
  classical
  intro q _ E L hi
  have hU : ∀ (U : Scheme.{0}) (x : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hi U ⟨x.face 0⟩
  have hex : ∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ s, Q q L x s := fun U x => Q_ex hp (hk q) hs L (hU U x) x
  refine ⟨fun U x => (hex U x).choose, fun V U g x =>
    Q_uniq hp hs (hU V (x.res g)) (Q_res (hex U x).choose_spec g) (hex V (x.res g)).choose_spec, fun U x v hv => ?_⟩
  have h := (hex U x).choose_spec U (𝟙 U) v (by rwa [sx_res_id])
  rwa [sec_res_id] at h
end

-- bundled from Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeTwoValueOfRootsKum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.V2

def PrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def KumTEx : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

def SecGlue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h⟩ := hP
  obtain ⟨T, hT, h'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h V g hg.1, h' V g hg.2⟩⟩

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, h'⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h' V g hg)⟩

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp only [Sec.res, op_comp, Functor.map_comp]; rfl

theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

theorem umap_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

theorem umap_id {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : Units.map (Scheme.Hom.appTop (𝟙 U)).hom.toMonoidHom u = u := by
  ext; simp

theorem unit_res {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (h : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  have := ConcreteCategory.congr_hom ((E.map (SimplexCategory.subinterval j l h).op).naturality g.op) x
  simpa using this

theorem glMat_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    glMat (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op y) = Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := rfl

theorem det_gmap {V U : Scheme.{0}} (g : V ⟶ U) (m : GL (Fin 1) Γ(U, ⊤)) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map g.appTop.hom m) = Units.map g.appTop.hom.toMonoidHom (Matrix.GeneralLinearGroup.det m) := by
  ext
  simp [Matrix.GeneralLinearGroup.map]

theorem lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit Sx.res
  have := ConcreteCategory.congr_hom ((L.app (op (SimplexCategory.mk 1))).naturality g.op) x
  simp only [ConcreteCategory.comp_apply] at this
  rw [this, glMat_res, det_gmap]

noncomputable def fv (q : ℕ) (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  kumT q U v + kumT q U w - kumT q U (v * w)

theorem kumT_pow (hK : KumTEx) (q : ℕ) [NeZero q] {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) :
    ∀ (a : ℕ) (v w : (Γ(U, ⊤))ˣ), (w : Γ(U, ⊤)) = ζ.1 ^ a * v → kumT q U w = kumT q U v + a • resGen 1 ζ := by
  intro a
  induction a with
  | zero => intro v w h; have : w = v := Units.ext (by simpa using h); subst this; simp
  | succ a ih =>
    intro v w h
    have hu : IsUnit (ζ.1 ^ (a + 1)) := by
      rw [show ζ.1 ^ (a + 1) = (w : Γ(U, ⊤)) * ((v⁻¹ : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) by rw [h, mul_assoc]; simp]
      exact (w * v⁻¹).isUnit
    have hz : IsUnit ζ.1 := (isUnit_pow_iff (Nat.succ_ne_zero a)).1 hu
    let m : (Γ(U, ⊤))ˣ := hz.unit ^ a * v
    have hm : kumT q U m = kumT q U v + a • resGen 1 ζ := ih v m (by simp [m])
    have hw : kumT q U w = kumT q U m + resGen 1 ζ := (hK q).2 U ζ m w (by rw [h]; simp [m, pow_succ']; ring)
    rw [hw, hm, succ_nsmul, add_assoc]

theorem res_fv (hK : KumTEx) (q : ℕ) [NeZero q] {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (v w : (Γ(U, ⊤))ˣ) :
    Sec.res g (fv q U v w) = fv q V (Units.map g.appTop.hom.toMonoidHom v) (Units.map g.appTop.hom.toMonoidHom w) := by
  have e : ∀ a b c : Sec ((res _ (tw q 1)).X 0) U, Sec.res g (a + b - c) = Sec.res g a + Sec.res g b - Sec.res g c := by
    intro a b c; simp [Sec.res]
  unfold fv
  rw [e, (hK q).1 V U g v hq, (hK q).1 V U g w hq, (hK q).1 V U g (v * w) hq, map_mul]

theorem umap_root {q : ℕ} {W V : Scheme.{0}} (h : W ⟶ V) (ζ : Prim q Γ(V, ⊤)) (v v' : (Γ(V, ⊤))ˣ) (a : ℕ)
    (ha : h.appTop.hom ((v' * v⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) = h.appTop.hom ζ.1 ^ a) :
    ((Units.map h.appTop.hom.toMonoidHom v' : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      (Prim.map h.appTop.hom ζ).1 ^ a * Units.map h.appTop.hom.toMonoidHom v := by
  have : (v' : Γ(V, ⊤)) = ((v' * v⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) * v := by simp
  show h.appTop.hom (v' : Γ(V, ⊤)) = h.appTop.hom ζ.1 ^ a * h.appTop.hom v
  rw [this, map_mul, ha]

theorem indepA (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤))
    (hq : IsUnit (q : Γ(V, ⊤))) (v v' w w' : (Γ(V, ⊤))ˣ) (hv : v ^ q = v' ^ q) (hw : w ^ q = w' ^ q) :
    fv q V v w = fv q V v' w' := by
  have hx : (((v' * v⁻¹ : (Γ(V, ⊤))ˣ)) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hv, inv_pow, mul_inv_cancel]; rfl
  have hy : (((w' * w⁻¹ : (Γ(V, ⊤))ˣ)) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, ← hw, inv_pow, mul_inv_cancel]; rfl
  apply (hG _ _ V).1
  refine loc_mono (loc_and ((hP q V).2.2.1 ζ _ hx) ((hP q V).2.2.1 ζ _ hy)) ?_
  rintro W h ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  rw [res_fv hK q h hq, res_fv hK q h hq]
  have h1 := umap_root h ζ v v' a ha
  have h2 := umap_root h ζ w w' b hb
  have h3 : ((Units.map h.appTop.hom.toMonoidHom v' * Units.map h.appTop.hom.toMonoidHom w' : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      (Prim.map h.appTop.hom ζ).1 ^ (a + b) * ((Units.map h.appTop.hom.toMonoidHom v * Units.map h.appTop.hom.toMonoidHom w : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) := by
    rw [Units.val_mul, h1, h2, Units.val_mul, pow_add]; ring
  unfold fv
  rw [kumT_pow hK q _ a _ _ h1, kumT_pow hK q _ b _ _ h2, kumT_pow hK q _ (a + b) _ _ h3, add_nsmul]
  abel

theorem indepB (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) (v v' w w' : (Γ(U, ⊤))ˣ) (hv : v ^ q = v' ^ q) (hw : w ^ q = w' ^ q) :
    fv q U v w = fv q U v' w' := by
  apply (hG _ _ U).1
  refine loc_mono ((hP q U).1 hq) ?_
  rintro V g ⟨ζ⟩
  rw [res_fv hK q g hq, res_fv hK q g hq]
  exact indepA hP hK hG q ζ (unit_res g hq) _ _ _ _ (by rw [← map_pow, ← map_pow, hv]) (by rw [← map_pow, ← map_pow, hw])

def Good (q : ℕ) (U : Scheme.{0}) (u1 u2 : (Γ(U, ⊤))ˣ) (a : Sec ((res _ (tw q 1)).X 0) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u1 →
    w ^ q = Units.map g.appTop.hom.toMonoidHom u2 → Sec.res g a = fv q V v w

theorem good_exists (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) (u1 u2 : (Γ(U, ⊤))ˣ) : ∃ a, Good q U u1 u2 a := by
  obtain ⟨S, hS, hS'⟩ := loc_and ((hP q U).2.2.2 hq u1) ((hP q U).2.2.2 hq u2)
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res _ (tw q 1)).X 0) V :=
    fun V g hg => fv q V (hS' V g hg).1.choose (hS' V g hg).2.choose
  obtain ⟨a, ha⟩ := (hG _ _ U).2 S hS s (by
    intro V W g k hg
    simp only [s]
    rw [res_fv hK q k (unit_res g hq)]
    apply indepB hP hK hG q (unit_res (k ≫ g) hq)
    · rw [← map_pow, (hS' V g hg).1.choose_spec, umap_comp, (hS' W (k ≫ g) (S.downward_closed hg k)).1.choose_spec]
    · rw [← map_pow, (hS' V g hg).2.choose_spec, umap_comp, (hS' W (k ≫ g) (S.downward_closed hg k)).2.choose_spec])
  refine ⟨a, fun V g v w hv hw => ?_⟩
  apply (hG _ _ V).1
  refine ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩
  show Sec.res k (Sec.res g a) = Sec.res k (fv q V v w)
  rw [res_comp, ha W (k ≫ g) hk, res_fv hK q k (unit_res g hq)]
  apply indepB hP hK hG q (unit_res (k ≫ g) hq)
  · rw [(hS' W (k ≫ g) hk).1.choose_spec, ← map_pow, hv, umap_comp]
  · rw [(hS' W (k ≫ g) hk).2.choose_spec, ← map_pow, hw, umap_comp]

theorem good_unique (hP : PrimLoc) (hG : SecGlue) (q : ℕ) [NeZero q] {U : Scheme.{0}}
    (hq : IsUnit (q : Γ(U, ⊤))) {u1 u2 : (Γ(U, ⊤))ˣ} {a b : Sec ((res _ (tw q 1)).X 0) U}
    (ha : Good q U u1 u2 a) (hb : Good q U u1 u2 b) : a = b := by
  apply (hG _ _ U).1
  refine loc_mono (loc_and ((hP q U).2.2.2 hq u1) ((hP q U).2.2.2 hq u2)) ?_
  rintro V g ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  rw [ha V g v w hv hw, hb V g v w hv hw]

theorem good_res (q : ℕ) {V U : Scheme.{0}} (g : V ⟶ U) {u1 u2 : (Γ(U, ⊤))ˣ} {a : Sec ((res _ (tw q 1)).X 0) U}
    (ha : Good q U u1 u2 a) :
    Good q V (Units.map g.appTop.hom.toMonoidHom u1) (Units.map g.appTop.hom.toMonoidHom u2) (Sec.res g a) := by
  intro W k v w hv hw
  rw [res_comp]
  exact ha W (k ≫ g) v w (by rw [hv, umap_comp]) (by rw [hw, umap_comp])

end LateralTheory.EtaleFoundations.V2

open LateralTheory.EtaleFoundations.V2 in
theorem LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_two_value_of_roots_kummer_gluing (hP : PrimLoc) (hK : KumTEx) (hG : SecGlue) : LateralTheory.EtaleFoundations.ExistsNaturalEtaleKummerChernClassDegreeTwoValue := by
  intro q _ E L hi
  have hq : ∀ (U : Scheme.{0}) (x : Sx E 2 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hi U ⟨x.sub 0 0 (by omega)⟩
  refine ⟨fun U x => pick (Good q U (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega)))), ?_, ?_⟩
  · intro V U g x
    have e1 : lineUnit L ((x.res g).sub 0 1 (by omega)) = Units.map g.appTop.hom.toMonoidHom (lineUnit L (x.sub 0 1 (by omega))) := by
      rw [sub_res, lineUnit_res]
    have e2 : lineUnit L ((x.res g).sub 1 1 (by omega)) = Units.map g.appTop.hom.toMonoidHom (lineUnit L (x.sub 1 1 (by omega))) := by
      rw [sub_res, lineUnit_res]
    have h1 := good_res q g (pick_spec (good_exists hP hK hG q (hq U x) (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega)))))
    rw [← e1, ← e2] at h1
    exact good_unique hP hG q (hq V (x.res g)) h1 (pick_spec (good_exists hP hK hG q (hq V (x.res g)) _ _))
  · intro U x v w hv hw
    have := pick_spec (good_exists hP hK hG q (hq U x) (lineUnit L (x.sub 0 1 (by omega))) (lineUnit L (x.sub 1 1 (by omega))))
      U (𝟙 U) v w (by rw [umap_id]; exact hv) (by rw [umap_id]; exact hw)
    rwa [res_id] at this
end

-- bundled from Development.EtaleCohomology.TateTwists.KumNatPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def ev_basic : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def prim_loc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u)

def sec_glue : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

theorem res_neg_isZero (R : Type) [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (by intro i h; change ((i : ℕ) : ℤ) = s at h; omega)

theorem units_map_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map (g ≫ x).appTop.hom.toMonoidHom u =
      Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) := by
  ext; simp; rfl

theorem isUnit_q_map {U X : Scheme.{0}} (x : U ⟶ X) (q : ℕ) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_unique (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) (q : ℕ) [NeZero q] (X : Scheme.{0})
    (u : (Γ(X, ⊤))ˣ) (hq : IsUnit (q : Γ(X, ⊤)))
    (γ γ' : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1)
    (h1 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0)
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h1' : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ'.1 1 0 (by simp) U x = 0)
    (h2' : ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
        ev γ'.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) : γ = γ' := by
  apply Cocycle.ext
  apply (hev (ZMod q)).2.2.1
  intro p s h U x
  match p, s, h with
  | 0, s, h =>
    obtain rfl : s = 1 := by omega
    revert x
    show ∀ x : U ⟶ X, _
    intro x
    apply (hsg (ZMod q) _ U).1
    obtain ⟨S, hS, hroot⟩ := (hpl q U).2.2.2 (isUnit_q_map x q hq) (Units.map x.appTop.hom.toMonoidHom u)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨v, hv⟩ := hroot V g hg
    have hv' : v ^ q = Units.map (g ≫ x).appTop.hom.toMonoidHom u := by rw [units_map_comp]; exact hv
    exact ((hev (ZMod q)).2.1 γ.1 0 1 h V U g x).trans ((h2 V (g ≫ x) v hv').trans
      ((h2' V (g ≫ x) v hv').symm.trans ((hev (ZMod q)).2.1 γ'.1 0 1 h V U g x).symm))
  | 1, s, h =>
    obtain rfl : s = 0 := by omega
    exact (h1 U x).trans (h1' U x).symm
  | p + 2, s, h =>
    have hz := res_neg_isZero (ZMod q) (tw q 1) s (by omega)
    have hv : γ.1.v (-((p + 2 : ℕ) : ℤ)) s h = γ'.1.v (-((p + 2 : ℕ) : ℤ)) s h := hz.eq_of_tgt _ _
    unfold ev
    rw [hv]

theorem kum_nat_of (he : kum_exists) (hev : ev_basic) (hpl : prim_loc) (hsg : sec_glue) : kum_nat := by
  intro q _ Y X f u hq
  obtain ⟨γ, hc, h1, h2⟩ := kum_spec_of_exists he q X u hq
  have hqY := isUnit_q_map f q hq
  obtain ⟨γ', hc', h1', h2'⟩ := kum_spec_of_exists he q Y (Units.map f.appTop.hom.toMonoidHom u) hqY
  rw [← hc, ← hc']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (sch.map f))) γ (zero_add 1)) = _
  congr 1
  refine kum_unique hev hpl hsg q Y _ hqY _ γ' ?_ ?_ h1' h2'
  · intro U x
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 1 0 (by simp) U x).trans (h1 U (x ≫ f))
  · intro U x v hv
    exact ((hev (ZMod q)).2.2.2.1 (sch.map f) γ.1 0 1 (by simp) U x).trans
      (h2 U (x ≫ f) v (by rw [hv, units_map_comp]))

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.PpEvBasicPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvBasicPf
variable {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
open LateralTheory.KummerTheory.AW

theorem ev_sub (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [ev_eq, Cochain.sub_v, Preadditive.comp_sub]
  exact map_sub (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl)) _ _

theorem ev_zero (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  rw [ev_eq, Cochain.zero_v, comp_zero]
  exact map_zero (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl))

theorem ev_zsmul (c : ℤ) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (c • α) p s h U x = c • ev α p s h U x := by
  exact map_zsmul (AddMonoidHom.mk' (fun β : Cochain ((chains R).obj E) I n => ev β p s h U x)
    (fun a b => ev_add a b p s h U x)) c α

theorem ev_post {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  rw [ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ev_eq]; rfl

theorem chainsXIso_nat {E' : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  rw [Iso.inv_comp_eq]
  unfold chains chainsXIso
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(p : ℤ)) = _
  exact HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl

theorem ev_pre {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  rw [ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, reassoc_of% (chainsXIso_nat (R := R) f p), ev_eq]
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map (f.app (op (SimplexCategory.mk p))))
    (freeGen R _ U x)) = _
  rw [map_freeGen]; rfl

end LateralTheory.EtaleFoundations.EvBasicPf

open LateralTheory.EtaleFoundations.EvBasicPf LateralTheory.KummerTheory.AW in
theorem LateralTheory.EtaleFoundations.pp_ev_basic_of : LateralTheory.EtaleFoundations.pp_ev_basic := fun _ _ =>
  ⟨fun α β p s h U x => ⟨ev_add α β p s h U x, ev_sub α β p s h U x, ev_zero p s h U x, fun c => ev_zsmul c α p s h U x⟩,
   fun α p s h _ _ g x => ev_res α p s h g x,
   fun α β hh => ev_ext α β hh,
   fun f α p s h U x => ev_pre f α p s h U x,
   fun m α p s h U x => ev_post m α p s h U x⟩
end
end

