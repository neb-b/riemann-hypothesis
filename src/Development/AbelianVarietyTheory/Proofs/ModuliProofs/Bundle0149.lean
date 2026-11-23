module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelObjectPullbackExistsAndFull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.fullObj_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (RZ H n N)) (t : SAB H S) (lev : D.La → (𝟙_ (Over S) ⟶ t.G)) (f : S' ⟶ S), (∃ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), ∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) ∧ ∀ (t' : SAB H S') (ν : SABMap t' t f) (lv : D.La → (𝟙_ (Over S') ⟶ t'.G)), (∀ a, (lv a).left ≫ ν.φ = f ≫ (lev a).left) → FullObj D s t lev → FullObj D (f ≫ s) t' lv := by
  intro E _ _ _ H D n N S S' s t lev f
  refine ⟨?_, fun t' m lv hlv o => ?_⟩
  · obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
      have hC := Out.CubePf.cubePull
      have hsemi : IsSemiAbelian ((Over.pullback f).obj t.G) := by
        refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
        · have := t.semi.comm
          infer_instance
        · have := t.semi.smooth
          change Smooth (pullback.snd t.G.hom f)
          infer_instance
        · have := t.semi.separated
          change IsSeparated (pullback.snd t.G.hom f)
          infer_instance
        · have := t.semi.quasiCompact
          change QuasiCompact (pullback.snd t.G.hom f)
          infer_instance
        · have := t.semi.geomConnected
          change GeometricallyConnected (pullback.snd t.G.hom f)
          infer_instance
        · intro Ω _ _ q
          obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ f)
          exact ⟨torusExtOfIso (pullCompIso q f t.G) A⟩
      have hp : ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
          (m : SABMap ⟨(Over.pullback f).obj t.G, hsemi, OAct.pullback f t.G t.act, PP', cub,
            sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
        have h := isGrpPullback_pullback t.G f
        obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
        have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
            pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
        have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
            pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
          Over.OverMorphism.ext (by
            show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
            rw [Category.assoc, hact, Category.assoc])
        refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
        · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
            (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
          refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
            (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
          · fin_cases i
            · exact (pa _ a).trans (by simp [U])
            · simp [U]
          · fin_cases i
            · simp [U]
            · exact (pa _ _).trans (by simp [U])
        · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
          refine LBIso.chartPull (chartPullPull t.PP.L _)
            (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
          fin_cases i
          · simp [U]
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
      obtain ⟨_, _, _, _, _, m, -⟩ := hp
      exact ⟨_, ⟨m⟩⟩
    exact ⟨t', m, fun a => GlobalTheory.ObjPull.secPull m.cart (lev a), fun a => GlobalTheory.ObjPull.secPull_left m.cart _⟩
  have hlv' : ∀ a, lv a = GlobalTheory.ObjPull.secPull m.cart (lev a) := fun a => by
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · exact (hlv a).trans (GlobalTheory.ObjPull.secPull_left m.cart _).symm
    · rw [Over.w, Over.w]
  have hL : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  obtain ⟨-, hamp, hk⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi) m.cart hL
  refine
    { proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
      ample := hamp o.ample
      ktriv := hk o.ktriv
      add := fun a c => by rw [hlv', hlv', hlv', o.add, map_mul]
      ker := fun a => by rw [hlv', o.ker a, map_one]
      geom := fun k _ _ _ x β hx => ?_ }
  obtain ⟨hdet, I, hI, hA⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
  refine ⟨fun τ => ?_, GlobalTheory.ObjPull.tateMove (GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x)) (fun c g => ?_)
    (fun n g g' c hc => ?_) I, hI, fun a => ?_⟩
  · rw [GlobalTheory.LiePull.lieMult_pull _ S S' t.G t'.G f m.cm.F t.act t'.act m.cart m.act k x τ,
      GlobalTheory.LiePull.lieMult_pull _ S S' t.G t'.G f m.cm.F t.act t'.act m.cart m.act k x τ]
    exact hdet τ
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' t.G t'.G f m.cm.F t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart hL
      (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
  · rw [hlv']
    exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull m.cart _ _).trans (hA a))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpFamOfDenseFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild.Fibre

theorem mem_range_spMap {R K : Type} [CommRing R] [Field K] (x : R →+* K) (p : Sp R)
    (h : RingHom.ker x = PrimeSpectrum.asIdeal (R := R) p) : p ∈ Set.range (spMap x) := by
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  rw [← h]
  rfl

theorem basis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

variable {S S' : Scheme.{0}}

theorem basis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact basis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

variable {A : Over S'} {Z : Over S} {x : S' ⟶ S} {φ : A.left ⟶ Z.left}

theorem comp_eq_pushPt (w : φ ≫ Z.hom = A.hom ≫ x) {a : Out.baseOver S' ⟶ A} {s : Out.baseOver S ⟶ Z}
    (h : a.left ≫ φ = x ≫ s.left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S) : t ≫ s = pushPt w (u ≫ a) := by
  apply Over.OverMorphism.ext
  have h1 : t.left = T.hom ≫ x := by simpa using Over.w t
  have h2 : u.left = T.hom := by simpa using Over.w u
  change t.left ≫ s.left = (u.left ≫ a.left) ≫ φ
  rw [h1, h2, Category.assoc, Category.assoc, h]

theorem basis_push [GrpObj A] [GrpObj Z] (hφ : IsGrpPullback A Z x φ) {r k : ℕ}
    {a : Fin r → (Out.baseOver S' ⟶ A)} {s : Fin r → (Out.baseOver S ⟶ Z)}
    (h : ∀ i, (a i).left ≫ φ = x ≫ (s i).left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S)
    (hb : ∀ z : T ⟶ A, z ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ a i) (fun i => (c i).val) = z)
    (z : Over.mk (T.hom ≫ x) ⟶ Z) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => t ≫ s i) (fun i => (c i).val) = z := by
  have inj : Function.Injective (pushHom hφ T) := fun y y' e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w y).trans (Over.w y').symm))
  obtain ⟨z, rfl⟩ := GrpDense.pushPt_surjective hφ.1 T z
  change pushHom hφ T z ^ k = 1 at hz
  rw [← map_pow, map_eq_one_iff _ inj] at hz
  have key : ∀ e : Fin r → ℕ, Out.linComb (fun i => t ≫ s i) e =
      pushHom hφ T (Out.linComb (fun i => u ≫ a i) e) := fun e => by
    simp only [Out.linComb, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    rw [comp_eq_pushPt hφ.1.w (h i) u t]
    exact (map_pow (pushHom hφ T) _ _).symm
  simp only [key]
  change ∃! c : Fin r → ZMod k, _ = pushHom hφ T z
  simp only [inj.eq_iff]
  exact hb z hz

theorem lab_single {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (i : Fin (2 * g)) : t.lab (Pi.single i 1) = t.pt i := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ (t.torsion i), pow_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
  · simp

theorem lab_zero {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) : t.lab 0 = 1 := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn]
  simp

theorem one_left {A : Over S} [GrpObj A] : (1 : Out.baseOver S ⟶ A).left = (η[A]).left :=
  Category.id_comp _

end GlobalTheory.ZM.NearBuild.Fibre

namespace GlobalTheory.ZM.NearBuild

open Fibre

theorem grpFam_of_dense_fibres :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (mu : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), N' ≠ 0 → DenseP (objPrimes b Mat κ β v) → Fam b Mat κ β v m M th sc → SmoothOfRelativeDimension g Z.hom → GeometricallyConnected Z.hom → AddAt b Mat κ β v m M th sc mu → (∀ i, EndAt b Mat κ β v m M th sc i (F i)) → ∃ _ : GrpObj Z, GrpFam b Mat κ β v m Z M (fun i => F (some i)) (fun i => sc (Pi.single i 1)) := by
  intro hL _ o _ g N' J b Mat κ R _ _ _ β v m Z M th sc mu F hN0 hden ⟨⟨I, p, hrep, _⟩, _, hfib⟩ hsm hgc hm hF
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hun : IsUnit (N' : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero] at this
    exact this
  obtain ⟨-, hpr, hamp⟩ := GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hrep
  have hD := dense_of_denseP hden
  have hs : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have s1 : Smooth (Out.baseOver (Sp R)).hom := inferInstanceAs (Smooth (𝟙 _))
  have h0 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s)
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) →
      (1 : Out.baseOver _ ⟶ t'.A).left ≫ φ = spMap x ≫ (sc 0).left := fun t' φ h => by
    have := h 0
    rwa [lab_zero, one_pow] at this
  have h1 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s)
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) →
      ∀ i, (t'.pt i ^ N').left ≫ φ = spMap x ≫ (sc (Pi.single i 1)).left := fun t' φ h i => by
    have := h (Pi.single i 1)
    rwa [lab_single] at this
  obtain ⟨_, -, hη, -, hab, hgp⟩ := grpObj_of_dense_fibres R Z mu (F none) (sc 0) _ hD hs hpr hgc (by
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨K, inferInstance, spMap x, t'.A, inferInstance, φ, mem_range_spMap x q hx, t'.ab.comm, hφ.1,
      hm K x s t' φ ht hφ, ?_, ?_⟩
    · have := hF none K x s t' φ ht hφ
      rwa [Option.elim, Hom.inv_def, Category.id_comp] at this
    · rw [← one_left, h0 t' hφ.2.2.2])
  have := hab.comm
  have hhom : ∀ i, IsMonHom (F (some i)) := fun i => hL.rigidity _ Z Z hab hab _ (by
    rw [hη]
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [← Category.assoc, comp_eq_pushPt hφ.1.w (h0 t' hφ.2.2.2) (toUnit T) t]
    have := t'.hom i
    have e : (toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A)) ≫ t'.act i = toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A) := by
      rw [Category.assoc, MonObj.one_comp]
    apply Over.OverMorphism.ext
    change (_ ≫ φ) ≫ (F (some i)).left = _ ≫ φ
    rw [Category.assoc, hF (some i) K x s t' φ ht hφ, ← Category.assoc, ← Over.comp_left]
    exact congrArg (fun z => z.left ≫ φ) e)
  have htor : ∀ {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s) (i),
      (t'.pt i ^ N') ^ N' = 1 := fun t' i => by
    have e : N' * N' = N' ^ 2 := (pow_two _).symm
    rw [← pow_mul (t'.pt i), e, t'.torsion]
  have hQ : ∀ i, sc (Pi.single i 1) ^ N' = 1 := fun i => by
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [MonObj.comp_pow, MonObj.comp_one, comp_eq_pushPt hφ.1.w (h1 t' hφ.2.2.2 i) (toUnit T) t]
    change pushHom (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) T _ ^ _ = 1
    rw [← map_pow]
    erw [← MonObj.comp_pow]
    rw [htor]
    erw [MonObj.comp_one]
    rw [map_one]
  have hB := torsion_basis_of_dense (Sp R) Z N' (2 * g) (fun i => sc (Pi.single i 1)) _ hab
    (Nat.pos_of_ne_zero hN0) (by
      have := hun.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this) hQ hD (by
      intro q hq
      obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨φ, hφ⟩ := hfib K x s t' ht
      have := t'.ab.comm
      refine ⟨K, inferInstance, inferInstance, 𝟙 _ ≫ spMap x, by simpa using mem_range_spMap x q hx, ?_⟩
      exact basis_push (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) (h1 t' hφ.2.2.2) (T := Over.mk (𝟙 _)) _ _
        (basis_pow_linComb (pow_two _) (NeZero.ne _) _ t'.pt t'.torsion (t'.bij K (𝟙 _))))
  refine ⟨inferInstance, hab, hsm, hrep.1, hamp, ⟨hhom, hQ, hB⟩, fun K _ _ x s t' ht => ?_⟩
  obtain ⟨φ, hφ⟩ := hfib K x s t' ht
  exact ⟨φ, ⟨hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ), fun i => (hF (some i) K x s t' φ ht hφ).symm,
    h1 t' hφ.2.2.2⟩, hφ.2.2.1⟩

end GlobalTheory.ZM.NearBuild
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFibrewiseThetaOfOpenImmersionCover
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ThetaLocal

open GlobalTheory.AbLocusPull

variable {X X' : Scheme.{0}}

theorem fn_ext_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    {a b : Γ(X, U)} (h : ∀ x, F x ∈ U → gs F x U a = gs F x U b) : a = b := by
  have := F.isIso_app U hU
  apply (ConcreteCategory.bijective_of_isIso (F.app U)).1
  refine fn_ext fun x hx => ?_
  have e₁ := gs_pull (𝟙 X') F x U hx a
  have e₂ := gs_pull (𝟙 X') F x U hx b
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h x hx).trans e₂.symm)

theorem exists_fn_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    (b : Γ(X', F ⁻¹ᵁ U)) : ∃ a : Γ(X, U), ∀ x, F x ∈ U → gs F x U a = gs (𝟙 X') x _ b := by
  have := F.isIso_app U hU
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (F.app U)).2 b
  refine ⟨a, fun x hx => ?_⟩
  have e₁ := gs_pull (𝟙 X') F x U hx a
  rw [Category.id_comp] at e₁
  exact e₁.symm

theorem exists_secOn_push {F : X' ⟶ X} [IsOpenImmersion F] {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {W : X.Opens} {W' : X'.Opens} (hr : W ≤ F.opensRange) (hW : F ⁻¹ᵁ W ≤ W')
    {θ' : ∀ k, Γ(X', W' ⊓ L'.U k)} (hθ' : θ' ∈ secOn L' W') :
    ∃ θ ∈ secOn L W, ∀ x, F x ∈ W → ∀ j k, F x ∈ L.U j → x ∈ X'.basicOpen (θ' k) → F x ∈ X.basicOpen (θ j) := by
  obtain ⟨w, hw⟩ := hw
  have hw := (isGen_iff w).1 hw
  have rel : ∀ (x : X') j j' k k', F x ∈ W → F x ∈ L.U j → F x ∈ L.U j' → x ∈ L'.U k → x ∈ L'.U k' →
      (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) =
        (gm F x (L.U j ⊓ L.U j') (L.g j j')).val * ((gw w (𝟙 X') x j' k').val * gs (𝟙 X') x _ (θ' k')) := by
    intro x j j' k k' hx hj hj' hk hk'
    have e := hw _ (𝟙 X') x j j' k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    rw [gs_secOn hθ' (𝟙 X') x k k' (hW hx) hk hk', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul]
    congr 2
    rw [mul_right_comm, inv_mul_cancel_right]
  have ex : ∀ j, ∃ a : Γ(X, W ⊓ L.U j), ∀ x k, F x ∈ W → F x ∈ L.U j → x ∈ L'.U k →
      gs F x _ a = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
    intro j
    let O : L'.ι → X'.Opens := fun k => F ⁻¹ᵁ W ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
    have le : ∀ k, O k ≤ W' ⊓ L'.U k := fun k x hx => ⟨hW hx.1, hx.2.2⟩
    let u : ∀ k, Γ(X', (L.pull F).U (fun _ => j) ⊓ L'.U k)ˣ := fun k => w.s (fun _ => j, k)
    let a : ∀ k, Γ(X', O k) := fun k => resG X' inf_le_right (u k).val * resG X' (le k) (θ' k)
    have va : ∀ x k, x ∈ O k → gs (𝟙 X') x _ (a k) = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
      intro x k hx
      refine (gs_mul _ x _ hx _ _).trans ?_
      rw [gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx.2]
      rfl
    obtain ⟨b, hb⟩ := glue_fn (F ⁻¹ᵁ (W ⊓ L.U j)) O (fun k x hx => ⟨hx.1, mem_pull.1 hx.2.1⟩)
      (fun x hx => (exists_chart hL' x).imp fun k hk => ⟨hx.1, mem_pull.2 hx.2, hk⟩) a (fun k k' x hk hk' => by
        rw [va x k hk, va x k' hk', rel x j j k k' hk.1 (mem_pull.1 hk.2.1) (mem_pull.1 hk.2.1) hk.2.2 hk'.2.2,
          gm_self hL F x (mem_pull.1 hk.2.1), Units.val_one, _root_.one_mul])
    obtain ⟨c, hc⟩ := exists_fn_of_isOpenImmersion F (inf_le_left.trans hr) b
    refine ⟨c, fun x k hx hj hk => ?_⟩
    have hm : x ∈ O k := ⟨hx, mem_pull.2 hj, hk⟩
    exact (hc x ⟨hx, hj⟩).trans ((hb x k hm).trans (va x k hm))
  choose θ hθ using ex
  refine ⟨θ, fun j j' => fn_ext_of_isOpenImmersion F (inf_le_left.trans (inf_le_left.trans hr)) fun x hx => ?_,
    fun x hx j k hj hk => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' x
    rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit F x (L.U j ⊓ L.U j') ⟨hx.1.2, hx.2⟩, hθ j x k hx.1.1 hx.1.2 hk, hθ j' x k hx.1.1 hx.2 hk]
    exact rel x j j' k k hx.1.1 hx.1.2 hx.2 hk hk
  · have hm : x ∈ W' ⊓ L'.U k := X'.basicOpen_le _ hk
    refine (isUnit_gs_iff F x (W ⊓ L.U j) ⟨hx, hj⟩ _).1 ?_
    rw [hθ j x k hx hj hm.2]
    exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X') x _ hm _).2 hk)

theorem hasTheta_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, HasTheta (u i).G (u i).PP.L) → HasTheta t.G t.PP.L := by
  intro E _ _ _ H Z t I Y f u m hf hc hu z
  obtain ⟨i, y, rfl⟩ := hc z
  have := hf i
  have h := (m i).cart.1
  have : IsOpenImmersion (m i).cm.F := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip ‹_›
  obtain ⟨w, g, -⟩ := (m i).lin
  have sq : ∀ x, t.G.hom ((m i).cm.F x) = f i ((u i).G.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  obtain ⟨V, hy, θ', hθ', hne⟩ := hu i y
  have hr : t.G.hom ⁻¹ᵁ (f i ''ᵁ V) ≤ (m i).cm.F.opensRange := by
    rintro x ⟨y', -, e⟩
    obtain ⟨x', h₁, -⟩ := Scheme.exists_preimage_of_isPullback h x y' e.symm
    exact ⟨x', h₁⟩
  have hW : (m i).cm.F ⁻¹ᵁ (t.G.hom ⁻¹ᵁ (f i ''ᵁ V)) ≤ (u i).G.hom ⁻¹ᵁ V := by
    rintro x ⟨y', hy', e⟩
    have e' : y' = (u i).G.hom x := (f i).isOpenEmbedding.injective (e.trans (sq x))
    show (u i).G.hom x ∈ V
    rw [← e']; exact hy'
  obtain ⟨θ, hθ, hb⟩ := exists_secOn_push t.PP.isLB (u i).PP.isLB ⟨w, g⟩ hr hW hθ'
  refine ⟨f i ''ᵁ V, ⟨y, hy, rfl⟩, θ, hθ, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨x, k, hx, hk⟩ := hne y' hy'
  obtain ⟨j, hj⟩ := exists_chart t.PP.isLB ((m i).cm.F x)
  refine ⟨(m i).cm.F x, j, (sq x).trans (congrArg _ hx), hb x ⟨y', hy', ?_⟩ j k hj hk⟩
  exact ((sq x).trans (congrArg _ hx)).symm

end GlobalTheory.ThetaLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOpenSetOfTTEqBot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory

theorem isOpen_setOf_TT_eq_bot : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (M : GlobalTheory.ZH.RatModel o Ω) (I : Type) (d : I → Ω) (e : ℕ), M.HasDiv S.th → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (S.TT M z = ⊥ ↔ ∃ k, d k ≠ 0 ∧ S.th x₀ ^ e / d k ∈ M.O z)) → IsOpen {z : M.Z | S.TT M z = ⊥} := by
  intro o Ω _ _ _ S M I d e hdiv h
  haveI : NeZero (S.r * S.N) :=
    ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨x₀, hx₀⟩ := hdiv z
  obtain ⟨k, hk, hreg⟩ := (h z x₀ hx₀).1 hz
  refine ⟨{w | M.Div S.th x₀ w} ∩ {w | S.th x₀ ^ e / d k ∈ M.O w}, ?_,
    (M.isOpen_setOf_div S.th x₀).inter (M.isOpen_setOf_mem_O _), hx₀, hreg⟩
  rintro w ⟨hw1, hw2⟩
  exact (h w x₀ hw1).2 ⟨k, hk, hw2⟩

end GlobalTheory
end

