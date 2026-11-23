module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0012
public import Development.EtaleCohomology.EtaleSheaves.Bundle0038
public import Development.EtaleCohomology.WeilConjectures.Bundle0002
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.LeafRepCut
public import Development.EtaleCohomology.EtaleSheaves.Bundle0036

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCoprodPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCoprodPf

section General
variable {C : Type*} [Category C] [Preadditive C]

theorem sum_comp_split {K L : CochainComplex C ℤ} {n : ℤ} {ι : Type} {Kj : ι → CochainComplex C ℤ}
    (i : ∀ j, Kj j ⟶ K) (p : ∀ j, K ⟶ Kj j) (α : Cochain K L n) (s : Finset ι) :
    ∑ j ∈ s, (Cochain.ofHom (p j)).comp ((Cochain.ofHom (i j)).comp α (zero_add n)) (zero_add n) =
      (Cochain.ofHom (∑ j ∈ s, p j ≫ i j)).comp α (zero_add n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Cochain.ofHom_add, Cochain.add_comp,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

theorem cls_inj {K L : CochainComplex C ℤ} {ι : Type} [Fintype ι] {Kj : ι → CochainComplex C ℤ}
    (i : ∀ j, Kj j ⟶ K) (p : ∀ j, K ⟶ Kj j) (hsum : ∑ j, p j ≫ i j = 𝟙 K) (n : ℤ)
    (x : CohomologyClass K L n) (hx : ∀ j, cpre (Cocycle.ofHom (i j)) L n n (zero_add n) x = 0) : x = 0 := by
  classical
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have h : ∀ j, ∃ β : Cochain (Kj j) L (n - 1),
      δ (n - 1) n β = (Cochain.ofHom (i j)).comp α.1 (zero_add n) := by
    intro j
    have := hx j
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff] at this
    obtain ⟨m, hm, β, hβ⟩ := this
    obtain rfl : m = n - 1 := by omega
    exact ⟨β, by rw [hβ]; rfl⟩
  choose β hβ using h
  have hδ : ∀ s : Finset ι, δ (n - 1) n (∑ j ∈ s, (Cochain.ofHom (p j)).comp (β j) (zero_add _)) =
      ∑ j ∈ s, (Cochain.ofHom (p j)).comp ((Cochain.ofHom (i j)).comp α.1 (zero_add n)) (zero_add n) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, δ_add, ih, δ_ofHom_comp, hβ]
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨n - 1, by omega, ∑ j, (Cochain.ofHom (p j)).comp (β j) (zero_add _), ?_⟩
  rw [hδ, sum_comp_split, hsum, Cochain.id_comp]

end General

section Sheaves
variable (R : Type) [CommRing R]

abbrev W : Spc ⥤ SimplicialObject (Shv R) := (SimplicialObject.whiskering _ _).obj (free R)

abbrev G : SimplicialObject (Shv R) ⥤ Cx R :=
  AlgebraicTopology.alternatingFaceMapComplex (Shv R) ⋙ ComplexShape.embeddingDownNat.extendFunctor (Shv R)

variable {m : ℕ} (Z : Fin m → Scheme.{0})

def gen (j : Fin m) : Sec ((free R).obj (yoneda.obj (Z j))) (∐ Z) :=
  ((LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (Z j))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).2
    (Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))))).choose

theorem gen_res (j t : Fin m) : Sec.res (Sigma.ι Z t) (gen R Z j) =
    Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))) t :=
  congrFun ((LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (Z j))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).2
    (Pi.single (M := fun t => Sec ((free R).obj (yoneda.obj (Z j))) (Z t)) j (freeGen R _ (Z j) (𝟙 (Z j))))).choose_spec t

def pr (j : Fin m) : (free R).obj (yoneda.obj (∐ Z)) ⟶ (free R).obj (yoneda.obj (Z j)) :=
  LateralTheory.E.L_sch_clsPfYon.yon R _ _ (gen R Z j)

theorem sec_comp {F F' F'' : Shv R} (φ : F ⟶ F') (ψ : F' ⟶ F'') {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sum_pr : ∑ j, pr R Z j ≫ (free R).map (yoneda.map (Sigma.ι Z j)) = 𝟙 _ := by
  classical
  apply LateralTheory.E.L_sch_clsPfYon.yon_ext
  apply (LateralTheory.EWeil.Gys.LV.GluePf.shvSigma R ((free R).obj (yoneda.obj (∐ Z))) (Cofan.mk (∐ Z) (Sigma.ι Z))
    (coproductIsCoproduct Z)).1
  funext t
  change Sec.res (Sigma.ι Z t) _ = Sec.res (Sigma.ι Z t) _
  rw [LateralTheory.E.LeafKumSpecPf.sec_res_map, LateralTheory.E.LeafKumSpecPf.sec_res_map]
  erw [LateralTheory.E.LeafKumSpecPf.freeGen_res]
  have hy : (ConcreteCategory.hom ((yoneda.obj (∐ Z)).map (Sigma.ι Z t).op)) (𝟙 (∐ Z)) = Sigma.ι Z t := by
    rfl
  rw [hy, LateralTheory.EtaleFoundations.EvDeltaPf.sec_sum, Finset.sum_eq_single t]
  · rw [sec_comp, pr, LateralTheory.E.L_sch_clsPfYon.yon_res, gen_res, Pi.single_eq_same,
      LateralTheory.EtaleFoundations.EvDeltaPf.freeGen_map]
    rfl
  · intro b _ hb
    rw [sec_comp, pr, LateralTheory.E.L_sch_clsPfYon.yon_res, gen_res, Pi.single_eq_of_ne (Ne.symm hb)]
    exact map_zero _
  · simp

def prS (j : Fin m) : (W R).obj (sch.obj (∐ Z)) ⟶ (W R).obj (sch.obj (Z j)) where
  app _ := pr R Z j
  naturality a b θ := by
    change (free R).map (𝟙 _) ≫ pr R Z j = pr R Z j ≫ (free R).map (𝟙 _)
    simp

theorem sum_prS : ∑ j, prS R Z j ≫ (W R).map (sch.map (Sigma.ι Z j)) = 𝟙 _ := by
  refine NatTrans.ext (funext fun a => ?_)
  rw [NatTrans.app_sum]
  exact sum_pr R Z

end Sheaves

theorem LeafCoprod_of : LateralTheory.E.E4.LeafCoprod := by
  intro _ q n i m Z hZ
  have : ∀ j, Finite (Ht q (sch.obj (Z j)) n i) := hZ
  refine Finite.of_injective (AddMonoidHom.pi fun j => pull (ZMod q) (sch.map (Sigma.ι Z j)) (tw q i) n) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hsum : ∑ j, (G (ZMod q)).map (prS (ZMod q) Z j) ≫ (chains (ZMod q)).map (sch.map (Sigma.ι Z j)) = 𝟙 _ := by
    have h1 : (G (ZMod q)).map (∑ j, prS (ZMod q) Z j ≫ (W (ZMod q)).map (sch.map (Sigma.ι Z j))) = 𝟙 _ := by
      rw [sum_prS, CategoryTheory.Functor.map_id]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Functor.map_sum] at h1
    simp only [Functor.map_comp] at h1
    exact h1
  exact cls_inj (fun j => (chains (ZMod q)).map (sch.map (Sigma.ι Z j))) (fun j => (G (ZMod q)).map (prS (ZMod q) Z j))
    hsum n x (fun j => congrFun hx j)

end LateralTheory.E.LeafCoprodPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDegCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafDegCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves

def Cov {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop) : Prop :=
  ∃ S ∈ (EtTop B) U, ∀ (U' : B.Etale) (a : U' ⟶ U), S a → P U' a

theorem Cov.mono {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P)
    (hPQ : ∀ U' a, P U' a → Q U' a) : Cov U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun U' a ha => hPQ U' a (hP U' a ha)⟩

theorem Cov.and {B : Scheme.{0}} {U : B.Etale} {P Q : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : Cov U P) (h' : Cov U Q) :
    Cov U (fun U' a => P U' a ∧ Q U' a) := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hQ⟩ := h'
  exact ⟨S ⊓ S', (EtTop B).intersection_covering hS hS', fun U' a ha => ⟨hP U' a ha.1, hQ U' a ha.2⟩⟩

theorem Cov.all {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop} (h : ∀ U' a, P U' a) : Cov U P :=
  ⟨⊤, (EtTop B).top_mem U, fun U' a _ => h U' a⟩

def SHV (q : ℕ) (i : ℤ) {B Y0 Y1 Y2 : Scheme.{0}} (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) : Prop :=
  ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)

abbrev rY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prU p ι U) (prU p ι U') (resYW p ι a) (resY p a) (pullback.lift_fst _ _ _).symm m

abbrev rB (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (m : ℤ) :=
  rpl q i (prB ι U) (prB ι U') (resBW ι a) a.left (pullback.lift_fst _ _ _).symm m

abbrev gY (q : ℕ) (i : ℤ) {B W Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prU p ι U) (prU (g ≫ p) ι U) (mW p g ι U) (mY p g U) (pullback.lift_fst _ _ _).symm m

abbrev bY (q : ℕ) (i : ℤ) {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) (m : ℤ) :=
  rpl q i (prB ι U) (prU p ι U) (toBW p ι U) (toBY p U) (pullback.lift_fst _ _ _).symm m

def LeafNeg : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (m : ℤ), m < 0 →
  Subsingleton (Hrel R f F m)

def LeafShMapZero : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (K K' : DerivedCategory (SShv B q)) (f : K ⟶ K') (m : ℤ),
  (∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0)) →
  (DerivedCategory.homologyFunctor (SShv B q) m).map f = 0

def LeafShIso : Prop := ∀ (B : Scheme.{0}) (q : ℕ) (L K : DerivedCategory (SShv B q)) (ℓ : L ⟶ K) (m : ℤ),
  (∀ (U : B.Etale) (x x' : (OU B q).obj U ⟶ (shiftFunctor _ m).obj L),
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map ℓ = (OU B q).map a ≫ x' ≫ (shiftFunctor _ m).map ℓ) →
    Cov U (fun U' a => (OU B q).map a ≫ x = (OU B q).map a ≫ x')) →
  (∀ (U : B.Etale) (y : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
    Cov U (fun U' a => ∃ x : (OU B q).obj U' ⟶ (shiftFunctor _ m).obj L, (OU B q).map a ≫ y = x ≫ (shiftFunctor _ m).map ℓ)) →
  IsIso ((DerivedCategory.homologyFunctor (SShv B q) m).map ℓ)

def LeafVan0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 2 < m → ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) m,
  Cov U (fun U' a => rY q i p ι a m y = 0)

def LeafKill2 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) 2,
  Cov U (fun U' a => rY q i (g1 ≫ p) ι a 2 (gY q i p g1 ι U 2 y) = 0)

def LeafKill1 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g1 ≫ p) ι U)) (tw q i) 1,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1 (gY q i (g1 ≫ p) g2 ι U 1 y) = 0)

def LeafVanB : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ (m : ℤ), 0 < m → ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) m,
  Cov U (fun U' a => rB q i ι a m c = 0)

def LeafInj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  Cov U (fun U' a => rB q i ι a 0 c = 0)

def LeafSurj0 : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  Cov U (fun U' a => ∃ c : Hrel (ZMod q) (sch.map (prB ι U')) (tw q i) 0,
    bY q i (g2 ≫ g1 ≫ p) ι U' 0 c = rY q i (g2 ≫ g1 ≫ p) ι a 0 y)

theorem loc_zero_map {B : Scheme.{0}} {q : ℕ} {K K' : DerivedCategory (SShv B q)} (f : K ⟶ K') {m : ℤ}
    (X X' : B.Etale → Type 1) [∀ U, Zero (X' U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K))
    (e' : ∀ U, X' U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K'))
    (hb : ∀ U, Function.Surjective (e U))
    (res' : ∀ U U', (U' ⟶ U) → X' U → X' U') (φ : ∀ U, X U → X' U)
    (hnat : ∀ U U' (a : U' ⟶ U) y, e' U' (res' U U' a y) = (OU B q).map a ≫ e' U y)
    (hf : ∀ U y, e' U (φ U y) = e U y ≫ (shiftFunctor _ m).map f)
    (hv : ∀ U y, Cov U (fun U' a => res' U U' a (φ U y) = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map f = 0) := by
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  refine (Cov.and (hv U y) (hv U y0)).mono fun U' a ⟨h1, h2⟩ => ?_
  rw [← hf, ← hnat, h1, ← h2, hnat, hf, hy0, zero_comp, comp_zero]

theorem loc_zero {B : Scheme.{0}} {q : ℕ} {K : DerivedCategory (SShv B q)} {m : ℤ}
    (X : B.Etale → Type 1) [∀ U, Zero (X U)]
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U))
    (res : ∀ U U', (U' ⟶ U) → X U → X U')
    (hnat : ∀ U U' (a : U' ⟶ U) y, e U' (res U U' a y) = (OU B q).map a ≫ e U y)
    (hv : ∀ U y, Cov U (fun U' a => res U U' a y = 0)) (U : B.Etale)
    (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K) :
    Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0) :=
  loc_zero_map (𝟙 K) X X e e hb res (fun _ y => y) hnat (fun U y => by simp) hv U x

theorem isZero_of (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (h : ∀ (U : B.Etale) (x : (OU B q).obj U ⟶ (shiftFunctor _ m).obj K),
      Cov U (fun U' a => (OU B q).map a ≫ x ≫ (shiftFunctor _ m).map (𝟙 K) = 0)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id]
  exact hZ B q K K (𝟙 K) m h

theorem isZero_neg (hZ : LeafShMapZero) {B : Scheme.{0}} {q : ℕ} (K : DerivedCategory (SShv B q)) (m : ℤ)
    (X : B.Etale → Type 1) (hs : ∀ U, Subsingleton (X U))
    (e : ∀ U, X U → ((OU B q).obj U ⟶ (shiftFunctor _ m).obj K)) (hb : ∀ U, Function.Surjective (e U)) :
    IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K) := by
  refine isZero_of hZ K m fun U x => Cov.all fun U' a => ?_
  obtain ⟨y, rfl⟩ := hb U x
  obtain ⟨y0, hy0⟩ := hb U 0
  rw [Subsingleton.elim y y0, hy0]
  simp

theorem goal_of (hN : LeafNeg) (hZ : LeafShMapZero) (hI : LeafShIso) (hV0 : LeafVan0) (hK2 : LeafKill2)
    (hK1 : LeafKill1) (hVB : LeafVanB) (hIn : LeafInj0) (hSu : LeafSurj0) : LateralTheory.E.EtaleTopologySheaves.LeafDeg := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  have hS : SHV q i V p g1 g2 := hA
  refine ⟨fun m hm => ?_, ?_, ?_, fun m hm => ?_, fun m hm => ?_, ?_⟩
  · exact isZero_of hZ K0 m (loc_zero _ (l0 · m) (fun U => (r0.1 U m).2) (fun U U' a => rY q i p ι a m)
      (fun U U' a y => r0.2 U U' a m y) (fun U y => hV0 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm y))
  · exact hZ B q K0 K1 f 2 (loc_zero_map f _ _ (l0 · 2) (l1 · 2) (fun U => (r0.1 U 2).2)
      (fun U U' a => rY q i (g1 ≫ p) ι a 2) (fun U => gY q i p g1 ι U 2)
      (fun U U' a y => r1.2 U U' a 2 y) (fun U y => mf U 2 y)
      (fun U y => hK2 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact hZ B q K1 K2 g 1 (loc_zero_map g _ _ (l1 · 1) (l2 · 1) (fun U => (r1.1 U 1).2)
      (fun U U' a => rY q i (g2 ≫ g1 ≫ p) ι a 1) (fun U => gY q i (g1 ≫ p) g2 ι U 1)
      (fun U U' a y => r2.2 U U' a 1 y) (fun U y => mg U 1 y)
      (fun U y => hK1 hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U y))
  · exact isZero_neg hZ K2 m _ (fun U => hN _ _ _ m hm) (l2 · m) (fun U => (r2.1 U m).2)
  · rcases lt_or_gt_of_ne hm with hm | hm
    · exact isZero_neg hZ L m _ (fun U => hN _ _ _ m hm) (lL · m) (fun U => (rL.1 U m).2)
    · exact isZero_of hZ L m (loc_zero _ (lL · m) (fun U => (rL.1 U m).2) (fun U U' a => rB q i ι a m)
        (fun U U' a c => rL.2 U U' a m c) (fun U c => hVB hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U m hm c))
  · refine hI B q L K2 ℓ 0 (fun U x x' hx => ?_) (fun U y => ?_)
    · obtain ⟨c, rfl⟩ := (rL.1 U 0).2 x
      obtain ⟨c', rfl⟩ := (rL.1 U 0).2 x'
      have hd := hIn hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U (c - c') (hx.mono fun U' a h => by
        rw [← mℓ U 0 c, ← mℓ U 0 c', ← r2.2 U U' a 0, ← r2.2 U U' a 0] at h
        rw [map_sub, map_sub, (r2.1 U' 0).1 h, sub_self])
      refine hd.mono fun U' a h => ?_
      rw [← rL.2 U U' a 0 c, ← rL.2 U U' a 0 c', sub_eq_zero.1 ((map_sub _ c c').symm.trans h)]
    · obtain ⟨z, rfl⟩ := (r2.1 U 0).2 y
      refine (hSu hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hS U z).mono fun U' a ⟨c, hc⟩ => ⟨lL U' 0 c, ?_⟩
      rw [← r2.2 U U' a 0 z, ← hc, mℓ U' 0 c]

end LateralTheory.E.LeafDegCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafExtendCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafExtendCut

def LeafStalkValuation : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp Ω) (x y : C)
  (hx : IsGenericPoint x (⊤ : Set C)), IsCurve c → y ≠ x →
    ValuationRing (C.presheaf.stalk y) ∧
      (letI := (C.presheaf.stalkSpecializes (hx.specializes (Set.mem_univ y))).hom.toAlgebra
       IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x))

def LeafLocalExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsProper p] (x y : C),
  IsGenericPoint x (⊤ : Set C) → ∀ (h : x ⤳ y), ValuationRing (C.presheaf.stalk y) →
    (letI := (C.presheaf.stalkSpecializes h).hom.toAlgebra
     IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x)) →
    ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X, ψ ≫ p = C.fromSpecStalk x ≫ sC →
      ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC

def LeafGlueExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsSeparated p] (x : C),
  IsGenericPoint x (⊤ : Set C) → ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X,
    (∀ y : C, ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC) →
      ∃ e : C ⟶ X, C.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = sC

theorem goal_of (h1 : LeafStalkValuation) (h2 : LeafLocalExtend) (h3 : LeafGlueExtend) :
    LateralTheory.E.LeafCurveVCut.LeafExtend := by
  intro k Ω _ _ _ X C0 p _ c0 x hc hx ψ hψ
  have : IsIntegral C0 := hc.1
  refine h3 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x hx ψ ?_
  intro y
  by_cases hyx : y = x
  · subst hyx
    obtain ⟨U, hxU, f, hf1, hf2⟩ := spread_out_of_isGermInjective'
      (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p ψ hψ
    exact ⟨U, hxU, hxU, f, hf1.symm, hf2⟩
  · obtain ⟨hv, hfr⟩ := h1 Ω c0 x y hx hc hyx
    exact h2 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x y hx _ hv hfr ψ hψ

end LateralTheory.E.LeafExtendCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafMapWPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf LateralTheory.E.HalfDegreeVanishing

namespace LateralTheory.E.LeafMapWPf

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

theorem pvm_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)).map f).1.2 : Scheme.Γ.obj (op Y)) =
      Scheme.Γ.map k.op (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) := by
  let N := op (SimplexCategory.mk n)
  let projection : (PB (bsumOf V W)).obj N ⟶ (PGL (a + b)).obj N :=
    (pullback.snd (bsumOf V W) (PGL.pr (a + b))).app N
  have h := types_congr_hom (projection.naturality k.op) x
  have h2 := congrArg (fun p => (p.1.2 : Scheme.Γ.obj (op Y))) (Functor.congr_hom h f)
  refine h2.trans ?_
  have h3 := congrArg (fun p => (p.2 : Scheme.Γ.obj (op Y)))
    (um_hom_val (Functor.congr_obj h i) (Functor.congr_obj h j)
      ((((PGL (a + b)).obj N).map k.op (pv V W x)).map f))
  exact h3.trans rfl

theorem pvm_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X)
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (((pv V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x)).map f).1.2 : Scheme.Γ.obj (op X)) =
      (((((PGL (a + b)).map θ.op).app (op X)) (pv V W x) : Fin (m + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X))).map f).1.2 := by
  have h := types_congr_hom
    (NatTrans.congr_app ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x
  have h2 := congrArg (fun p => (p.1.2 : Scheme.Γ.obj (op X))) (Functor.congr_hom h f)
  refine h2.trans ?_
  have h3 := congrArg (fun p => (p.2 : Scheme.Γ.obj (op X))) (um_hom_val (Functor.congr_obj h i) (Functor.congr_obj h j) (((ConcreteCategory.hom
      (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) ≫
        (((PGL (a + b)).map θ.op).app (op X)))) x).map f))
  exact h3.trans rfl

theorem pe_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X) :
    pe V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x) = ((E.map θ.op).app (op X)) (pe V W x) :=
  types_congr_hom
    (NatTrans.congr_app ((pullback.fst (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x

theorem pw_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (e : Sx E n X)
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W (((E.map θ.op).app (op X)) e)).map f) =
      (show GL (Fin b) (Scheme.Γ.obj (op X)) from
        ((((ofCat (glCat b)).map θ.op).app (op X)) (pw W e) : Fin (m + 1) ⥤ SingleObj (GL (Fin b) (Scheme.Γ.obj (op X)))).map f) :=
  eq_of_heq (Functor.hcongr_hom (types_congr_hom (NatTrans.congr_app (W.naturality θ.op) (op X)) e) f)

def gX (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) (x : ((U2 V W).obj n).obj X) : ((PGL b).obj n).obj X :=
  show Fin (n.unop.len + 1) ⥤ Um b (Scheme.Γ.obj (op X.unop)) from gfun V W x.1 x.2

theorem gX_nat_X (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (k : X ⟶ Y) (x : ((U2 V W).obj n).obj X) :
    gX V W n Y (((U2 V W).obj n).map k x) = ((PGL b).obj n).map k (gX V W n X x) := by
  apply um_functor_ext
  · intro i
    show wb (a := a) ((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n.unop.len))).map k.unop.op x.1)).obj i).1 = _
    rw [pv_res]; rfl
  · intro i j f
    apply Prod.ext
    · show (show GL (Fin b) _ from (pw W (pe V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n.unop.len))).map k.unop.op x.1))).map f) = _
      rw [pe_res, pw_res]; rfl
    · apply Units.ext
      exact pvm_res V W k.unop x.1 f

theorem gX_nat_n {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : Scheme.{0}ᵒᵖ) (x : ((U2 V W).obj n).obj X) :
    gX V W m X ((((U2 V W).map θ).app X) x) = (((PGL b).map θ).app X) (gX V W n X x) := by
  apply um_functor_ext
  · intro i
    show wb (a := a) ((pv V W ((((PB (bsumOf V W)).map θ.unop.op).app (op X.unop)) x.1)).obj i).1 = _
    rw [pv_simp]; rfl
  · intro i j f
    apply Prod.ext
    · show (show GL (Fin b) _ from (pw W (pe V W ((((PB (bsumOf V W)).map θ.unop.op).app (op X.unop)) x.1))).map f) = _
      rw [pe_simp, pw_simp]; rfl
    · apply Units.ext
      exact (pvm_simp V W θ.unop x.1 f).trans rfl

def gmap : U2 V W ⟶ PGL b where
  app n :=
    { app := fun X => TypeCat.ofHom (gX V W n X)
      naturality := fun X Y k => by
        ext x
        exact gX_nat_X V W n k x }
  naturality n m θ := by
    ext X x
    exact gX_nat_n V W θ X x

theorem gmap_pr : gmap V W ≫ PGL.pr b = f2 V W ≫ PB.pr _ ≫ W := by
  ext n X x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  erw [Category.id_comp, Category.comp_id]
  rfl

theorem gmap_line : gmap V W ≫ PGL.line b = f2 V W ≫ pullback.snd (bsumOf V W) (PGL.pr (a + b)) ≫ PGL.line (a + b) := by
  ext n X x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  erw [Category.id_comp, Category.comp_id]
  rfl

theorem LeafMapW_of : LateralTheory.E.HalfDegreeVanishing.LeafMapW := fun V W => ⟨gmap V W, gmap_pr V W, gmap_line V W⟩

end LateralTheory.E.LeafMapWPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafModelCurveCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafModelCurveCut

def ExistsNormalProperCurveModel : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L),
      IsIntegral C0 ∧ IsProper c0 ∧ (∀ y : C0, IsIntegrallyClosed (C0.presheaf.stalk y)) ∧
      topologicalKrullDim C0 = 1 ∧ IsGenericPoint x (⊤ : Set C0) ∧
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafSmoothOfNormal : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

theorem goal_of (hN : ExistsNormalProperCurveModel) (hS : LeafSmoothOfNormal) : LateralTheory.E.LeafCurveVCut.LeafModelCurve := by
  intro Ω L _ _ _ _ u hu hfin
  obtain ⟨C0, c0, x, ψ, hint, hprop, hnorm, hdim, hx, hψ⟩ := hN Ω L u hu hfin
  refine ⟨C0, c0, x, ψ, ⟨hint, hprop, ?_⟩, hx, hψ⟩
  have := hprop
  exact hS Ω c0 hint inferInstance hnorm hdim

end LateralTheory.E.LeafModelCurveCut

end
end

