module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ChernPowerZsmulEqPowSmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem cohomology_cast_zsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (c : ℤ)
    (x : Ht q E n i) : Ht.cast hn hi (c • x) = c • Ht.cast hn hi x := by
  subst hn hi
  rfl

theorem UpperTheory.chernPower_zsmul_eq_pow_smul :
    ∀ (q : ℕ) {E : Spc} (y : Ht q E 2 1) (m : ℤ) (j : ℕ), cpow q (m • y) j = (m ^ j) • cpow q y j := by
  intro q E y m j
  induction j with
  | zero =>
    rw [cpow_zero, cpow_zero, pow_zero, one_smul]
  | succ k ih =>
    rw [cpow_succ, cpow_succ, ih, map_zsmul, map_zsmul, AddMonoidHom.zsmul_apply, smul_smul,
      ← pow_succ', cohomology_cast_zsmul]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ExistsUniqueSimplexPullbackOfMapEq
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

theorem UpperTheory.existsUnique_simplex_pullback_of_map_eq :
    ∀ {X Y Z : Spc} (f : X ⟶ Z) (g : Y ⟶ Z) (n : ℕ) (U : Scheme.{0}) (s : Sx X n U) (t : Sx Y n U),
        Sx.map f s = Sx.map g t →
        ∃! z : Sx (pullback f g) n U, Sx.map (pullback.fst f g) z = s ∧ Sx.map (pullback.snd f g) z = t := by
  intro X Y Z f g n U s t h
  let G : Spc ⥤ Type := (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk n)) ⋙
    (evaluation Scheme.{0}ᵒᵖ Type).obj (op U)
  have sq : IsPullback (G.map (pullback.fst f g)) (G.map (pullback.snd f g)) (G.map f) (G.map g) :=
    (IsPullback.of_hasPullback f g).map G
  obtain ⟨z, h1, h2⟩ := Types.exists_of_isPullback sq s t h
  refine ⟨z, ⟨h1, h2⟩, ?_⟩
  rintro z' ⟨h1', h2'⟩
  exact Types.ext_of_isPullback sq (h1'.trans h1.symm) (h2'.trans h2.symm)
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.FirstChernClassEqZsmulOfLineUnitEqZpow
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private noncomputable def trivNat : glCat 1 ⟶ glCat 1 where
  app A := (SingleObj.mapHom _ _ (1 : GL (Fin 1) A →* GL (Fin 1) A)).toCatHom
  naturality A B f := by
    have : (1 : GL (Fin 1) B →* GL (Fin 1) B).comp (Matrix.GeneralLinearGroup.map f.hom) =
        (Matrix.GeneralLinearGroup.map f.hom).comp (1 : GL (Fin 1) A →* GL (Fin 1) A) := by
      ext x : 1
      simp
    change (SingleObj.mapHom _ _ ((1 : GL (Fin 1) B →* GL (Fin 1) B).comp (Matrix.GeneralLinearGroup.map f.hom))).toCatHom =
      (SingleObj.mapHom _ _ ((Matrix.GeneralLinearGroup.map f.hom).comp (1 : GL (Fin 1) A →* GL (Fin 1) A))).toCatHom
    rw [this]

private theorem lineUnit_triv {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (y : Sx E 1 U) :
    lineUnit (L ≫ ofCatMap trivNat) y = 1 := by
  unfold lineUnit
  simp only [ofCatMap]
  have h : glMat ((ConcreteCategory.hom ((nerveMap (trivNat.app Γ(U, ⊤)).toFunctor).app (op ⦋1⦌)))
      ((ConcreteCategory.hom ((L.app (op ⦋1⦌)).app (op U))) y)) = 1 := rfl
  exact (congrArg Matrix.GeneralLinearGroup.det h).trans (map_one _)

theorem UpperTheory.firstChernClass_eq_zsmul_of_lineUnit_eq_zpow :
    DivisorAdditivity → ∀ (q : ℕ) [NeZero q] {E : Spc} (L M : E ⟶ ofCat (glCat 1)) (ε : ℤˣ), Inv q E →
        (∀ (U : Scheme.{0}) (y : Sx E 1 U), lineUnit L y = lineUnit M y ^ (ε : ℤ)) → c1 q L = (ε : ℤ) • c1 q M := by
  intro hA q _ E L M ε hE hLM
  have add : ∀ (L M N : E ⟶ ofCat (glCat 1)), GlobalTheory.EtC.Inv q E →
      (∀ (U : Scheme) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) →
        c1 q N = c1 q L + c1 q M := fun L M N => (hA q).1 L M N
  set T := L ≫ ofCatMap trivNat with hT
  have hT1 : ∀ (U : Scheme.{0}) (y : Sx E 1 U), lineUnit T y = 1 := fun U y => lineUnit_triv L y
  have h0 := add T T T hE (fun U x => by rw [hT1 U x]; simp)
  have hc : c1 q T = 0 := left_eq_add.mp h0
  rcases Int.units_eq_one_or ε with rfl | rfl
  · have h1 := add M T L hE (fun U x => by rw [hLM U x, hT1 U x]; simp)
    rw [h1, hc, add_zero]
    simp
  · have h1 := add L M T hE (fun U x => by rw [hT1 U x, hLM U x]; simp)
    rw [hc] at h1
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul]
    exact eq_neg_of_add_eq_zero_left h1.symm
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataBundleIsLocallySurjectiveEtale
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem exists_local_lift {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) {U : Scheme.{0}}
    (p : P.PA.obj (op U)) (x : U) :
    ∃ O : U.Opens, x ∈ O ∧ ∃ t : Sx (cech P.e) 0 (O : Scheme.{0}),
      ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op (O : Scheme.{0})) t =
        Quotient.mk (P.relS (O : Scheme.{0})) (P.PA.map O.ι.op p) := by
  obtain ⟨O, a, h, u, hx, hv⟩ := P.onto p.1 p.2 x
  refine ⟨O, hx, cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl), ?_⟩
  have key : ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op (O : Scheme.{0}))
      (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl)) =
      Quotient.mk (P.relS (O : Scheme.{0})) (a ≫ P.ρ, P.v a) := by
    change Quotient.mk _ (P.sv (Sx.map P.bunF (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl))) 0) = _
    rw [P.sv_bunF, pts_cechPt]
  rw [key]
  exact Quotient.sound ⟨h, u, hv⟩

theorem UpperTheory.projBundleData_bundle_isLocallySurjective_etale :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d),
        Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} ((P.bunF ≫ P.pS).app (op ⦋0⦌)) := by
  intro T W r d P
  constructor
  intro U s
  obtain ⟨p, rfl⟩ := Quotient.exists_rep s
  choose O hO t ht using fun x => exists_local_lift P p x
  have hc : TopologicalSpace.IsOpenCover O := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hO x⟩
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_
    (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hc))
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨x⟩
  exact ⟨t x, ht x⟩
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataCechExistsUniqueSimplexOfVertices
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem comp_hom_eq_of_coords {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (U : Scheme.{0})
    (a b : Sx (cech P.e) 0 U)
    (hab : ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) a = ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) b) :
    pts P.e a 0 ≫ P.e = pts P.e b 0 ≫ P.e := by
  have hq : (⟦P.sv (Sx.map P.bunF a) 0⟧ : Quotient (P.relS U)) = ⟦P.sv (Sx.map P.bunF b) 0⟧ := hab
  have hr := Quotient.exact hq
  change P.rel U _ _ at hr
  rw [PBData.sv_bunF, PBData.sv_bunF] at hr
  obtain ⟨h, u, hu⟩ := hr
  exact P.inj _ _ h u hu

theorem UpperTheory.projBundleData_cech_existsUnique_simplex_of_vertices :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → Sx (cech P.e) 0 U),
        (∀ i j, ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) (t i) = ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op U) (t j)) →
        ∃! z : Sx (cech P.e) n U, ∀ i, Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i := by
  intro T W r d P n U t ht
  let y : Fin (n + 1) → (U ⟶ P.T') := fun i => pts P.e (t i) 0
  have hy : ∀ i, y i ≫ P.e = y 0 ≫ P.e := fun i => comp_hom_eq_of_coords P U (t i) (t 0) (ht i 0)
  have key : ∀ (z : Sx (cech P.e) n U) (i : Fin (n + 1)),
      Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i ↔ pts P.e z i = y i := by
    intro z i
    constructor
    · intro h
      have := congrFun (congrArg (pts P.e) h) 0
      rw [pts_along] at this
      simpa using this
    · intro h
      apply pts_inj
      funext j
      rw [pts_along]
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hj
      simpa using h
  refine ⟨cechPt P.e n (y 0 ≫ P.e) y hy, fun i => (key _ i).2 (by rw [pts_cechPt]), ?_⟩
  intro z hz
  apply pts_inj
  rw [pts_cechPt]
  funext i
  exact (key z i).1 (hz i)
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.QuasiIsoChainsOfCechConditionOfLocallySurjective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private abbrev vtx {X : Spc} {Q : PSh} (p : X ⟶ disc.obj Q) : X.obj (op ⦋0⦌) ⟶ Q :=
  p.app (op ⦋0⦌)

private lemma vtx_cond {X : Spc} {Q : PSh} (p : X ⟶ disc.obj Q) (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    X.map (SimplexCategory.const ⦋0⦌ n.unop i).op ≫ vtx p = p.app n := by
  have h := p.naturality (SimplexCategory.const ⦋0⦌ n.unop i).op
  simpa using h

private noncomputable def nerveMap {X : Spc} {Q : PSh} (p : X ⟶ disc.obj Q) :
    X ⟶ (Arrow.mk (vtx p)).cechNerve where
  app n := WidePullback.lift (p.app n) (fun i => X.map (SimplexCategory.const ⦋0⦌ n.unop i).op)
    (fun i => vtx_cond p n i)
  naturality n n' g := by
    apply WidePullback.hom_ext
    · intro i
      erw [Category.assoc, Category.assoc, WidePullback.lift_π]
      simp only [Arrow.cechNerve]
      erw [WidePullback.lift_π, WidePullback.lift_π]
      rw [← X.map_comp]
      congr 1
    · erw [Category.assoc, Category.assoc, WidePullback.lift_base]
      simp only [Arrow.cechNerve]
      erw [WidePullback.lift_base, WidePullback.lift_base]
      simpa using p.naturality g

private theorem isIso_nerveMap_of_existsUnique_vertices {X : Spc} {Q : PSh} (p : X ⟶ disc.obj Q)
    (h : ∀ (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → Sx X 0 U),
      (∀ i j, (p.app (op ⦋0⦌)).app (op U) (t i) = (p.app (op ⦋0⦌)).app (op U) (t j)) →
      ∃! z : Sx X n U, ∀ i, Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i) :
    IsIso (_root_.nerveMap p) := by
  have hπ : ∀ (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}) (x : (X.obj n).obj (op U)) (i : Fin (n.unop.len + 1)),
      (WidePullback.π (fun _ : Fin (n.unop.len + 1) => vtx p) i).app (op U) (((_root_.nerveMap p).app n).app (op U) x)
        = (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op).app (op U) x := by
    intro n U x i
    have e : (_root_.nerveMap p).app n ≫ WidePullback.π (fun _ : Fin (n.unop.len + 1) => vtx p) i = X.map (SimplexCategory.const ⦋0⦌ n.unop i).op := by
      simp only [_root_.nerveMap]
      erw [WidePullback.lift_π]
    have e2 := NatTrans.congr_app e (op U)
    rw [NatTrans.comp_app] at e2
    simpa using ConcreteCategory.congr_hom e2 x
  have hb : ∀ (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}) (x : (X.obj n).obj (op U)),
      (WidePullback.base (fun _ : Fin (n.unop.len + 1) => vtx p)).app (op U) (((_root_.nerveMap p).app n).app (op U) x)
        = (p.app n).app (op U) x := by
    intro n U x
    have e : (_root_.nerveMap p).app n ≫ WidePullback.base (fun _ : Fin (n.unop.len + 1) => vtx p) = p.app n := by
      simp only [_root_.nerveMap]
      erw [WidePullback.lift_base]
    have e2 := NatTrans.congr_app e (op U)
    rw [NatTrans.comp_app] at e2
    simpa using ConcreteCategory.congr_hom e2 x
  have hv : ∀ (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}) (x : (X.obj n).obj (op U)) (i : Fin (n.unop.len + 1)),
      (p.app (op ⦋0⦌)).app (op U) ((X.map (SimplexCategory.const ⦋0⦌ n.unop i).op).app (op U) x)
        = (p.app n).app (op U) x := by
    intro n U x i
    have e2 := NatTrans.congr_app (vtx_cond p n i) (op U)
    rw [NatTrans.comp_app] at e2
    have e3 := ConcreteCategory.congr_hom e2 x
    simp only [ConcreteCategory.comp_apply] at e3
    exact e3
  have hbπ : ∀ (n : SimplexCategoryᵒᵖ) (U : Scheme.{0}) (w : ((Arrow.mk (vtx p)).cechNerve.obj n).obj (op U)) (i : Fin (n.unop.len + 1)),
      (p.app (op ⦋0⦌)).app (op U) ((WidePullback.π (fun _ : Fin (n.unop.len + 1) => vtx p) i).app (op U) w)
        = (WidePullback.base (fun _ : Fin (n.unop.len + 1) => vtx p)).app (op U) w := by
    intro n U w i
    have e2 := NatTrans.congr_app (WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) => vtx p) i) (op U)
    rw [NatTrans.comp_app] at e2
    simpa using ConcreteCategory.congr_hom e2 w
  have key : ∀ n, IsIso ((_root_.nerveMap p).app n) := by
    intro n
    have hU : ∀ U : Schemeᵒᵖ, IsIso (((_root_.nerveMap p).app n).app U) := by
      intro U
      obtain ⟨U⟩ := U
      rw [isIso_iff_bijective]
      constructor
      · intro x y hxy
        let t : Fin (n.unop.len + 1) → Sx X 0 U := fun i => (X.map (SimplexCategory.const ⦋0⦌ n.unop i).op).app (op U) x
        have ht : ∀ i j, (p.app (op ⦋0⦌)).app (op U) (t i) = (p.app (op ⦋0⦌)).app (op U) (t j) := by
          intro i j
          exact (hv n U x i).trans (hv n U x j).symm
        obtain ⟨z, -, huniq⟩ := h n.unop.len U t ht
        have hx : ∀ i, Sx.along (E := X) (N := n.unop.len) x (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ i) = t i := fun i => rfl
        have hy : ∀ i, Sx.along (E := X) (N := n.unop.len) y (SimplexCategory.const ⦋0⦌ ⦋n.unop.len⦌ i) = t i := by
          intro i
          have a := hπ n U x i
          have b := hπ n U y i
          rw [hxy] at a
          exact b.symm.trans a
        exact (huniq x hx).trans (huniq y hy).symm
      · intro w
        let t : Fin (n.unop.len + 1) → Sx X 0 U := fun i => (WidePullback.π (fun _ : Fin (n.unop.len + 1) => vtx p) i).app (op U) w
        have ht : ∀ i j, (p.app (op ⦋0⦌)).app (op U) (t i) = (p.app (op ⦋0⦌)).app (op U) (t j) := by
          intro i j
          exact (hbπ n U w i).trans (hbπ n U w j).symm
        obtain ⟨z, hz, -⟩ := h n.unop.len U t ht
        refine ⟨z, ?_⟩
        apply yonedaEquiv.symm.injective
        apply WidePullback.hom_ext
        · intro i
          apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp]
          erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact (hπ n U z i).trans (hz i)
        · apply yonedaEquiv.injective
          simp only [yonedaEquiv_comp]
          erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact (hb n U z).trans ((hv n U z 0).symm.trans ((congrArg (fun a => (p.app (op ⦋0⦌)).app (op U) a) (hz 0)).trans (hbπ n U w 0)))
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

theorem UpperTheory.quasiIso_chains_of_cech_condition_of_locallySurjective :
    ∀ (R : Type) [CommRing R] (X : Spc) (Q : PSh) (p : X ⟶ disc.obj Q),
        (∀ (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → Sx X 0 U),
          (∀ i j, (p.app (op ⦋0⦌)).app (op U) (t i) = (p.app (op ⦋0⦌)).app (op U) (t j)) →
          ∃! z : Sx X n U, ∀ i, Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i) →
        Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (p.app (op ⦋0⦌)) →
        QuasiIso ((chains R).map p) := by
  intro R _ X Q p h hs
  have e : _root_.nerveMap p ≫ (Arrow.mk (vtx p)).augmentedCechNerve.hom = p := by
    ext n : 2
    simp [_root_.nerveMap, Arrow.augmentedCechNerve]
  haveI := isIso_nerveMap_of_existsUnique_vertices p h
  haveI := quasiIso_chains_cech_of_isLocallySurjective R (X _⦋0⦌) Q (vtx p) hs
  rw [← e, Functor.map_comp]
  infer_instance
end

