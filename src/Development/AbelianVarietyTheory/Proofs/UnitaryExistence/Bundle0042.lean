module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.SpanEqTopOfForallMaximal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieMultIffFinrank
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace GlobalTheory.LieExt

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)
  {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ (Over.pullback g).obj G} (hx : IsUnivChart _ n x)
  {O : Type} [CommRing O] (act : Geo.Tor.OAct O G') (b : O → (G ⟶ G))
  (hab : ∀ a, (act.act a).left ≫ F = F ≫ (b a).left)
  (act' : O → ((Over.pullback g).obj G ⟶ (Over.pullback g).obj G)) [∀ a, IsMonHom (act' a)]
  (hact' : ∀ a, act' a = (Over.pullback g).map (b a)) (τ : O →+* k)


include hc hg hab hact' in
theorem lieMult_of_finrank {N : ℕ} (hN : Module.finrank k (eigLat hx act' (fun a => τ a)) = N) :
    Geo.Tor.LieMult act tk τ N := by
  let B := Module.finBasisOfFinrankEq k _ hN
  have hT : ∀ (w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') v, Rel (F := F) tk g w v →
      (Geo.Tor.IsLieEigen act tk τ w ↔ IsTan v ∧ ∀ a, v ≫ act' a = spMap (scaleD (τ a)) ≫ v) := by
    intro w v h
    refine and_congr (tan_iff hc hg h) (forall_congr' fun a => ?_)
    rw [hact']
    exact eig_iff hc (act.act a) (b a) (hab a) (τ a) h
  have hmem : ∀ c, c ∈ eigLat hx act' (fun a => τ a) ↔
      ∀ a, tvec (x := x) c ≫ act' a = spMap (scaleD (τ a)) ≫ tvec (x := x) c := by
    intro c
    rw [mem_eigLat_iff]
    exact forall_congr' fun a => (tvec_eig_iff hx (act' a) c (τ a)).symm
  choose vB hv using fun i => rel_exists_w hc hg (tvec (x := x) (B i : Fin n → k))
  let P : (Fin N → k) → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G) :=
    fun d => (List.ofFn fun i => spMap (scaleD (d i)) ≫ tvec (x := x) (B i : Fin n → k)).prod
  let Wd : (Fin N → k) → (viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') :=
    fun d => (List.ofFn fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i).prod
  have hPW : ∀ d, Rel (F := F) tk g (Wd d) (P d) := fun d => rel_prod hc hg _ _ fun i => rel_pre _ (hv i)
  have list_prod_tan_aux : ∀ {M : ℕ} (u : Fin M → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G))
      (hu : ∀ i, IsTan (u i)), ∃ h : IsTan (List.ofFn u).prod,
        tcoord hx _ h = ∑ i, tcoord hx (u i) (hu i) := by
    intro M
    induction M with
    | zero =>
      intro u hu
      have e0 : (List.ofFn u).prod = 1 := by simp
      refine ⟨e0 ▸ isTan_one, ?_⟩
      rw [tcoord_congr hx e0 _ isTan_one, tcoord_one]
      simp
    | succ M ih =>
      intro u hu
      obtain ⟨h, e⟩ := ih (fun i => u i.succ) (fun i => hu i.succ)
      have e0 : (List.ofFn u).prod = u 0 * (List.ofFn fun i => u i.succ).prod := by
        rw [List.ofFn_succ, List.prod_cons]
      refine ⟨e0 ▸ isTan_mul (hu 0) h, ?_⟩
      rw [tcoord_congr hx e0 _ (isTan_mul (hu 0) h), tcoord_mul hx (hu 0) h, e, Fin.sum_univ_succ]
  have hPeq : ∀ d, P d = tvec (x := x) (∑ i, d i • (B i : Fin n → k)) := by
    intro d
    obtain ⟨h, e⟩ := list_prod_tan_aux (M := N) (fun i => spMap (scaleD (d i)) ≫ tvec (x := x) (B i : Fin n → k))
      (fun i => isTan_scale (d i) (isTan_tvec hx _))
    refine (tcoord_spec hx (P d) h).trans ?_
    show tvec (x := x) (tcoord hx (P d) h) = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      (tcoord_scale hx (d i) (isTan_tvec hx _)).trans (by rw [tcoord_tvec])
  refine ⟨vB, fun i => (hT _ _ (hv i)).2 ⟨isTan_tvec hx _, (hmem _).1 (B i).2⟩, fun w hw => ?_⟩
  obtain ⟨v, hwv⟩ := rel_exists_v hc hg (X := sp (R₀ := k) (DualNumber k)) w
  obtain ⟨ht, he⟩ := (hT _ _ hwv).1 hw
  obtain ⟨c, rfl⟩ : ∃ c, tvec (x := x) c = v := ⟨_, (tcoord_spec hx v ht).symm⟩
  let c' : eigLat hx act' (fun a => τ a) := ⟨c, (hmem c).2 he⟩
  have key : ∀ d : Fin N → k, (∃ u : Fin N → (Geo.Tor.epsPt tk ⟶ G'),
      (∀ i, (u i).left = Geo.Tor.spMap (Geo.Tor.epsScale (d i)) ≫ (vB i).left) ∧ w = (List.ofFn u).prod) ↔
      B.equivFun c' = d := fun d => by
    have e₁ : B.equivFun c' = d ↔ c = ∑ i, d i • (B i : Fin n → k) := by
      rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
      simp [c']
    have e₂ : w = Wd d ↔ c = ∑ i, d i • (B i : Fin n → k) := by
      refine (rel_eq_iff hc hwv (hPW d)).trans ?_
      rw [hPeq]
      exact ⟨fun h => tvec_inj hx h, fun h => by rw [← h]⟩
    rw [e₁, ← e₂]
    constructor
    · rintro ⟨u, hu, hwu⟩
      have hu' : u = fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i :=
        funext fun i => Over.OverMorphism.ext (hu i)
      rw [hwu, hu']
    · intro h
      exact ⟨fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i, fun i => rfl, h⟩
  exact (existsUnique_congr key).2 existsUnique_eq'

end Count

theorem lieMult_iff_finrank {k K : Type} [Field k] [Field K] [Algebra k K] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] {n : ℕ} {xc : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n xc)
    {O : Type} [CommRing O] (act : Geo.Tor.OAct O G) [∀ a, IsMonHom (act.act a)] (χ : O →+* k) (N : ℕ) :
    Geo.Tor.LieMult act (fB k K) ((algebraMap k K).comp χ) N ↔
      Module.finrank k (eigLat hx act.act χ) = N := by
  obtain ⟨x', hx', hcomp⟩ := tanBC_alg (R := k) (R' := K) G n xc hx
  have hpt : ∀ c : Fin n → k, pushR G (tvec (x := x') (algebraMap k K ∘ c)) =
      spMap (dualMapA k K) ≫ tvec (x := xc) c := fun c =>
    Over.OverMorphism.ext (by rw [pushR_left, hcomp c]; rfl)
  have hLk : ∀ a (c : Fin n → k), tmap hx' ((Over.pullback (fB k K)).map (act.act a)) (algebraMap k K ∘ c) =
      algebraMap k K ∘ tmap hx (act.act a) c := by
    intro a c
    apply tvec_inj hx'
    apply pushR_inj G
    rw [tvec_tmap hx', pushR_map, hpt, hpt, tvec_tmap hx, Category.assoc]
  have e0 : Module.finrank k (eigLat hx act.act χ) =
      Module.finrank K (eigLat hx' (fun a => (Over.pullback (fB k K)).map (act.act a))
        (fun a => (algebraMap k K).comp χ a)) :=
    finrank_eig_bc (fun a => tmap hx (act.act a))
      (fun a => tmap hx' ((Over.pullback (fB k K)).map (act.act a))) hLk χ
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  rw [e0]
  exact ⟨finrank_of_lieMult (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id _) hx' act act.act
      (fun a => by simp) _ (fun a => rfl) _,
    lieMult_of_finrank (Geo.Tor.isGrpPullback_of_iso (Iso.refl G)) (Category.comp_id _) hx' act act.act
      (fun a => by simp) _ (fun a => rfl) _⟩

theorem lieMult_extend_iff {k K : Type} [Field k] [Field K] (φ : k →+* K) (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [Smooth G.hom] {O : Type} [CommRing O] (act : Geo.Tor.OAct O G) (χ : O →+* k) (N : ℕ) :
    Geo.Tor.LieMult act (Geo.Tor.spMap φ) (φ.comp χ) N ↔ Geo.Tor.LieMult act (𝟙 _) χ N := by
  let _ := φ.toAlgebra
  have := act.hom
  obtain ⟨n, x, hx⟩ := univChartLoc G
  have h := lieMult_iff_finrank (K := k) G hx act χ N
  have e : fB k k = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rw [e, Algebra.algebraMap_self, RingHom.id_comp] at h
  exact (lieMult_iff_finrank (K := K) G hx act χ N).trans h.symm

theorem exists_comp_eq {k K O : Type} [Field k] [IsAlgClosed k] [Field K] [CommRing O] [Algebra.IsIntegral ℤ O]
    (φ : k →+* K) (τ : O →+* K) : ∃ χ : O →+* k, φ.comp χ = τ := by
  let _ := φ.toAlgebra
  have h : ∀ a, ∃ z : k, φ z = τ a := fun a => by
    have hi : IsIntegral k (τ a) := ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map τ.toIntAlgHom).tower_top
    exact minpoly.mem_range_of_degree_eq_one k _
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi))
  choose f hf using h
  have inj := φ.injective
  exact ⟨⟨⟨⟨f, inj (by simp [hf])⟩, fun a b => inj (by simp [hf])⟩, inj (by simp [hf]),
    fun a b => inj (by simp [hf])⟩, RingHom.ext hf⟩

theorem detCond_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (D : Geo.Tor.Datum H)
    {k K : Type} [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [Smooth G.hom] (act : Geo.Tor.OAct (𝓞 E) G) {ρ : k} (h : Geo.Tor.DetCond D act (𝟙 _) ρ) :
    Geo.Tor.DetCond D act (Geo.Tor.spMap φ) (φ ρ) := by
  intro τ
  obtain ⟨χ, rfl⟩ := exists_comp_eq φ τ
  rw [lieMult_extend_iff, lieMult_extend_iff]
  exact ⟨fun e => (h χ).1 (φ.injective e), fun e => (h χ).2 fun e' => e (congrArg φ e')⟩

end GlobalTheory.LieExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnivChartOfStandardSmooth
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLoc

section Chart

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Chart

variable {R : Type} [CommRing R]

theorem univChart_of_standardSmooth (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (S : Type) [CommRing S] [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (j : sp (R₀ := R) S ⟶ G) (ε : S →ₐ[R] R) (hε : spMap ε ≫ j = 1)
    (hj : ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R), IsNilpotent (RingHom.ker aug) →
      ∀ y : sp (R₀ := R) A ⟶ G, spMap aug ≫ y = 1 → ∃ φ : S →ₐ[R] A, y = spMap φ ≫ j)
    (hinj : ∀ (A : Type) [CommRing A] [Algebra R A] (φ φ' : S →ₐ[R] A),
      spMap φ ≫ j = spMap φ' ≫ j → φ = φ') :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G, IsUnivChart G n x := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n R S
  letI : Algebra (MvPolynomial (Fin n) R) S := g.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin n) R) S :=
    IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) R) S := hg
  have hπ : ∀ m : ℕ, ∃ π : S →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε ∧
      ∀ i, π (sX (R := R) i) = algebraMap R _ (ε (sX (R := R) i)) + zR m i := fun m =>
    etale_exists (n := n) ε (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun i => by
      rw [map_add (f := _), AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])
  choose π hπaug hπX using hπ
  refine ⟨fun m => spMap (π m) ≫ j, fun m => ?_, fun m => ?_, ?_⟩
  · rw [← Category.assoc, spMap_comp]
    congr 2
    refine etale_ext (n := n) ε (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_trunc]
      exact hπaug (m + 1)
    · exact hπaug m
    · intro i
      rw [AlgHom.comp_apply, hπX, hπX, map_add (f := _), AlgHom.commutes]
      rfl
  · have e : (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp ε := by
      refine etale_ext (n := n) ε (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_
      · rw [← AlgHom.comp_assoc, jetAug_comp_zero]
        exact hπaug m
      · ext s
        simp
      · intro i
        rw [AlgHom.comp_apply, hπX, map_add (f := _), AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]
        rfl
    rw [← Category.assoc, spMap_comp, e, ← spMap_comp, Category.assoc, hε, comp_one']
  · intro A _ _ aug m hJ y hy
    have hJn := nil_of_pow _ hJ
    obtain ⟨φ, rfl⟩ := hj A aug hJn y hy
    have hφ : aug.comp φ = ε := hinj _ _ _ (by rw [← spMap_comp, Category.assoc, hy, hε])
    have hmem : ∀ i : Fin n, φ (sX (R := R) (S := S) i) - algebraMap R A (ε (sX (R := R) (S := S) i)) ∈
        RingHom.ker aug := by
      intro i
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← AlgHom.comp_apply, hφ, sub_self]
    let ψ := jetLift (R := R) (RingHom.ker aug) hJ
      (fun i : Fin n => φ (sX (R := R) (S := S) i) - algebraMap R A (ε (sX (R := R) (S := S) i))) hmem
    have hψaug : aug.comp ψ = jetAug R (Fin n) m := jet_ext fun i => by
      rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hmem i
    have hψπ : ψ.comp (π m) = φ := by
      refine etale_ext (n := n) ε aug hJn _ _ ?_ hφ ?_
      · rw [← AlgHom.comp_assoc, hψaug]
        exact hπaug m
      · intro i
        rw [AlgHom.comp_apply, hπX, map_add (f := _), AlgHom.commutes, jetLift_zR, add_sub_cancel]
    refine ⟨ψ, ⟨hψaug, ?_⟩, ?_⟩
    · rw [← Category.assoc, spMap_comp, hψπ]
    · rintro ψ₂ ⟨_, h2⟩
      rw [← Category.assoc, spMap_comp] at h2
      have h4 := (hinj _ _ _ h2).symm
      apply jet_ext
      intro i
      rw [jetLift_zR]
      have := AlgHom.congr_fun h4 (sX (R := R) i)
      rw [AlgHom.comp_apply, hπX, map_add (f := _), AlgHom.commutes] at this
      rw [← this, add_sub_cancel_left]

theorem univChart_baseChange (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (S : Type) [CommRing S] [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (j : sp (R₀ := R) S ⟶ G) [IsOpenImmersion j.left] (R' : Type) [CommRing R'] [Algebra R R']
    (ε : S →ₐ[R] R') (hε : spMap ε ≫ j = 1) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R') (JetR R' (Fin n) m) ⟶ (Over.pullback (fB R R')).obj G,
      IsUnivChart _ n x := by
  let inc : S →ₐ[R] R' ⊗[R] S := Algebra.TensorProduct.includeRight
  let j' : sp (R₀ := R') (R' ⊗[R] S) ⟶ (Over.pullback (fB R R')).obj G := pullR G (spMap inc ≫ j)
  have hpush : ∀ (A : Type) [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (φ : R' ⊗[R] S →ₐ[R'] A), pushR G (spMap φ ≫ j') = spMap ((φ.restrictScalars R).comp inc) ≫ j := by
    intro A _ _ _ _ φ
    rw [pushR_spMap, pushR_pullR, ← Category.assoc, spMap_comp]
  have hlift : ∀ (A : Type) [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (φ : S →ₐ[R] A), ∃ φ' : R' ⊗[R] S →ₐ[R'] A, (φ'.restrictScalars R).comp inc = φ := by
    intro A _ _ _ _ φ
    refine ⟨Algebra.TensorProduct.lift (Algebra.ofId R' A) φ fun _ _ => Commute.all _ _, ?_⟩
    ext s
    simp [inc]
  obtain ⟨ε', hε'⟩ := hlift R' ε
  refine univChart_of_standardSmooth _ n (R' ⊗[R] S) j' ε' ?_ ?_ ?_
  · apply pushR_inj G
    rw [hpush, hε', hε, pushR_one]
  · intro A _ _ aug hJ y hy
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have _ : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hz : spMap (aug.restrictScalars R) ≫ pushR G y = spMap ε ≫ j := by
      rw [← pushR_spMap, hy, pushR_one, hε]
    obtain ⟨φ, h1, -⟩ := SqZero.exists_chart_pt_of_nil j (aug.restrictScalars R) (aug_surj aug)
      (fun a ha => elt_nil _ hJ a ha) _ _ hz
    obtain ⟨φ', h2⟩ := hlift A φ
    refine ⟨φ', pushR_inj G ?_⟩
    rw [hpush, h2, h1]
  · intro A _ _ φ φ' h
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have _ : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h1 := congrArg (pushR G) h
    rw [hpush, hpush] at h1
    have h2 := SqZero.chart_inj j h1
    exact Algebra.TensorProduct.ext (Subsingleton.elim _ _) h2

theorem exists_standardSmooth_chart (X : Over (Spec (CommRingCat.of R))) (n : ℕ)
    (h : SmoothOfRelativeDimension n X.hom) (x : X.left) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ X),
      Algebra.IsStandardSmoothOfRelativeDimension n R S ∧ IsOpenImmersion j.left ∧
        x ∈ Set.range j.left := by
  obtain ⟨B, j₀, hj₀, ⟨q, hq⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X.left) (x := x) (U := ⊤) trivial
  letI : Algebra R B := (Spec.preimage (j₀ ≫ X.hom)).hom.toAlgebra
  let j : sp (R₀ := R) B ⟶ X := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ X.hom)).symm
  have h1 : SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    have e : j₀ ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := Over.w j
    rw [← e, ← zero_add n]
    infer_instance
  obtain ⟨s, hs, H⟩ := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)
    (φ := CommRingCat.ofHom (algebraMap R B))).1 h1
  obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ (q : PrimeSpectrum B).asIdeal := by
    by_contra! hc
    exact (q : PrimeSpectrum B).2.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 hc))
  have hq' : (q : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away t))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away t) t]
    exact htq
  obtain ⟨q', hq'⟩ := hq'
  have Ht := H t hts
  rw [CommRingCat.hom_ofHom, ← IsScalarTower.algebraMap_eq,
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at Ht
  refine ⟨Localization.Away t, inferInstance, inferInstance, spMap (SqZero.awayHom R t) ≫ j, Ht, ?_,
    q', ?_⟩
  · change IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away t))) ≫ j₀)
    infer_instance
  · rw [← hq, ← hq']
    rfl

theorem exists_univChart_away (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (h : SmoothOfRelativeDimension n G.hom) (p : PrimeSpectrum R) :
    ∃ r ∉ p.asIdeal, ∃ x : ∀ m : ℕ, sp (R₀ := Localization.Away r)
      (JetR (Localization.Away r) (Fin n) m) ⟶ (Over.pullback (fB R (Localization.Away r))).obj G,
      IsUnivChart _ n x := by
  let e : Spec (CommRingCat.of R) ⟶ G.left := η[G].left
  obtain ⟨S, _, _, j, hS, hj, hmem⟩ := exists_standardSmooth_chart G n h (e p)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := (e ⁻¹ᵁ j.left.opensRange).1) hmem (e ⁻¹ᵁ j.left.opensRange).2
  refine ⟨r, hr, ?_⟩
  obtain ⟨ε, hε⟩ := SqZero.exists_chart_pt j (1 : sp (R₀ := R) (Localization.Away r) ⟶ G) (by
    rintro _ ⟨t, rfl⟩
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this)
  exact univChart_baseChange G n S j _ ε hε.symm

end Chart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem lie_locally_free :
    ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (n : ℕ),
      SmoothOfRelativeDimension n G.hom → ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal,
        ∃ v : Fin n → (epsR (Localization.Away r) ⟶
          (Over.pullback (spMap (algebraMap R (Localization.Away r)))).obj G), IsLieBasis v := by
  intro R _ G _ _ n h p
  obtain ⟨r, hr, x, hx⟩ := exists_univChart_away G n h p
  exact ⟨r, hr, _, Chart.basis_of_chart hx⟩

end GlobalTheory.LieLoc
end
end

