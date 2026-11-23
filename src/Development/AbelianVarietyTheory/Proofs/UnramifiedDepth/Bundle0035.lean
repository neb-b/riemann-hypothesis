module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Statements.ChartPoints.ChartPt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.FormalGroupCoeffSecondLinear

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsStruct
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
open scoped CategoryTheory.Obj

private theorem mul_left_fst {S' S : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {Y : Over S} {Z : Over S'}
    (e : Y.left ⟶ Z.left) (a b : Z ⟶ (Over.pullback f).obj G) (za zb : Y ⟶ G)
    (ha : e ≫ a.left ≫ pullback.fst G.hom f = za.left) (hb : e ≫ b.left ≫ pullback.fst G.hom f = zb.left) :
    e ≫ (a * b).left ≫ pullback.fst G.hom f = (za * zb).left := by
  let F := Over.pullback f
  let m : Z ⟶ F.obj (G ⊗ G) := lift a b ≫ Functor.LaxMonoidal.μ F G G
  have key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom f) ≫ g.left =
      (m ≫ F.map g).left ≫ pullback.fst G.hom f := by
    intro g
    rw [Category.assoc, ← SplitTorusPoints.map_left_fst, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  have h1 : m ≫ F.map (fst G G) = a := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))
  have h2 : m ≫ F.map (snd G G) = b := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))
  have h3 : m ≫ F.map μ[G] = a * b := Category.assoc _ _ _
  have hq : e ≫ m.left ≫ pullback.fst (G ⊗ G).hom f = (lift za zb).left := by
    apply pullback.hom_ext
    · have := key (fst G G)
      rw [h1] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (ha.trans
        (congrArg (fun t => t.left) (lift_fst za zb)).symm))
    · have := key (snd G G)
      rw [h2] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (hb.trans
        (congrArg (fun t => t.left) (lift_snd za zb)).symm))
  have := key μ[G]
  rw [h3] at this
  rw [← this, ← Category.assoc, hq]
  rfl

end

private theorem mono_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) : Mono (Out.thick R I e) := by
  have : IsClosedImmersion (Out.thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

private theorem exists_struct {R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (S : Type) [CommRing S] [Algebra R S]
    (h : Kills I k S) : ∃ s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))),
      s ≫ Out.thick R I k = (sp (R₀ := R) S).hom := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap R S) h)), ?_⟩
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))) = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem exists_equiv {B : Scheme.{0}} (X : Type) [AddCommGroup X] (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ B) :
    ∃ e : (Over.mk s ⟶ splitTorus B X) ≃* (Multiplicative X →* Sˣ), ∀ t χ, e t = χ ↔
      ∀ x : X, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) = (χ (Multiplicative.ofAdd x) : S) := by
  let u : Γ(Spec (CommRingCat.of S), ⊤)ˣ ≃* Sˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.toMulEquiv
  refine ⟨(splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight), fun t χ => ?_⟩
  have hv : ∀ x : X, ((((splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight)) t
      (Multiplicative.ofAdd x) : Sˣ) : S) = (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) := fun x =>
    congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (splitTorusPointsEquiv_val B X (Over.mk s) t x)
  constructor
  · rintro rfl x
    exact (hv x).symm
  · intro h
    ext x
    exact (hv x).trans (h x)

private theorem irel_iff {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegPre R} {k : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G)
    (S : Type) [CommRing S] [Algebra R S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))))
    (hs : s ≫ Out.thick R I k = (sp (R₀ := R) S).hom) :
    ∃ e : (Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X) ≃* (Multiplicative D.X →* Sˣ),
      ∀ χ z, IRel c S χ z ↔ (e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k) = z.left := by
  obtain ⟨e, he⟩ := exists_equiv D.X S s
  refine ⟨e, fun χ z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨w, hw, hz⟩
    have := mono_thick I k
    have hws : w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).hom = s := by
      rw [← cancel_mono (Out.thick R I k), hs, ← Over.w z, ← hz, ← Over.w c.i]
      simp only [Category.assoc]
      exact congrArg (fun g => w ≫ c.i.left ≫ g) (Over.w (Out.fstG I k G)).symm
    let t : Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X := Over.homMk w hws
    have ht : e t = χ := (he t χ).2 hw
    rw [← ht, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).trans hz
  · exact ⟨(e.symm χ).left, (he _ χ).1 (e.apply_symm_apply χ), (Category.assoc _ _ _).symm.trans h⟩


open scoped CategoryTheory.Obj in
theorem irel_points : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G), (∀ (S : Type) [CommRing S] [Algebra R S], Kills I k S → (∀ χ, ∃! z, IRel c S χ z) ∧ (∀ χ χ' z z', IRel c S χ z → IRel c S χ' z' → IRel c S (χ * χ') (z * z')) ∧ ∀ χ χ' z, IRel c S χ z → IRel c S χ' z → χ = χ') ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') χ z, IRel c S χ z → IRel c S' ((Units.map (φ : S →* S')).comp χ) (spMap φ ≫ z) := by
  intro R _ _ I D k G _ _ c
  refine ⟨fun S _ _ hS => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_struct I k S hS
    obtain ⟨e, he⟩ := irel_iff c S s hs
    refine ⟨fun χ => ?_, fun χ χ' z z' h h' => ?_, fun χ χ' z h h' => ?_⟩
    · refine ⟨Over.homMk ((e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k)) ?_,
        (he _ _).2 rfl, fun z hz => Over.OverMorphism.ext ((he _ _).1 hz).symm⟩
      rw [← hs]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Out.thick R I k) (Over.w (e.symm χ ≫ c.i)))))
    · rw [he] at h h' ⊢
      have := c.i_hom
      rw [map_mul, MonObj.mul_comp]
      exact (Category.id_comp _).symm.trans (mul_left_fst (Out.thick R I k) G (Y := sp S) (Z := Over.mk s) (𝟙 _)
        _ _ z z' ((Category.id_comp _).trans h) ((Category.id_comp _).trans h'))
    · rw [he] at h h'
      have := mono_thick I k
      have h1 : e.symm χ ≫ c.i = e.symm χ' ≫ c.i :=
        Over.OverMorphism.ext ((cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (h.trans h'.symm))
      exact e.symm.injective (c.isKernel.hom_ext h1 (toUnit_unique _ _))
  · rintro S _ _ S' _ _ φ χ z ⟨w, hw, hz⟩
    refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ w, fun x => ?_, ?_⟩
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← RingHom.comp_apply,
        ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, RingHom.comp_apply, hw]
      rfl
    · rw [Category.assoc, hz]
      rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTateOfCharacter
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChTor

namespace GlobalTheory.ChTor

theorem exists_tate_of_character :
    ∀ (Γ : Type) [Group Γ] (U : Type) [CommGroup U] (p : ℕ), 1 ≤ p → (∀ a b : Γ, a * b = b * a) → ∀ e : ℕ → Γ → Γ → U, (∀ k : ℕ, 1 ≤ k → (∀ (l : ℕ) (z s : Γ), 1 ≤ l → z ^ k = 1 → s ^ (k * l) = 1 → e (k * l) z s = e k z (s ^ l)) ∧ ∀ κ : Γ → U, (∀ z z', z ^ k = 1 → z' ^ k = 1 → κ (z * z') = κ z * κ z') → ∃! s : Γ, s ^ k = 1 ∧ ∀ z, z ^ k = 1 → e k z s = κ z) → ∀ κ : Γ → U, (∀ z z', (∃ m, z ^ (p ^ m) = 1) → (∃ m, z' ^ (p ^ m) = 1) → κ (z * z') = κ z * κ z') → ∃ s : ℕ → Γ, (∀ m, s m ^ (p ^ m) = 1 ∧ s (m + 1) ^ p = s m) ∧ ∀ m z, z ^ (p ^ m) = 1 → e (p ^ m) z (s m) = κ z := by
  intro Γ _ U _ p hp hc e he κ hκ
  have hpm : ∀ m : ℕ, 1 ≤ p ^ m := fun m => Nat.one_le_pow _ _ hp
  have key : ∀ m : ℕ, ∃! s : Γ, s ^ (p ^ m) = 1 ∧ ∀ z, z ^ (p ^ m) = 1 → e (p ^ m) z s = κ z :=
    fun m => (he (p ^ m) (hpm m)).2 κ (fun z z' hz hz' => hκ z z' ⟨m, hz⟩ ⟨m, hz'⟩)
  choose s hs hu using key
  refine ⟨s, fun m => ⟨(hs m).1, ?_⟩, fun m => (hs m).2⟩
  have h1 : s (m + 1) ^ (p ^ m * p) = 1 := by rw [← pow_succ]; exact (hs (m + 1)).1
  apply hu m
  refine ⟨by rw [← pow_mul, mul_comm]; exact h1, fun z hz => ?_⟩
  rw [← (he (p ^ m) (hpm m)).1 p z (s (m + 1)) hp hz h1, ← pow_succ]
  apply (hs (m + 1)).2
  rw [pow_succ, pow_mul, hz, one_pow]

end GlobalTheory.ChTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHom
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_comp_single {R : Type} [CommRing R] {d : ℕ} (φ ψ : Pt R 1 d)
    (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) : lin (comp1 φ ψ) = lin φ * lin ψ := by
  ext i j
  have h := coeff_lin_ev (m := 1) ![ψ] (by intro k l; fin_cases k; exact hψ l) (φ i) (0, j)
  rw [Fintype.sum_prod_type, Fin.sum_univ_one] at h
  rw [Matrix.mul_apply]
  exact h

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_formal_add {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (φ ψ : Pt R 1 d)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hψ : ∀ i, MvPowerSeries.constantCoeff (ψ i) = 0) : lin (F.add φ ψ) = lin φ + lin ψ := by
  ext i j
  have h := coeff_lin_ev (m := 2) ![φ, ψ]
    (by intro k l; fin_cases k; exacts [hφ l, hψ l]) (F.F i) (0, j)
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [formal_group_coeff_first_linear, formal_group_coeff_second_linear, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  exact h.trans (congrArg₂ (· + ·) (_root_.one_mul _) (_root_.one_mul _))

open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA in
private theorem linear_part_zero_point {R : Type} [CommRing R] {d : ℕ} : lin (pt R (n := 1) d 0) = 1 := by
  ext i j
  change MvPowerSeries.coeff _ (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 d) = _
  rw [coeff_X_single, Matrix.one_apply]
  simp [eq_comm]

theorem linPart_act_ringHom : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d) (OE : Type) [CommRing OE] (act : Geo.Tor.Germ.OAct OE F) (S : Type) [CommRing S] (β : R →+* S), ∃ ρ : OE →+* Matrix (Fin d) (Fin d) S, ∀ a, ρ a = linPart (actMap β act a) ∧ ρ a = (lin (act.act a)).map β := by
  intro R _ d F OE _ act S _ β
  let ρ₀ : OE →+* Matrix (Fin d) (Fin d) R := RingHom.mk'
    { toFun := fun a => lin (act.act a)
      map_one' := by rw [act.one_act, linear_part_zero_point]
      map_mul' := fun a b => by rw [act.mul_act, linear_part_comp_single _ _ (act.const b)] }
    (fun a b => by
      change lin (act.act (a + b)) = lin (act.act a) + lin (act.act b)
      rw [act.add_act, linear_part_formal_add _ _ _ (act.const a) (act.const b)])
  refine ⟨(β.mapMatrix).comp ρ₀, fun a => ⟨?_, rfl⟩⟩
  ext i j
  change β (MvPowerSeries.coeff _ (act.act a i)) =
    MvPowerSeries.coeff _ (MvPowerSeries.map β (act.act a i))
  rw [MvPowerSeries.coeff_map]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupLawJacobianExtensionChangeCoeff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma map_sub' {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (a' : Fin m → Fin d → PS S n e) (h : ∀ i j, MvPowerSeries.map β (a i j) = a' i j) :
    MvPowerSeries.map β (sub a f) = sub a' (MvPowerSeries.map β f) := by
  unfold sub
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2) (fun q => ha q.1 q.2))]
  simp only [h]

private lemma cc_sub {R : Type} [CommRing R] {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub a f) = 0 := by
  unfold sub
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
      (fun q => ha q.1 q.2)) (fun q => ha q.1 q.2) hf

private lemma ev_eq {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Fin d → PS R n d) (f : PS R m d) :
    ev a f = sub a f := rfl

private lemma map_pt {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.map β (pt R d j i) = pt S d j i := by simp [pt]

private lemma cc_pt {R : Type} [CommRing R] {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (pt R d j i) = 0 := by simp [pt]

private lemma map_subst_single {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d) :
    MvPowerSeries.map β (sub ![x] f) =
      sub ![fun j => MvPowerSeries.map β (x j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by fin_cases i; exact hx j) f _ (fun i j => by fin_cases i; rfl)

private lemma map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d) :
    MvPowerSeries.map β (sub ![x, y] f) =
      sub ![fun j => MvPowerSeries.map β (x j), fun j => MvPowerSeries.map β (y j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f _ (fun i j => by fin_cases i <;> rfl)

private lemma constCoeff_subst_single {R : Type} [CommRing R] {n d e : ℕ}
    (x : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0) (f : PS R 1 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x] f) = 0 :=
  cc_sub _ (fun i j => by fin_cases i; exact hx j) f hf

private lemma constantCoeff_sub2_eq_zero {R : Type} [CommRing R] {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x, y] f) = 0 :=
  cc_sub _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f hf

private lemma isHomF_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ}
    (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (φ : Fin e → PS R 1 d)
    (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0) (h : IsHomF F F' φ) :
    IsHomF (fun j => MvPowerSeries.map β (F j)) (fun j => MvPowerSeries.map β (F' j))
      (fun j => MvPowerSeries.map β (φ j)) := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun j => by simp [MvPowerSeries.constantCoeff_map, h0], fun j => ?_⟩
  have := congrArg (MvPowerSeries.map β) (h1 j)
  simp only [ev_eq] at this ⊢
  rw [map_subst_single β _ hF, map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))
    (fun i => constCoeff_subst_single _ (cc_pt _) _ (h0 i))] at this
  simp only [map_subst_single β _ (cc_pt _), map_pt] at this
  exact this

private lemma lin_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d e : ℕ} (φ : Fin e → PS R 1 d) :
    lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β := by
  ext i j
  simp [lin, MvPowerSeries.coeff_map]

private noncomputable def mapLaw {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d : ℕ} (F : FGLaw R d) :
    FGLaw S d where
  F := F.mapF β
  const i := by simp [FGLaw.mapF, MvPowerSeries.constantCoeff_map, F.const]
  unit i := by
    have := congrArg (MvPowerSeries.map β) (F.unit i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun _ => by simp) (cc_pt _)] at this
    simp only [map_pt, Pi.zero_apply, map_zero, MvPowerSeries.map_X] at this
    exact this
  comm i := by
    have := congrArg (MvPowerSeries.map β) (F.comm i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _)] at this
    simp only [map_pt] at this
    exact this
  assoc i := by
    have := congrArg (MvPowerSeries.map β) (F.assoc i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l)) (cc_pt _),
      map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l))] at this
    simp only [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _), map_pt] at this
    exact this

theorem changeCoeff_law_lin_extSer : ∀ (R S : Type) [CommRing R] [CommRing S] (β : R →+* S), (∀ (d : ℕ) (F : FGLaw R d), ∃ F' : FGLaw S d, F'.F = F.mapF β) ∧ (∀ (d e : ℕ) (φ : Fin e → PS R 1 d), lin (fun j => MvPowerSeries.map β (φ j)) = (lin φ).map β) ∧ ∀ (d g r : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q → ExtSer (F.mapF β) (FB.mapF β) (fun j => MvPowerSeries.map β (J j)) (fun j => MvPowerSeries.map β (Q j)) := by
  intro R S _ _ β
  refine ⟨fun d F => ⟨mapLaw β F, rfl⟩, fun d e φ => lin_map β φ, fun d g r F FB J Q h => ⟨?_, ?_, ?_⟩⟩
  · have hg : (fun j => MvPowerSeries.map β (gmF R r j)) = gmF S r := by
      funext j; simp [gmF]
    rw [← hg]
    exact isHomF_map β _ _ _ (fun j => by simp [gmF]) h.homI
  · exact isHomF_map β _ _ _ F.const h.homQ
  · rw [lin_map, lin_map]
    obtain ⟨h0, A', B', h1, h2, h3⟩ := h.exact
    refine ⟨?_, A'.map β, B'.map β, ?_, ?_, ?_⟩
    · rw [← Matrix.map_mul, h0]; simp
    · rw [← Matrix.map_mul, h1]; simp
    · rw [← Matrix.map_mul, h2]; simp
    · rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add β), h3]; simp

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GmLawCharsMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChF
open MvPowerSeries

private lemma gm_hs {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Pt R n d)
    (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero (fun p => h p.1 p.2)

private lemma ev_gm {R : Type} [CommRing R] {n r : ℕ} (a b : Pt R n r)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin r) :
    ev ![a, b] (gmF R r i) = a i + b i + a i * b i := by
  have h := gm_hs (m := 2) ![a, b] (by
    intro j i
    fin_cases j
    · exact ha i
    · exact hb i)
  unfold ev gmF
  rw [subst_add h, subst_add h, subst_mul h, subst_X h, subst_X h]
  rfl

private lemma ev_ch {R : Type} [CommRing R] {n r : ℕ} (a : Pt R n r)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin r) :
    ev ![a] (1 + X ((0 : Fin 1), i) : PS R 1 r) = 1 + a i := by
  have h := gm_hs (m := 1) ![a] (by
    intro j i
    fin_cases j
    exact ha i)
  have h1 := ev_one ![a]
  unfold ev at h1 ⊢
  rw [subst_add h, h1, subst_X h]
  rfl

private lemma gm_const {R : Type} [CommRing R] {r : ℕ} (i : Fin r) :
    constantCoeff (gmF R r i) = 0 := by
  simp [gmF]

private lemma pt_const {R : Type} [CommRing R] {n r : ℕ} (j : Fin n) (i : Fin r) :
    constantCoeff (pt R r j i) = 0 := by
  simp [pt]

private def gmLaw (R : Type) [CommRing R] (r : ℕ) : FGLaw R r where
  F := gmF R r
  const := gm_const
  unit i := by
    rw [ev_gm _ _ (by simp) (pt_const _)]
    simp [pt]
  comm i := by
    rw [ev_gm _ _ (pt_const _) (pt_const _)]
    simp only [pt, gmF]
    ring
  assoc i := by
    have h : ∀ (j k : Fin 3) (l : Fin r), constantCoeff (ev (n := 3) ![pt R r j, pt R r k] (gmF R r l)) = 0 := by
      intro j k l
      rw [ev_gm _ _ (pt_const _) (pt_const _)]
      simp [pt]
    rw [ev_gm _ _ (h _ _) (pt_const _), ev_gm _ _ (pt_const _) (h _ _),
      ev_gm _ _ (pt_const _) (pt_const _), ev_gm _ _ (pt_const _) (pt_const _)]
    ring

private lemma mulF_gm (R : Type) [CommRing R] (r : ℕ) (N : ℕ) :
    ∀ i : Fin r, mulF (gmF R r) N i = (1 + X ((0 : Fin 1), i)) ^ N - 1 := by
  induction N with
  | zero => intro i; simp [mulF]
  | succ N ih =>
    intro i
    simp only [mulF, addOf]
    rw [ev_gm _ _ (by intro l; rw [ih]; simp) (pt_const _), ih]
    simp only [pt]
    ring

theorem gmLaw_chars_mul : ∀ (R : Type) [CommRing R] (r : ℕ), (∃ Gl : FGLaw R r, Gl.F = gmF R r) ∧ (∀ i : Fin r, IsCh (gmF R r) (1 + MvPowerSeries.X ((0 : Fin 1), i)) ∧ dl (1 + MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) = Pi.single i 1) ∧ ∀ (N : ℕ) (i : Fin r), mulF (gmF R r) N i = (1 + MvPowerSeries.X ((0 : Fin 1), i)) ^ N - 1 := by
  intro R _ r
  refine ⟨⟨gmLaw R r, rfl⟩, fun i => ⟨⟨by simp, ?_⟩, ?_⟩, mulF_gm R r⟩
  · have hA : addOf (gmF R r) (pt R (n := 2) r 0) (pt R (n := 2) r 1) = gmF R r := by
      funext l
      unfold addOf
      rw [ev_gm _ _ (pt_const _) (pt_const _)]
      rfl
    rw [hA, ev_ch _ gm_const, ev_ch _ (pt_const _), ev_ch _ (pt_const _)]
    simp only [pt, gmF]
    ring
  · classical
    funext j
    simp only [dl, map_add (f := _), coeff_one, coeff_X, Finsupp.single_eq_zero, one_ne_zero, if_false, zero_add,
      Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), Prod.mk.injEq, true_and, Pi.single_apply]

end GlobalTheory.ChF
end
end

