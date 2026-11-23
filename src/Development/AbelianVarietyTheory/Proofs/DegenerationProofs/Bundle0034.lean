module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.IsoExtend

variable {X Y Y' : Scheme.{0}}

theorem exists_gen_chartPull {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (H : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen A', t.IsGen := by
  obtain ⟨w, hw⟩ := H
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (w.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have val : ∀ i, y ∈ A'.U i → gm (𝟙 Y') y _ (res (a.le i) (pullU h _ (w.s (a.idx i)))) =
      gm h y (A.U (a.idx i)) (w.s (a.idx i)) := fun i hi =>
    (gm_res (𝟙 Y') y (a.le i) hi _).trans ((gm_pull (𝟙 Y') h y _ (a.le i hi) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx i) ⊓ A.U (a.idx j))) (hw (a.idx i) (a.idx j))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    rfl (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val i hy.1)).trans (e'.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2)
    ((gm_res (𝟙 Y') y _ hy _).trans (val j hy.2)))

theorem gm_div_pull (L M : LB X) (f : Y ⟶ X) (y : Y) (J J' : PUnit → M.ι × L.ι) (p q : (PUnit → M.ι) × (PUnit → L.ι))
    (ep : J PUnit.unit = (p.1 PUnit.unit, p.2 PUnit.unit)) (eq : J' PUnit.unit = (q.1 PUnit.unit, q.2 PUnit.unit))
    (hJ : y ∈ ((LB.div M L).pull f).U J) (hJ' : y ∈ ((LB.div M L).pull f).U J')
    (hp : y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2) (hq : y ∈ (M.pull f).U q.1 ⊓ (L.pull f).U q.2) :
    gm (𝟙 Y) y (((LB.div M L).pull f).U J ⊓ ((LB.div M L).pull f).U J') (((LB.div M L).pull f).g J J') =
      gm (𝟙 Y) y ((LB.div (M.pull f) (L.pull f)).U p ⊓ (LB.div (M.pull f) (L.pull f)).U q)
        ((LB.div (M.pull f) (L.pull f)).g p q) := by
  refine (gm_pull_g (LB.div M L) f (𝟙 Y) y J J' hJ hJ').trans ?_
  rw [ep, eq]
  refine (gm_div L M (𝟙 Y ≫ f) y (p.1 PUnit.unit, p.2 PUnit.unit) (q.1 PUnit.unit, q.2 PUnit.unit)
    ⟨⟨mem_pull.1 hp.1, mem_pull.1 hp.2⟩, mem_pull.1 hq.1, mem_pull.1 hq.2⟩).trans (Eq.symm ?_)
  refine (gm_div (L.pull f) (M.pull f) (𝟙 Y) y p q ⟨hp, hq⟩).trans ?_
  exact congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y p.1 q.1 hp.1 hq.1)
    (congrArg (·⁻¹) (gm_pull_g L f (𝟙 Y) y p.2 q.2 hp.2 hq.2))

def chartPullDiv (L M : LB X) (f : Y ⟶ X) :
    ChartPull ((LB.div M L).pull f) (LB.div (M.pull f) (L.pull f)) (𝟙 Y) :=
  have le : ∀ (J : PUnit → M.ι × L.ι) (y : Y), y ∈ ((LB.div M L).pull f).U J →
      y ∈ (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (L.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    have h : f y ∈ M.U (J PUnit.unit).1 ⊓ L.U (J PUnit.unit).2 := (mem_pull (L := LB.div M L) (J := J)).1 hy
    ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => gm_div_pull L M f y J J' (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) rfl rfl hJ hJ' (le J y hJ) (le J' y hJ') }

def chartDivPull (L M : LB X) (f : Y ⟶ X) :
    ChartPull (LB.div (M.pull f) (L.pull f)) ((LB.div M L).pull f) (𝟙 Y) :=
  have le : ∀ (p : (PUnit → M.ι) × (PUnit → L.ι)) (y : Y), y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2 →
      y ∈ ((LB.div M L).pull f).U (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit)) := fun p y hy =>
    (mem_pull (L := LB.div M L) (J := fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))).2
      ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  { idx := fun p _ => (p.1 PUnit.unit, p.2 PUnit.unit)
    le := le
    g := fun y p q hp hq => (gm_div_pull L M f y (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))
      (fun _ => (q.1 PUnit.unit, q.2 PUnit.unit)) p q rfl rfl (le p y hp) (le q y hq) hp hq).symm }

theorem lbIso_pull_iff_gen (L M : LB X) (f : Y ⟶ X) :
    LBIso (L.pull f) (M.pull f) ↔ ∃ t : LB.Gen ((LB.div M L).pull f), t.IsGen :=
  ⟨exists_gen_chartPull (chartPullDiv L M f), exists_gen_chartPull (chartDivPull L M f)⟩

theorem exists_gen_of_chart {D : LB X} (hD : D.IsLB) (f : Y ⟶ X) (i : D.ι) (hf : ∀ y, f y ∈ D.U i) :
    ∃ t : LB.Gen (D.pull f), t.IsGen := by
  have le : ∀ J : PUnit → D.ι, (D.pull f).U J ≤ f ⁻¹ᵁ (D.U (J PUnit.unit) ⊓ D.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (D.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J, y ∈ (D.pull f).U J → gm (𝟙 Y) y _ (res (le J) (pullU f _ (D.g (J PUnit.unit) i))) =
      gm (𝟙 Y ≫ f) y _ (D.g (J PUnit.unit) i) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g D f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))).trans ?_
  exact gm_cocycle hD (𝟙 Y ≫ f) y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (hf y)

theorem exists_gen_of_diff {D : LB X} (hD : D.IsLB) (σ : X ⟶ X)
    (c : LB.Gen (LB.LinComb D ![𝟙 X, σ] ![1, -1])) (hc : c.IsGen) (r : Y ⟶ X) {B : Scheme.{0}} (q : Y ⟶ B)
    (τ : B ⟶ X) (hr : r ≫ σ = q ≫ τ) (H : ∃ t : LB.Gen (D.pull τ), t.IsGen) :
    ∃ t : LB.Gen (D.pull r), t.IsGen := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨u, hu, -⟩ := exists_gen hD (φ' := fun _ : PUnit => r) (ε' := fun _ => 1) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, hr])
    (LB.mulGen D _ _ _ _ (LB.pullGen D _ _ c r) (LB.pullGen D _ _ t q))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ c hc r) (DVR.pullGen_isGen _ _ _ t ht q))
  exact ⟨u, hu⟩

theorem exists_gen_diff (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H)
    (pU : HU ⟶ U) (hp : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (sq : IsPullback jH pU p j)
    {D : LB H} (hD : D.IsLB) (H₀ : ∃ t : LB.Gen (D.pull jH), t.IsGen) :
    ∃ c : LB.Gen (LB.LinComb D ![𝟙 H, p ≫ e] ![1, -1]), c.IsGen := by
  obtain ⟨t, ht⟩ := H₀
  let eU : U ⟶ HU := sq.lift (j ≫ e) (𝟙 U) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : eU ≫ jH = j ≫ e := sq.lift_fst _ _ _
  have h₂ : eU ≫ pU = 𝟙 U := sq.lift_snd _ _ _
  have h₃ : jH ≫ p ≫ e = (pU ≫ eU) ≫ jH := by rw [Category.assoc, h₁, sq.w_assoc]
  obtain ⟨t', ht', vt⟩ := exists_gen hD (φ' := fun i => jH ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, h₃])
    (LB.mulGen D _ _ _ _ t (LB.invGen D _ _ (LB.pullGen D _ _ t (pU ≫ eU))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ t ht _)))
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen hD (φ' := fun i => e ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fin.prod_univ_two, reassoc_of% he])
    (LB.oneGen D) (LB.isGen_oneGen D)
  obtain ⟨c, ⟨hc, -⟩, -⟩ := GlobalTheory.GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hp hg he sq h₁ D hD (Fin 2) _ _ t' ρ ht' hρ
    (corr_of_val hD fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, vt _ _ _ _ hJ, vρ _ _ _ _ hJ, val_mul hJ, val_inv, val_pull hJ, val_one,
        Category.id_comp, reassoc_of% h₂, mul_inv_cancel])
  exact ⟨c, hc⟩

end GlobalTheory.IsoExtend


open GlobalTheory.IsoExtend in
theorem GlobalTheory.lbIso_extend_of_normal : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → ∀ (L M : LB H), L.IsLB → M.IsLB → LBIso (L.pull jH) (M.pull jH) → (LBIso (L.pull e) (M.pull e) → LBIso L M) ∧ ∀ s : S, ∃ N : S.Opens, s ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι) := by
  intro S _ _ hS U H HU _ j _ p e jH pU hp hg he sq L M hL hM h
  have hD : (LB.div M L).IsLB := LB.isLB_div hM hL
  obtain ⟨c, hc⟩ := exists_gen_diff S hS U H HU j p e jH pU hp hg he sq hD ((lbIso_pull_iff_gen L M jH).1 h)
  refine ⟨fun h' => ?_, fun s => ?_⟩
  · exact exists_gen_chartPull (chartPullUnpull (LB.div M L) (𝟙 H) rfl)
      (exists_gen_of_diff hD _ c hc (𝟙 H) p e (Category.id_comp _) ((lbIso_pull_iff_gen L M e).1 h'))
  · obtain ⟨i, hi⟩ := exists_chart hD (e s)
    refine ⟨e ⁻¹ᵁ (LB.div M L).U i, hi, (lbIso_pull_iff_gen L M _).2 ?_⟩
    exact exists_gen_of_diff hD _ c hc _ (𝟙 _) _ (Category.id_comp _).symm
      (exists_gen_of_chart hD _ i fun y => y.2)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulEqZeroOfAppEqZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.SquareZero


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
open TopologicalSpace in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.SquareZero.mul_eq_zero_of_app_eq_zero : ∀ (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X X' : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (β : X' ⟶ X),
    IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : X.Opens) (x y : Γ(X, W)),
    (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0 := by
  intro A A' _ _ g hg hsq X X' f f' β hpb W x y hx hy
  apply TopCat.Presheaf.section_ext X.sheaf W (x * y) 0
  intro p hp
  obtain ⟨V, hVaff, hpV, hVW⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hp
  have hres : ∀ z : Γ(X, W), (β.app W).hom z = 0 →
      _root_.GlobalTheory.AbLaw.rs X hVW z ∈
        Ideal.map (_root_.GlobalTheory.SmallExtLift.cst f V) (RingHom.ker g) := fun z hz =>
    _root_.GlobalTheory.SmallExtLift.mem_of_app_eq_zero hg hpb hVaff _
      (by rw [_root_.GlobalTheory.SectionKernel.app_rs, hz, map_zero])
  have hzero : _root_.GlobalTheory.AbLaw.rs X hVW (x * y) = 0 := by
    rw [map_mul]
    have hmem := Ideal.mul_mem_mul (hres x hx) (hres y hy)
    rw [← Ideal.map_mul, ← pow_two, hsq, Ideal.map_bot, Ideal.mem_bot] at hmem
    exact hmem
  have h1 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV (x * y)
  have h2 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVW) p hpV 0
  change X.presheaf.germ W p hp (x * y) = X.presheaf.germ W p hp 0
  rw [← h1, ← h2, map_zero]
  exact congrArg _ hzero

end GlobalTheory.SquareZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormRepGeneratorsAndThetaSeriesTerm
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem norm_cubN (h : N.Int q) (k : ℕ) (a b x : N.A) : ‖((cubN N.θ k a b x : Cˣ) : C)‖ = 1 := by
  rw [cubN, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun i _ => h.θ _ _ _

theorem norm_dbl (h : N.Int q) (x : N.A) : ‖((dbl N.θ N.σ x : Cˣ) : C)‖ = 1 := by
  rw [dbl, Units.val_div_eq_div_val, norm_div, h.θ, h.σ, div_one]

theorem norm_mulq (h : N.Int q) (n : ℕ) (x : N.A) : ‖((mulq N.θ N.σ n x : Cˣ) : C)‖ = 1 := by
  rw [mulq, Units.coe_prod, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Units.val_div_eq_div_val, norm_div, h.norm_cubN, Units.val_pow_eq_pow_val, norm_pow, h.norm_dbl,
    one_pow, div_one]

theorem norm_τ (h : N.Int q) (a b : N.X) : ‖(N.τ a b : C)‖ = Real.exp (-QuadraticMap.polar q a b) := by
  rw [NumD.τ, Units.val_div_eq_div_val, Units.val_div_eq_div_val, norm_div, norm_div, h.ψ, h.ψ, h.ψ,
    ← Real.exp_sub, ← Real.exp_sub, QuadraticMap.polar]
  congr 1
  ring

theorem norm_pow_generators_eq_pow (h : N.Int q) (g : N.Gt) (k : ℕ) (χ : N.X) :
    ‖((g ^ k).s χ : C)‖ = ‖(g.s χ : C)‖ ^ k := by
  have := congrArg (fun u : Cˣ => ‖(u : C)‖) (g.pow_s k χ)
  simpa only [Units.val_mul, norm_mul, h.norm_cubN, mul_one, Units.val_pow_eq_pow_val, norm_pow] using this

theorem norm_rep_generators_eq_exp (h : N.Int q) {k : ℕ} (p : N.QT k) (hk : k ≠ 0) (χ : N.X) :
    ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k)) := by
  have e := h.norm_pow_generators_eq_pow p.1.2 k χ
  rw [N.mem_QT.1 p.2, NumD.io_s, h.norm_τ] at e
  refine (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le hk).1 ?_
  rw [← e, ← Real.exp_nat_mul]
  congr 1
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  field_simp

theorem norm_wQ (h : N.Int q) {k : ℕ} (hk : Odd k) (p : N.QT k) :
    ‖(N.wQ p : C)‖ = Real.exp (-(q p.1.1.toAdd / k)) := by
  have hk0 : k ≠ 0 := hk.pos.ne'
  rw [NumD.wQ, NumB.wS]
  simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val, norm_div, norm_mul, norm_pow,
    h.norm_cubN, h.norm_dbl, h.norm_mulq, h.ψ, h.norm_rep_generators_eq_exp p hk0, mul_one, one_pow, div_one]
  rw [← Real.exp_nat_mul, ← Real.exp_sub, QuadraticMap.polar_self]
  congr 1
  obtain ⟨j, rfl⟩ := hk
  have e : (2 * j + 1 - 1) / 2 = j := by omega
  have : ((2 * j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  rw [e, two_smul]
  field_simp
  push_cast
  ring

theorem norm_txT (h : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  rw [NumD.txT, NumD.vt]
  simp only [Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul, h.norm_mulq, h.ψ,
    h.norm_wQ hm.pow, h.norm_pow_generators_eq_pow, h.norm_rep_generators_eq_exp p (pow_ne_zero 2 hm0), div_one, NumD.Gt.pow_b]
  rw [← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  have e : q (p.1.1.toAdd + m • χ) =
      q p.1.1.toAdd + (m : ℝ) ^ 2 * q χ + m * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (m • χ) = m * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (m • χ) = (m : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm0
  rw [e]
  push_cast
  field_simp
  ring

end GlobalTheory.Ex.NumD.Int

namespace GlobalTheory.Ex

theorem norm_QT_s_and_norm_txT : ∀ (C : Type) [NormedField C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → (∀ (k : ℕ) (p : N.QT k), k ≠ 0 → ∀ χ, ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k))) ∧ ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) χ, ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ :=
  fun _ _ _ _ h => ⟨fun _ p hk χ => h.norm_rep_generators_eq_exp p hk χ, fun _ hm p χ => h.norm_txT hm p χ⟩
end GlobalTheory.Ex
end

