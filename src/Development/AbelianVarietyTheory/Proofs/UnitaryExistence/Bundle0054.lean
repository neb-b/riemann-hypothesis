module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjIsAbelianSchemeDimRigidifiedSym
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ObjDim

open ReciprocityTheory.ChartRestriction.G.Chart (sp JetR zR IsUnivChart jetLift jetLift_zR jet_ext jetAug_zR tmap tvec eigLat)

theorem exists_isUnivChart {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin g) m) ⟶ G, IsUnivChart G g x := by
  obtain ⟨X, h0, hnat, hinj, hsurj⟩ := NilCoord.nilpotent_coordinates G g hG
  have nil : ∀ {A : Type} [CommRing A] (J : Ideal A) (m : ℕ), J ^ (m + 1) = ⊥ → ∀ a ∈ J, IsNilpotent a :=
    fun J m hJ a ha => ⟨m + 1, by
      have := Ideal.pow_mem_pow ha (m + 1)
      rwa [hJ, Ideal.mem_bot] at this⟩
  have hz : ∀ m (i : Fin g), IsNilpotent (ReciprocityTheory.ChartRestriction.G.Chart.zR (R := R) m i) := fun m i =>
    nil _ m (Chart.ker_jetAug_pow (Fin g) m) _ (Chart.zR_mem_ker m i)
  refine ⟨fun m => X _ (ReciprocityTheory.ChartRestriction.G.Chart.zR m), fun m => hnat _ _ _ _ (hz _), fun m => ?_, fun A _ _ aug m hJ y hy => ?_⟩
  · rw [hnat _ _ _ _ (hz _), ← h0]
    congr 1
    funext i
    have h := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := R) 0 i) (0 + 1)
    rw [Chart.ker_jetAug_pow, Ideal.mem_bot] at h
    exact (pow_one _).symm.trans h
  · obtain ⟨a, ha, rfl⟩ := hsurj A R aug (fun r => ⟨algebraMap R A r, aug.commutes r⟩) (nil _ m hJ) y hy
    refine ⟨jetLift R _ hJ a ha, ⟨jet_ext fun j => ?_, ?_⟩, fun ψ hψ => jet_ext fun j => ?_⟩
    · rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact ha j
    · rw [hnat _ _ _ _ (hz _)]
      simp only [jetLift_zR]
    · rw [jetLift_zR]
      have h := hψ.2
      rw [hnat _ _ _ _ (hz _)] at h
      exact (congrFun (hinj A _ _ (fun i => nil _ m hJ _ (ha i)) (fun i => (hz m i).map ψ) h) j).symm

def tanAct {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) {O : Type} [CommRing O]
    (act : OAct O G) : O →+* Module.End R (Fin n → R) :=
  haveI := act.hom
  RingHom.mk'
    { toFun := fun a => tmap hx (act.act a)
      map_one' := LinearMap.ext fun c => Chart.tvec_inj hx (by
        rw [Chart.tvec_tmap, act.one, Category.comp_id]; rfl)
      map_mul' := fun a b => LinearMap.ext fun c => Chart.tvec_inj hx (by
        rw [Module.End.mul_apply, Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, mul_comm, act.mul,
          Category.assoc]) }
    fun a b => LinearMap.ext fun c => Chart.tvec_inj hx (by
      show tvec (tmap hx (act.act (a + b)) c) = tvec (tmap hx (act.act a) c + tmap hx (act.act b) c)
      rw [Chart.tvec_add hx, Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, act.add, MonObj.comp_mul])

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul]
  simp [j]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_eq_of_eigen (H : Host E) {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {N : Type} [AddCommGroup N]
    [Module k N] [Module.Finite k N] (act : 𝓞 E →+* Module.End k N) (ρ : k) (hρ : ρ ^ 2 = -(H.d : k)) (p q : ℕ)
    (h : ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → Module.finrank k (EigenSplit.eigenSub act τ) = p) ∧
      (τ H.rt ≠ ρ → Module.finrank k (EigenSplit.eigenSub act τ) = q)) :
    Module.finrank k N = Module.finrank ℚ E / 2 * (p + q) := by
  classical
  let σ : (E →+* k) → (𝓞 E →+* k) := fun φ => φ.comp (algebraMap (𝓞 E) E)
  have hc := NumberField.Embeddings.card E k
  obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) hc
  have hs : EigenSplit.IsSplitting σ :=
    EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  have h1 : Module.finrank k N = ∑ φ, Module.finrank k (EigenSplit.eigenSub act (σ φ)) := by
    rw [(EigenSplit.eigenEquiv hs act).finrank_eq, Module.finrank_pi_fintype]
  let c : (E →+* k) → (E →+* k) := fun φ => φ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hcc : Function.Involutive c := fun φ => RingHom.ext fun a => by
    simp [c]
  have hrt : ∀ φ, σ (c φ) H.rt = -σ φ H.rt := fun φ => by
    rw [← map_neg, ← HostModel.bar_rt]
    exact congrArg φ (H.bar_eq H.rt).symm
  have hd : (H.d : k) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have h2 : ∀ φ, Module.finrank k (EigenSplit.eigenSub act (σ φ)) +
      Module.finrank k (EigenSplit.eigenSub act (σ (c φ))) = p + q := fun φ => by
    have hsq : σ φ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast, hρ]
    have hne : -ρ ≠ ρ := fun e => hd (by
      have : ρ = 0 := by linear_combination (-1 / 2 : k) * e
      rw [this] at hρ
      simpa using hρ)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with e | e
    · rw [(h _).1 e, (h _).2 (by rw [hrt, e]; exact hne)]
    · rw [(h _).2 (by rw [e]; exact hne), (h _).1 (by rw [hrt, e, neg_neg]), add_comm]
  have h3 : 2 * Module.finrank k N = Module.finrank ℚ E * (p + q) := by
    have := Equiv.sum_comp hcc.toPerm fun φ => Module.finrank k (EigenSplit.eigenSub act (σ φ))
    rw [two_mul, h1]
    conv_lhs => arg 2; rw [← this]
    rw [← Finset.sum_add_distrib, ← hc]
    exact (Finset.sum_congr rfl fun φ _ => h2 φ).trans (by simp)
  rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
    Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h3 ⊢
  rw [Nat.mul_div_cancel _ two_pos]
  linarith

variable {H : Host E} {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
  {s : S ⟶ Sp B}

theorem dim_geometric_fibre (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) {d : ℕ}
    (hd : SmoothOfRelativeDimension d ((Over.pullback x).obj o.t.G).hom) :
    d = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  let β : B →+* k := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have : CharZero k := ⟨fun n m e => by
    have := CharP.exists k
    obtain ⟨r, hr⟩ := this
    have hr0 : r = 0 := by
      by_contra h
      have := (b.unit r (Nat.pos_of_ne_zero h)).map β
      rw [map_natCast, CharP.cast_eq_zero] at this
      exact not_isUnit_zero this
    subst hr0
    have := CharP.charP_to_charZero k
    exact Nat.cast_injective e⟩
  obtain ⟨hdet, -⟩ := o.geom k x β hβ
  have := o.t.semi.comm
  have : IsCommMonObj ((Over.pullback x).obj o.t.G) := inferInstance
  obtain ⟨z, hz⟩ := exists_isUnivChart ((Over.pullback x).obj o.t.G) d hd
  let act := OAct.pullback x o.t.G o.t.act
  have := act.hom
  have key : ∀ (τ : 𝓞 E →+* k) N, LieMult o.t.act x τ N →
      Module.finrank k (EigenSplit.eigenSub (tanAct hz act) τ) = N := fun τ N hL => by
    have e : EigenSplit.eigenSub (tanAct hz act) τ = eigLat hz act.act fun a => τ a := by
      ext c
      rw [EigenSplit.mem_eigenSub, Chart.mem_eigLat_iff]
      rfl
    rw [e]
    exact Chart.finrank_of_lieMult (isGrpPullback_id o.t.G) (Category.comp_id x) hz o.t.act o.t.act.act
      (fun a => by simp) act.act (fun a => rfl) τ hL
  have := finrank_eq_of_eigen H (tanAct hz act) (β b.ρ) (by rw [← map_pow, b.ρ_sq, map_neg, map_natCast]) D.p D.q
    fun τ => ⟨fun h => key τ _ ((hdet τ).1 h), fun h => key τ _ ((hdet τ).2 h)⟩
  simpa using this

theorem smoothOfRelativeDimension (o : Obj D l b s) :
    SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom := by
  have := o.t.semi.smooth
  have := o.t.semi.geomConnected
  choose n W hW hd using H1.exists_dim o.t.G.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q))) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := S.residueField (o.t.G.hom y)
  let k := AlgebraicClosure κ
  let x : Sp k ⟶ S := spMap (algebraMap κ k) ≫ S.fromSpecResidueField (o.t.G.hom y)
  have hp := (isGrpPullback_pullback o.t.G x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum k)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have : Smooth ((Over.pullback x).obj o.t.G).hom := by
    change Smooth (pullback.snd o.t.G.hom x)
    infer_instance
  have : ConnectedSpace ((Over.pullback x).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := o.t.G.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj o.t.G).hom y'
  rw [← dim_geometric_fibre o x hd', ← H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)]
  exact hd y

end GlobalTheory.ObjDim

namespace GlobalTheory

theorem obj_isAbelianScheme_dim_rigidified_sym :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type)
      [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧
      SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧
      Out.Sym o.t.G o.t.PP.L := by
  intro E _ _ _ H D l B _ b S s o
  obtain ⟨-, ws, gs', -⟩ := o.t.sym
  exact ⟨⟨inferInstance, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩, ObjDim.smoothOfRelativeDimension o,
    ⟨o.t.PP.rig, o.t.PP.rigGen⟩, fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩⟩

def objPolAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {B : Type}
    [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) : Out.PolAV S where
  A := o.t.G
  isAb := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).1
  g := Module.finrank ℚ E / 2 * (D.p + D.q)
  smoothDim := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).2.1
  L := o.t.PP.L
  isLB := o.t.PP.isLB
  rigid := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).2.2.1
  sym := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).2.2.2
  ample := o.ample
  ktriv := o.ktriv

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniformizationPeriodLatticeChange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.FamRigid

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct])
    (fun a b w => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c a w => by simp [hermForm, Matrix.mulVec_smul, dotProduct_smul])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (hermForm Hm z w).im := rfl

theorem re_eq_imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (hermForm Hm z w).re = imForm Hm (Complex.I • z) w := by
  simp [imForm_apply, hermForm, smul_dotProduct]

theorem isBounded_sublevel {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (c : ℝ) :
    Bornology.IsBounded {z : Fin g → ℂ | (hermForm Hm z z).re ≤ c} := by
  have hc : Continuous fun z : Fin g → ℂ => (hermForm Hm z z).re := by
    unfold hermForm
    refine Complex.continuous_re.comp ?_
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨m, hm, hle⟩ := (isCompact_sphere (0 : Fin g → ℂ) 1).exists_forall_le' hc.continuousOn
    (a := 0) (fun b hb => hp b (by rintro rfl; simp at hb))
  refine (Metric.isBounded_closedBall (x := (0 : Fin g → ℂ)) (r := 1 + c / m)).subset ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  rw [mem_closedBall_zero_iff]
  by_cases h0 : z = 0
  · subst h0
    have : 0 ≤ c := by simpa [hermForm] using hz
    have := div_nonneg this hm.le
    simp only [norm_zero]
    linarith
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 h0
    have h1 := hle ((‖z‖⁻¹ : ℝ) • z) (by simp [norm_smul, hn.ne'])
    have h2 : (hermForm Hm ((‖z‖⁻¹ : ℝ) • z) ((‖z‖⁻¹ : ℝ) • z)).re =
        ‖z‖⁻¹ * ‖z‖⁻¹ * (hermForm Hm z z).re := by
      rw [re_eq_imForm, re_eq_imForm, smul_comm, map_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul, smul_eq_mul, _root_.mul_assoc]
    rw [h2] at h1
    have h3 : m * (‖z‖ * ‖z‖) ≤ c := by
      have := mul_le_mul_of_nonneg_right h1 (mul_pos hn hn).le
      refine this.trans (le_trans (le_of_eq ?_) hz)
      field_simp
    have h4 : ‖z‖ * ‖z‖ ≤ c / m := by
      rw [le_div_iff₀ hm]; linarith
    nlinarith

theorem finite_order {g : ℕ} {L : Type} [AddCommGroup L] [Module.Finite ℤ L] (P : L →+ (Fin g → ℂ))
    (hinj : Function.Injective P) (hd : DiscreteTopology P.range)
    (hsp : Submodule.span ℝ (Set.range P) = ⊤) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) (δ : L ≃ₗ[ℤ] L)
    (k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ a, P (δ a) = k (P a))
    (hiso : ∀ a b, (hermForm Hm (P (δ a)) (P (δ b))).im = (hermForm Hm (P a) (P b)).im) :
    ∃ n, 0 < n ∧ δ ^ n = 1 := by
  have hB : (imForm Hm).compl₁₂ (k.restrictScalars ℝ) (k.restrictScalars ℝ) = imForm Hm := by
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨a, rfl⟩
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.compl₁₂_apply, LinearMap.restrictScalars_apply, ← hk, imForm_apply, hiso]
  have hQ : ∀ a, (hermForm Hm (P (δ a)) (P (δ a))).re = (hermForm Hm (P a) (P a)).re := by
    intro a
    rw [re_eq_imForm, re_eq_imForm, hk, ← map_smul]
    conv_rhs => rw [← hB]
    rfl
  have hQn : ∀ (n : ℕ) a, (hermForm Hm (P ((δ ^ n) a)) (P ((δ ^ n) a))).re =
      (hermForm Hm (P a) (P a)).re := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih => intro a; rw [pow_succ', LinearEquiv.mul_apply, hQ, ih]
  have hper : ∀ a, ∃ n, 0 < n ∧ (δ ^ n) a = a := by
    intro a
    have hfin := Metric.finite_isBounded_inter_isClosed (s := (P.range : Set (Fin g → ℂ)))
      DiscreteTopology.isDiscrete (isBounded_sublevel Hm hp (hermForm Hm (P a) (P a)).re)
      AddSubgroup.isClosed_of_discrete
    obtain ⟨m, n, hmn, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
      (f := fun n : ℕ => P ((δ ^ n) a)) (t := _ ∩ (P.range : Set (Fin g → ℂ))) (fun n => Set.mem_inter
        (show P ((δ ^ n) a) ∈ {z : Fin g → ℂ | (hermForm Hm z z).re ≤ (hermForm Hm (P a) (P a)).re}
          from (hQn n a).le) ⟨_, rfl⟩) hfin
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    refine ⟨d + 1, Nat.succ_pos _, ?_⟩
    have := hinj he
    rw [add_assoc, pow_add, LinearEquiv.mul_apply] at this
    exact ((δ ^ m).injective this).symm
  choose N hN hNa using hper
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := L)
  refine ⟨∏ a ∈ S, N a, Finset.prod_pos fun a _ => hN a, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on hS ?_
  intro a ha
  obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem N (Finset.mem_coe.1 ha)
  rw [hd]
  change (δ ^ (N a * d)) a = a
  clear hd
  induction d with
  | zero => rfl
  | succ d ih => rw [Nat.mul_succ, pow_add, LinearEquiv.mul_apply, hNa, ih]

theorem ex_eq_of_level_group : (∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n → σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P P' : (U.Di i).La →+ (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di i).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsPeriod (U.Di i) ty P → IsPeriod (U.Di i) ty P' → (∀ a b, (U.Di i).EF (gam a) (gam b) = (U.Di i).EF a b) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La), ∃ e, gam a = a + l.M • e) → (∀ a, ∃ e, gam a = a + l.A • e) → (∀ a, P' (gam a) = h₀ *ᵥ P a) → IsUnit h₀.det ∧ U.u i P = U.u i P' ∧ ∀ z, (U.ex i P' (h₀ *ᵥ z)).left = (U.ex i P z).left := by
  intro hMink E _ _ _ H D l Xo σ g ty U i P P' gam h₀ hP hP' hiso hM hA hh
  have hsurj : Function.Surjective h₀.mulVec := by
    have : LinearMap.range (h₀.mulVecLin.restrictScalars ℝ) = ⊤ := by
      rw [eq_top_iff, ← hP'.2.2.2.1, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact ⟨P (gam.symm a), by simp [← hh]⟩
    exact LinearMap.range_eq_top.1 this
  have hu : IsUnit h₀ := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hpt : U.u i P = U.u i P' := (U.fibre i P P' hP hP').2
    ⟨gam, LinearEquiv.ofBijective h₀.mulVecLin ⟨Matrix.mulVec_injective_iff_isUnit.2 hu, hsurj⟩,
      hiso, hM, hA, hh⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 hu, hpt, ?_⟩
  obtain ⟨h₁, gam₁, hex, hh₁, hiso₁, hM₁, -⟩ :=
    _root_.GlobalTheory.familyUnif_exp_unique E H D l Xo σ g ty U i i P P' hP hP' hpt
  have hM₁' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (U.Di i).La),
      ∃ e, gam₁ a = a + l.M • e := by
    intro a ha
    refine Submodule.smul_induction_on ha ?_ ?_
    · intro v hv b _
      obtain ⟨c, e, rfl⟩ := U.t_surj i b
      obtain ⟨e₁, he₁⟩ := hM₁ (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
      obtain ⟨r, hr⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      refine ⟨e₁ + r • (gam₁ (v • e) - v • e), ?_⟩
      rw [smul_add, ← map_smul, smul_comm v, map_add (f := _), he₁, map_nsmul, hr, smul_add, smul_smul,
        smul_sub]
      abel
    · rintro x y ⟨e, he⟩ ⟨e', he'⟩
      exact ⟨e + e', by rw [map_add (f := _), he, he', smul_add]; abel⟩
  have f₀ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hM
  have f₁ := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam₁ hiso₁ hM₁'
  haveI := (U.Di i).fin
  haveI : Module.Finite ℤ (U.Di i).La := Module.Finite.trans (𝓞 E) _
  obtain ⟨-, hinj, hd, hsp, Hm, -, hp, hE⟩ := hP'
  haveI : Module.IsTorsionFree ℤ (U.Di i).La :=
    Function.Injective.moduleIsTorsionFree P' hinj (fun r x => map_zsmul P' r x)
  haveI : Module.Free ℤ (U.Di i).La := Module.free_of_finite_type_torsion_free'
  let δ : (U.Di i).La ≃ₗ[ℤ] (U.Di i).La := (gam₁.symm.trans gam).toAddEquiv.toIntLinearEquiv
  have hδ : ∀ a, δ a = gam (gam₁.symm a) := fun a => rfl
  obtain ⟨n, hn, hδn⟩ := finite_order P' hinj hd hsp Hm hp δ
    (h₀.mulVecLin ∘ₗ h₁.symm.toLinearMap)
    (fun a => by
      have := hh₁ (gam₁.symm a)
      rw [gam₁.apply_symm_apply] at this
      rw [hδ, hh, this]
      simp)
    (fun a b => by
      rw [hE, hE, hδ, hδ, hiso, ← hiso₁, gam₁.apply_symm_apply, gam₁.apply_symm_apply])
  have hδ1 := hMink _ δ n l.M hn hδn l.three_le (fun y => by
    obtain ⟨e, he⟩ := f₀ (gam₁.symm y)
    obtain ⟨e', he'⟩ := f₁ (gam₁.symm y)
    rw [gam₁.apply_symm_apply] at he'
    refine ⟨e - e', ?_⟩
    rw [hδ, he, smul_sub]
    conv_rhs => rw [he']
    abel)
  have hg : ∀ a, gam a = gam₁ a := fun a => by
    have := hδ (gam₁ a)
    rw [hδ1, gam₁.symm_apply_apply] at this
    exact this.symm
  have hlin : h₀.mulVecLin.restrictScalars ℝ = h₁.toLinearMap.restrictScalars ℝ := by
    refine LinearMap.ext_on hP.2.2.2.1 ?_
    rintro _ ⟨a, rfl⟩
    change h₀ *ᵥ P a = h₁ (P a)
    rw [← hh, ← hh₁, hg]
  intro z
  have : h₀ *ᵥ z = h₁ z := LinearMap.congr_fun hlin z
  rw [this, hex]

end GlobalTheory.FamRigid
end

