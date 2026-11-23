module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0128
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0164
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDiffUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeLinearEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique

theorem dim_eq_of_smooth {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g d : ℕ} (u : HolUnif A L g)
    (hs : SmoothOfRelativeDimension d A.hom) : g = d :=
  _root_.GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension A L g d u hs

theorem isDiff_unique_off {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (hs : SmoothOfRelativeDimension g A.hom) (hc : ConnectedSpace A.left) {v : epsR ℂ ⟶ A} (hv : ¬ IsTangent v)
    {w w' : Fin g → ℂ} (h : u.IsDiff w v) (h' : u.IsDiff w' v) : w = w' :=
  _root_.GlobalTheory.CompanionTheory.Ggeo.DualFibre.eq_of_isDiff_of_not_isTangent A L g u hs hc v hv w w' h h'


open TangentOrigin in
theorem exists_linear_of_smooth {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
    (hs : SmoothOfRelativeDimension g A.hom) (u₀ u : HolUnif A L g) :
    ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u₀.ex z := by
  obtain ⟨h₁, h₂⟩ := TorusTransfer.tangent_bijective u hs
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  let ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (u.ex z)) u.ex_add
  let G' : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (u₀.ex z)) u₀.ex_add
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q ↦
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ := Set.ext fun z ↦ u.ker z
  have key : ∃! F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, ex (F z) = G' z := by
   refine existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto
    (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(A.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    ?_ ?_ (u.hol U 0).1 (u₀.hol U 0).1 (fun s ↦ (u.hol U s).2) (fun s ↦ (u₀.hol U s).2) ?_
   · rw [← map_zero ex]
     exact h0
   · intro a ha b hb h
     refine Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
       (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦ ?_))
     exact (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))
   · intro w hw
     obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
     have hvU := (tangent_mem_iff (u := u) hv U).2 h0
     refine (h₁ v hv).unique hd ((isDiff_iff hv hU hvU h0 0).2 ?_)
     rw [(isDiff_iff hv hU hvU h0 w).1 hd]
     refine RingHom.ext fun s ↦ TrivSqZeroExt.ext rfl ?_
     rw [jet_snd, jet_snd, map_zero]
     exact hw s
  obtain ⟨F, hF, -⟩ := key
  exact ⟨F, hF⟩


open GlobalTheory.OrthoMetric in
theorem exists_transport {X : Scheme.{0}} {G : Over X} [GrpObj G] {y : Sp ℂ ⟶ X} {A A' : Over (Sp ℂ)} [GrpObj A]
    [GrpObj A'] {φ : A.left ⟶ G.left} {φ' : A'.left ⟶ G.left} (hp : IsGrpPullback A G y φ)
    (hp' : IsGrpPullback A' G y φ') {L : LB G.left} {g : ℕ} (u' : HolUnif A' (L.pull φ') g) :
    ∃ u : HolUnif A (L.pull φ) g, (∀ z, (u.ex z).left ≫ φ = (u'.ex z).left ≫ φ') ∧ (∀ z, z ∈ u.Λ ↔ z ∈ u'.Λ) ∧
      ∀ (j : L.ι) z, u.fr (fun _ => j) z = u'.fr (fun _ => j) z := by
  let e : (Fin g → ℂ) → (Over.mk y ⟶ G) := fun z => Function.surjInv (liftPt_surjective hp') (u'.ex z)
  have he : ∀ z, liftPt hp' (e z) = u'.ex z := fun z => Function.surjInv_eq _ _
  have hel : ∀ z, (e z).left = (u'.ex z).left ≫ φ' := fun z => by
    rw [← he, liftPt_comp]
  have hpre : ∀ z (V : G.left.Opens), ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (φ' ⁻¹ᵁ V) ↔ ⊤ ≤ (e z).left ⁻¹ᵁ V := fun z V => by
    rw [hel]
    exact (GlobalTheory.top_le_preimage_comp _ _ _).symm
  have hj : ∀ (j : L.ι) z, ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull φ').U (fun _ => j) ↔ ⊤ ≤ (e z).left ⁻¹ᵁ L.U j :=
    fun j z => by
      rw [← he z]
      exact lift_le hp' (e z) (fun _ => j)
  refine ⟨fibreUnif hp e u'.Λ.toAddSubgroup (fun j => u'.fr (fun _ => j)) ?_ ?_ ?_ u'.discrete u'.full ?_ ?_ ?_ ?_,
    fun z => liftPt_comp hp _ |>.trans (hel z), fun z => Iff.rfl, fun j z => rfl⟩
  · intro z w
    refine liftPt_injective hp' ?_
    rw [liftPt_mul, he, he, he, u'.ex_add]
  · intro p
    obtain ⟨z, hz⟩ := u'.ex_onto (liftPt hp' p)
    exact ⟨z, liftPt_injective hp' ((he z).trans hz)⟩
  · intro z
    have h1 : e z = 1 ↔ u'.ex z = 1 := by
      rw [← he z, ← liftPt_one hp']
      exact (liftPt_injective hp').eq_iff.symm
    exact h1.trans (u'.ker z)
  · intro V f
    have h := u'.hol (φ' ⁻¹ᵁ V) ((φ'.app V).hom f)
    have es : {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e b).left ⁻¹ᵁ V} = {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (φ' ⁻¹ᵁ V)} :=
      Set.ext fun z => ⟨fun h => (hpre z V).2 h.2, fun h => ⟨trivial, (hpre z V).1 h⟩⟩
    rw [es]
    refine ⟨h.1, h.2.congr fun z _ => ?_⟩
    show valAt' (e z).left V f = _
    rw [hel]
    exact (GlobalTheory.valAt'_comp _ _ _ _).symm
  · intro j
    have es : {z | ⊤ ≤ (e z).left ⁻¹ᵁ L.U j} = {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.pull φ').U (fun _ => j)} :=
      Set.ext fun z => (hj j z).symm
    rw [es]
    exact u'.fr_hol _
  · intro j z hz
    exact u'.fr_ne _ z ((hj j z).2 hz)
  · intro j j' z hz
    obtain ⟨h1, h2⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hz
    have hz' := (GlobalTheory.top_le_preimage_inf (u'.ex z).left _ _).2 ⟨(hj j z).2 h1, (hj j' z).2 h2⟩
    rw [u'.fr_compat _ _ z hz', GlobalTheory.ArchMetricCompare.val_pull_g L _ _ _ _ hz', hel]

theorem isDiff_of_comp {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g : ℕ}
    (u : HolUnif A L g) (u' : HolUnif A' L' g) (ψ : A'.left ⟶ A.left)
    (hex : ∀ w, (u'.ex w).left ≫ ψ = (u.ex w).left) {w : Fin g → ℂ} {v₁ : epsR ℂ ⟶ A} {v₂ : epsR ℂ ⟶ A'}
    (h : v₂.left ≫ ψ = v₁.left) (d : u'.IsDiff w v₂) : u.IsDiff w v₁ := by
  intro U hU f
  have hU' : ⊤ ≤ v₂.left ⁻¹ᵁ (ψ ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, h]
    exact hU
  have k := d (ψ ⁻¹ᵁ U) hU' ((ψ.app U).hom f)
  have aux : ∀ (q : (epsR ℂ).left ⟶ A.left) (_ : v₂.left ≫ ψ = q) (hq : ⊤ ≤ q ⁻¹ᵁ U),
      (q.appLE U ⊤ hq).hom f = (v₂.left.appLE (ψ ⁻¹ᵁ U) ⊤ hU').hom ((ψ.app U).hom f) := by
    intro q e hq
    subst e
    rw [Scheme.Hom.comp_appLE]
    rfl
  have e2 : (fun z => valAt' (u'.ex z).left (ψ ⁻¹ᵁ U) ((ψ.app U).hom f)) = fun z => valAt' (u.ex z).left U f := by
    funext z
    rw [GlobalTheory.valAt'_comp, hex]
  rw [e2] at k
  rw [aux _ h hU]
  exact k

theorem isDiff_unique {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (hs : SmoothOfRelativeDimension g A.hom) (hc : ConnectedSpace A.left) {v : epsR ℂ ⟶ A}
    {w w' : Fin g → ℂ} (h : u.IsDiff w v) (h' : u.IsDiff w' v) : w = w' := by
  by_cases hv : IsTangent v
  · exact ((TorusTransfer.tangent_bijective u hs).1 v hv).unique h h'
  · exact isDiff_unique_off u hs hc hv h h'


open GlobalTheory.OrthoMetric in
theorem exists_linearEquiv_of_fibreLatVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Sp ℂ ⟶ X) (g g' : ℕ) (Λ Λ' : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (R : RiemLat E g Λ) (R' : RiemLat E g' Λ') (A₀ : Type) (x : A₀ → Fin g → ℂ) (x' : A₀ → Fin g' → ℂ) (v : A₀ → (epsAt z ⟶ t.G)), FibreLatVec t z R x v → FibreLatVec t z R' x' v → ∃ φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ), φ '' Set.range R.P = Set.range R'.P ∧ (∀ p q, R'.ip (φ p) (φ q) = R.ip p q) ∧ (∀ a p, φ (R.B a p) = R'.B a (φ p)) ∧ ∀ i, φ (x i) = x' i := by
  intro E _ _ _ H X t z g g' Λ Λ' _ _ _ _ R R' A₀ x x' v h h'
  obtain ⟨A, _, φ, u, χ, hp, hAH, hB, -, hΛ, hv⟩ := h
  obtain ⟨A', _, φ', u', χ', hp', hAH', hB', -, hΛ', hv'⟩ := h'
  have := t.semi.smooth
  have := t.semi.geomConnected
  have sm : Smooth A.hom := MorphismProperty.of_isPullback hp.1 ‹_›
  have hc : ConnectedSpace A.left := GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) z _ _ hp.1
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected A.hom (Classical.arbitrary _)
  obtain ⟨u₂, h₁, h₂, h₃⟩ := exists_transport hp hp' u'
  have e1 := dim_eq_of_smooth u hd
  have e2 := dim_eq_of_smooth u₂ hd
  subst e1
  subst e2
  have hL : (t.PP.L.pull φ).IsLB := pull_isLB t.PP.isLB φ
  obtain ⟨F, hF⟩ := exists_linear_of_smooth hd u u₂
  have hinj := UnifCompare.injective u u₂ F hF
  let T := LinearEquiv.ofInjectiveEndo F hinj
  have hTF : ∀ w, T w = F w := fun _ => rfl
  let χ₂ : u₂.Λ → ℂ := fun l => χ' ⟨l, (h₂ l).1 l.2⟩
  have hpre : ∀ (j : (t.PP.L.pull φ).ι) w, ⊤ ≤ (u₂.ex w).left ⁻¹ᵁ (t.PP.L.pull φ).U j →
      ⊤ ≤ (u'.ex w).left ⁻¹ᵁ (t.PP.L.pull φ').U j := fun j w hw => by
    have a := (GlobalTheory.ArchMetricCompare.le_pull_iff t.PP.L φ (show Sp ℂ ⟶ _ from (u₂.ex w).left) j).1 hw
    have b : (show Sp ℂ ⟶ _ from (u₂.ex w).left) ≫ φ = (show Sp ℂ ⟶ _ from (u'.ex w).left) ≫ φ' := h₁ w
    rw [b] at a
    exact (GlobalTheory.ArchMetricCompare.le_pull_iff t.PP.L φ' (show Sp ℂ ⟶ _ from (u'.ex w).left) j).2 a
  have e3 : ∀ (j : (t.PP.L.pull φ).ι) w, u₂.fr j w = u'.fr j w := fun j w => h₃ (j PUnit.unit) w
  have hAH₂ : u₂.IsAH R'.Hm χ₂ := by
    refine ⟨hAH'.1, hAH'.2.1, fun l => hAH'.2.2.1 _, fun l j w hw => ?_⟩
    rw [e3, e3]
    exact hAH'.2.2.2 ⟨l, (h₂ l).1 l.2⟩ j w (hpre j w hw)
  have hH := UnifCompare.hermForm_eq hL u u₂ hAH hAH₂ F hF
  refine ⟨T, ?_, fun p q => hH q p, fun a p => ?_, fun i => ?_⟩
  · ext y
    constructor
    · rintro ⟨w, ⟨l, rfl⟩, rfl⟩
      exact (hΛ' _).1 ((h₂ _).1 ((UnifCompare.mem_iff u u₂ F hF _).2 ((hΛ _).2 ⟨l, rfl⟩)))
    · intro hy
      have e4 : F (T.symm y) = y := T.apply_symm_apply y
      refine ⟨T.symm y, (hΛ _).1 ((UnifCompare.mem_iff u u₂ F hF _).1 ?_), T.apply_symm_apply y⟩
      rw [e4]
      exact (h₂ _).2 ((hΛ' _).2 hy)
  · have key : ∀ q, F (R.B a q) - R'.B a (F q) ∈ u₂.Λ := fun q => by
      have e : u₂.ex (F (R.B a q)) = u₂.ex (R'.B a (F q)) := by
        rw [hF]
        refine pt_ext hp ?_
        calc (u.ex (R.B a q)).left ≫ φ = (u.ex q).left ≫ φ ≫ (t.act.act a).left := hB a q
          _ = ((u.ex q).left ≫ φ) ≫ (t.act.act a).left := (Category.assoc _ _ _).symm
          _ = ((u'.ex (F q)).left ≫ φ') ≫ (t.act.act a).left := by rw [← h₁ (F q), hF]
          _ = (u'.ex (F q)).left ≫ φ' ≫ (t.act.act a).left := Category.assoc _ _ _
          _ = (u'.ex (R'.B a (F q))).left ≫ φ' := (hB' a (F q)).symm
          _ = (u₂.ex (R'.B a (F q))).left ≫ φ := (h₁ _).symm
      rw [← u₂.ker]
      have h5 := u₂.ex_add (F (R.B a q) - R'.B a (F q)) (R'.B a (F q))
      rw [sub_add_cancel, e] at h5
      exact mul_eq_right.1 h5.symm
    have h0 := GlobalTheory.LatticeHom.eq_zero_of_forall_smul_mem u₂.Λ u₂.discrete
      (z := F (R.B a p) - R'.B a (F p)) fun c => by
        have := key (c • p)
        simpa only [map_smul, smul_sub] using this
    exact sub_eq_zero.1 h0
  · obtain ⟨v₁, f₁, d₁⟩ := hv i
    obtain ⟨v₂, f₂, d₂⟩ := hv' i
    have d₃ : u₂.IsDiff (T (x i)) v₁ :=
      (UnifCompare.isDiff_iff u u₂ T.toContinuousLinearEquiv hF (x i) v₁).1 d₁
    obtain ⟨ψ, hψ⟩ := GlobalTheory.SharpPull.exists_lift hp' hp (𝟙 t.G)
    have hψ' : ψ.left ≫ φ = φ' := hψ.trans (Category.comp_id _)
    have hv₁ : v₂.left ≫ ψ.left = v₁.left := hp.1.hom_ext
      (by rw [Category.assoc, hψ', f₂, f₁]) (by rw [Category.assoc, Over.w, Over.w, Over.w])
    have hex : ∀ w, (u'.ex w).left ≫ ψ.left = (u₂.ex w).left := fun w => hp.1.hom_ext
      (by rw [Category.assoc, hψ', h₁]) (by rw [Category.assoc, Over.w, Over.w, Over.w])
    exact isDiff_unique u₂ hd hc d₃ (isDiff_of_comp u₂ u' ψ.left hex hv₁ d₂)

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair
open GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.UU

theorem cubWeil_of_lbIso (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] (hs : IsSemiAbelian G) (τ : TorusExtension G)
    (L₁ L₂ : RigLB G) (c₁ : CubicalStr G L₁) (c₂ : CubicalStr G L₂) (hw : LBIso L₁.L L₂.L) (N : ℕ)
    (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G) (ζ : Γ(Sp ℂ, ⊤)ˣ) (h : CubWeil c₁ N x y ζ) : CubWeil c₂ N x y ζ :=
  _root_.GlobalTheory.CompanionTheory.Ar.CubIso.cubWeil_of_lbIso G hs τ L₁ L₂ c₁ c₂ hw N x y ζ h

theorem cubWeil_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {N : ℕ}
    {Z : Scheme.{0}} {a b : Z ⟶ S} (hab : a = b) {x y : Over.mk a ⟶ G} {x' y' : Over.mk b ⟶ G}
    (hx : x'.left = x.left) (hy : y'.left = y.left) {ζ : Γ(Z, ⊤)ˣ} (h : CubWeil c N x y ζ) :
    CubWeil c N x' y' ζ := by
  subst hab
  obtain rfl : x' = x := Over.OverMorphism.ext hx
  obtain rfl : y' = y := Over.OverMorphism.ext hy
  exact h

theorem cubWeil_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {Z : Scheme.{0}} (a : Z ⟶ S') (b : Z ⟶ S)
    (hb : b = a ≫ f) {N : ℕ} {x y : Over.mk a ⟶ t'.G} {x₀ y₀ : Over.mk b ⟶ t.G} (ex : x₀.left = x.left ≫ m.φ)
    (ey : y₀.left = y.left ≫ m.φ) (hx : x ^ N = 1) (hy : y ^ N = 1) {ζ : Γ(Z, ⊤)ˣ}
    (h : CubWeil t.cub N x₀ y₀ ζ) : CubWeil t'.cub N x y ζ := by
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.UU.existsUnique_cubWeil t'.cub hx hy
  have hw : m.cm.F ≫ t.G.hom = t'.G.hom ≫ f := m.cart.1.w
  have mul : ∀ (T : Over S') (x y : T ⟶ t'.G), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (m.cart.2 T x y _ _ rfl rfl).symm
  have h1 := GlobalTheory.UU.cubWeil_of_isPullCubical S S' f t.G t'.G m.cm hw mul _ _ t.cub t'.cub m.lin N (Over.mk a) x y ξ hξ
  have h2 : CubWeil t.cub N x₀ y₀ ξ := cubWeil_congr hb.symm ex ey h1
  rwa [h2.unique h] at hξ

theorem cubWeil_quot {G B : Over (Sp ℂ)} [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] (hs : IsSemiAbelian G)
    (τ : TorusExtension G) (q : G ⟶ B) [IsMonHom q] (L₁ : RigLB G) (c₁ : CubicalStr G L₁) (L₂ : RigLB B)
    (c₂ : CubicalStr B L₂) (hw : LBIso L₁.L (L₂.L.pull q.left)) (N : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ G)
    (ζ : Γ(Sp ℂ, ⊤)ˣ) (h : CubWeil c₁ N x y ζ) : CubWeil c₂ N (x ≫ q) (y ≫ q) ζ := by
  obtain ⟨hL, hr, ⟨c', hc⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (CubeMap.ofHom q) L₂ c₂
  have h1 := cubWeil_of_lbIso G hs τ L₁ ((CubeMap.ofHom q).rigLB L₂ hL hr) c₁ c' hw N x y ζ h
  have hw' : (CubeMap.ofHom q).F ≫ B.hom = G.hom ≫ 𝟙 _ := by
    simp [CubeMap.ofHom]
  have e : ∀ (T : Over (Sp ℂ)) (a : T ⟶ G), Out.toBase hw' a =
      (Over.homMk (𝟙 T.left) (by simp) : Over.mk (T.hom ≫ 𝟙 _) ⟶ T) ≫ a ≫ q := fun T a =>
    Over.OverMorphism.ext (by simp [Out.toBase, CubeMap.ofHom])
  have mul : ∀ (T : Over (Sp ℂ)) (a b : T ⟶ G), Out.toBase hw' (a * b) = Out.toBase hw' a * Out.toBase hw' b := by
    intro T a b
    rw [e, e, e, MonObj.mul_comp, MonObj.comp_mul]
  have h2 := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ (𝟙 _) B G (CubeMap.ofHom q) hw' mul _ _ c₂ c' hc N _ x y ζ h1
  exact cubWeil_congr (by simp) rfl rfl h2

theorem ex_nsmul {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {g n : ℕ} {M : LieModel G (𝟙 (Sp R)) (Fin g → R)}
    {B : Set (Fin n → ℂ)} {ψ : (Fin n → ℂ) → (R →+* ℂ)} (e : Flat.FamExp G M B ψ) {b : Fin n → ℂ} (hb : b ∈ B)
    (k : ℕ) (z : Fin g → ℂ) : e.ex b (k • z) = e.ex b z ^ k := by
  have h0 : e.ex b 0 = 1 := by
    have := e.add b hb 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  induction k with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ k ih => rw [succ_nsmul, e.add b hb, ih, pow_succ]

theorem ex_nsmul_hol {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (k : ℕ) (z : Fin g → ℂ) :
    u.ex (k • z) = u.ex z ^ k := by
  have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  induction k with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ k ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem weil_value {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (tB : SAB H (Sp ℂ))
    (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ tB.G.left) (g : ℕ) (u : HolUnif A (tB.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hpb : IsGrpPullback A tB.G (𝟙 _) φ) (hAH : u.IsAH Hm χ)
    (hP : IsPrincipal tB) (N : ℕ) (ζ : ℂˣ) (a b : Fin g → ℂ) (hN : 0 < N) (ha : a ∈ u.Λ) (hb : b ∈ u.Λ)
    (x y : 𝟙_ (Over (Sp ℂ)) ⟶ tB.G) (hx : x.left = (u.ex ((N : ℂ)⁻¹ • a)).left ≫ φ)
    (hy : y.left = (u.ex ((N : ℂ)⁻¹ • b)).left ≫ φ) (h : CubWeil tB.cub N x y (unitOn ζ)) :
    (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((a ⬝ᵥ Hm *ᵥ star b).im : ℝ) : ℂ) / N) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hA : IsAbelianScheme A := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := hAb.comm
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hpb.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hpb.2 T x y (pushPt hpb.1.w x) (pushPt hpb.1.w y) rfl rfl,
        ← hpb.2 T y x (pushPt hpb.1.w y) (pushPt hpb.1.w x) rfl rfl, _root_.mul_comm]
    · exact MorphismProperty.of_isPullback (P := @Smooth) hpb.1 hAb.smooth
    · exact MorphismProperty.of_isPullback (P := @IsProper) hpb.1 hAb.proper
    · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 hAb.geomConnected
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := tB.sym
  have hL' : (tB.PP.L.pull φ).IsLB := by
    refine ⟨top_le_iff.1 ?_, ?_, ?_⟩
    · intro y _
      obtain ⟨j, hj⟩ := exists_chart tB.PP.isLB (φ y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j, mem_pull.2 hj⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 _) y _ hy, map_one, gm_pull_g tB.PP.L φ (𝟙 _) y J J hy hy]
      exact gm_self tB.PP.isLB φ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy,
        gm_pull_g tB.PP.L φ (𝟙 _) y I J hy.1.1 hy.1.2,
        gm_pull_g tB.PP.L φ (𝟙 _) y J K hy.1.2 hy.2,
        gm_pull_g tB.PP.L φ (𝟙 _) y I K hy.1.1 hy.2]
      exact gm_cocycle tB.PP.isLB φ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have hw := (isGen_iff _).1 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen hL')
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpb.1 hd
      L := tB.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hpb ⟨tB.PP.rig, tB.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hpb fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := relAmple_pull hpb.1 tB.PP.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hP.2.1
      ktriv := kTriv_pull hpb tB.PP.isLB hL' hw hP.2.2 }
  haveI : IsCommMonObj A := hA.comm
  have tors : ∀ w : Fin g → ℂ, w ∈ u.Λ → u.ex ((N : ℂ)⁻¹ • w) ^ N = 1 := fun w hw => by
    rw [← ex_nsmul_hol, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (u.ker w).2 hw
  obtain ⟨hL, hr, ⟨c', hc⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (cubeMapOf hpb) tB.PP tB.cub
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil c' (tors a ha) (tors b hb)
  have hw' : (cubeMapOf hpb).F ≫ tB.G.hom = A.hom ≫ 𝟙 _ := hpb.1.w
  have mul : ∀ (T : Over (Sp ℂ)) (p q : T ⟶ A), Out.toBase hw' (p * q) = Out.toBase hw' p * Out.toBase hw' q :=
    fun T p q => Over.OverMorphism.ext (hpb.2 T p q _ _ rfl rfl).symm
  have h1 := cubWeil_of_isPullCubical _ _ (𝟙 _) tB.G A (cubeMapOf hpb) hw' mul _ _ tB.cub c' hc N _ _ _ ξ hξ
  have h2 : CubWeil tB.cub N x y ξ := cubWeil_congr (by simp) hx hy h1
  obtain rfl : ξ = unitOn ζ := h2.unique h
  have hW₁ : Out.WeilIs Q.A Q.L N (u.ex ((N : ℂ)⁻¹ • a)) (u.ex ((N : ℂ)⁻¹ • b)) (unitOn ζ) :=
    (cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA (tors a ha) (tors b hb) _).1 hξ
  obtain ⟨Ef, hE, -, -, -, -, hWe⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hAH
  let c : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (Ef ⟨a, ha⟩ ⟨b, hb⟩ : ℂ) / N)) (Complex.exp_ne_zero _)
  have hW₂ := hWe N ⟨a, ha⟩ ⟨b, hb⟩ c hN rfl
  have e := ((GlobalTheory.abelianSchemeLaws_all.1.weil (Sp ℂ) Q N (𝟙_ _)).1 _ _ (tors a ha) (tors b hb)).unique hW₁ hW₂
  have e' : ζ = c := Units.ext (by
    have := congrArg (fun v : Γ(Sp ℂ, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom v.val) e
    simpa [unitOn] using this)
  rw [e']
  show Complex.exp _ = _
  have i := hE ⟨a, ha⟩ ⟨b, hb⟩
  congr 3
  exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) i

theorem cubWeil_eq_exp_riemann : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (N : ℕ) (ζ : ℂˣ) (y y' : Fin g → ℂ), 0 < N → y ∈ e.per b → y' ∈ e.per b → CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im : ℝ) : ℂ) / N) := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ ℓ hb hpb hAH hP hLift N ζ y y' hN hy hy' hW
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨ρ, hρ⟩ := GlobalTheory.AlphaPair.exists_ptEquiv P.m.cart (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.AlphaPair.exists_ptEquiv hpb (𝟙 (Sp ℂ)) (𝟙 (Sp ℂ)) (Category.id_comp _).symm
  letI := P.τ.grpB
  have := P.τ.q_hom
  have := P.e_hom
  have tors : ∀ w : Fin g → ℂ, w ∈ e.per b → e.ex b ((N : ℂ)⁻¹ • w) ^ N = 1 := fun w hw => by
    rw [← ex_nsmul e hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact hw
  let s : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G := ρ.symm (e.ex b ((N : ℂ)⁻¹ • y))
  let s' : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G := ρ.symm (e.ex b ((N : ℂ)⁻¹ • y'))
  have hs : s.left ≫ P.m.φ = (e.ex b ((N : ℂ)⁻¹ • y)).left :=
    (hρ s).symm.trans (congrArg (fun q => q.left) (ρ.apply_symm_apply _))
  have hs' : s'.left ≫ P.m.φ = (e.ex b ((N : ℂ)⁻¹ • y')).left :=
    (hρ s').symm.trans (congrArg (fun q => q.left) (ρ.apply_symm_apply _))
  have ts : s ^ N = 1 := ρ.injective (by
    show ρ (ρ.symm _ ^ N) = ρ 1
    rw [map_pow, ρ.apply_symm_apply, tors y hy, map_one])
  have ts' : s' ^ N = 1 := ρ.injective (by
    show ρ (ρ.symm _ ^ N) = ρ 1
    rw [map_pow, ρ.apply_symm_apply, tors y' hy', map_one])
  have W₁ : CubWeil P.tK.cub N s s' (unitOn ζ) :=
    cubWeil_fibre P.m (𝟙 (Sp ℂ)) (spMap (ψ b)) (Category.id_comp _).symm hs.symm hs'.symm ts ts' hW
  have W₂ := cubWeil_quot P.tK.semi P.τ (P.τ.q ≫ P.e.hom) P.tK.PP P.tK.cub P.tB.PP P.tB.cub P.pp N s s' _ W₁
  have lat : ∀ w : Fin g → ℂ, w ∈ e.per b → ℓ w ∈ u.Λ := fun w hw => by
    have h1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G).left ≫ P.m.φ = (e.ex b w).left := by
      have := hρ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.tK.G)
      rw [map_one] at this
      rw [← this]
      exact congrArg (fun q => q.left) (Eq.symm hw)
    have h2 := hLift w 1 h1
    refine (u.ker _).1 (ρ'.injective ?_)
    apply Over.OverMorphism.ext
    rw [map_one, hρ', h2, MonObj.one_comp]
  have hl : ∀ w : Fin g → ℂ, ℓ ((N : ℂ)⁻¹ • w) = (N : ℂ)⁻¹ • ℓ w := fun w => map_smul _ _ _
  exact weil_value P.tB A φ g' u Hm χ hpb hAH hP N ζ (ℓ y) (ℓ y') hN (lat y hy) (lat y' hy') _ _
    ((hl y) ▸ (hLift _ s hs).symm) ((hl y') ▸ (hLift _ s' hs').symm) W₂

end GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair
end
end

