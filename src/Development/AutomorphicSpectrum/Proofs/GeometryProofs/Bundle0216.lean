module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0209
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0171
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0204
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0192
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0137
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx

open GlobalTheory.CompanionTheory.Ar.Cusp.FamEx GlobalTheory.CompanionTheory.Ar.Flat.PerGram

section Tangent

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem surjective_of_add_mem {g₀ : ℕ} (Λ : Submodule ℤ (Fin g₀ → ℂ)) (hd : DiscreteTopology Λ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g₀ → ℂ)) (h : ∀ y, ∃ z, y - F z ∈ Λ) : Function.Surjective F := by
  have hc : (Λ : Set (Fin g₀ → ℂ)).Countable := by
    haveI := hd
    have : Countable Λ := countable_of_Lindelof_of_discrete
    exact Set.countable_coe_iff.1 this
  intro y
  have h0 : (LinearMap.range F).mkQ y = 0 := by
    refine GlobalTheory.eq_zero_of_forall_smul_mem_countable (hc.image (LinearMap.range F).mkQ) fun s => ?_
    obtain ⟨z, hz⟩ := h (s • y)
    refine ⟨_, hz, ?_⟩
    simp only [map_sub, map_smul, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero (LinearMap.range F)).2 ⟨z, rfl⟩, sub_zero]
  simpa using h0

theorem exists_isDiff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
    {z : Sp ℂ ⟶ X} (t' : SAB H (Sp ℂ)) (m : SABMap t' t z) (hP : IsProper t'.G.hom)
    (hA : Out.RelAmple t'.G t'.PP.L) {φ : A.left ⟶ t.G.left} (hp : IsGrpPullback A t.G z φ) (u : HolUnif A L g)
    {x : epsR ℂ ⟶ A} (hx : IsTangent x) : ∃ w, u.IsDiff w x := by
  have hab : IsAbelianScheme t'.G := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  obtain ⟨g₀, hg⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ t'.G hab
  obtain ⟨u₀, hc⟩ := GlobalTheory.CompanionTheory.Ar.AVExp.exists_holUnif t'.G t'.PP.L g₀ hab hA hg
  obtain ⟨ht₁, ht₂⟩ := @GlobalTheory.TangentOrigin.tangent_bijection_of_values @GlobalTheory.valAt'_rules t'.G _ _ g₀ u₀ hc
  obtain ⟨e, hmon, -⟩ := grpPullback_iso hp m.cart
  haveI := hmon
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun w => (u.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u) e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo t'.G hab _ g₀ g u₀ ht₁ ht₂
    (fun w => u.ex w ≫ e.hom) (fun p q => by rw [u.ex_add, MonObj.mul_comp]) hol
  have hF' : ∀ w, u₀.ex (F w) = u.ex w ≫ e.hom := hF
  have hsurj : Function.Surjective F := surjective_of_add_mem u₀.Λ u₀.discrete F fun y => by
    obtain ⟨w, hw⟩ := u.ex_onto (u₀.ex y ≫ e.inv)
    refine ⟨w, (u₀.ker _).1 ?_⟩
    have h1 : u₀.ex (F w) = u₀.ex y := by rw [hF', hw, Category.assoc, e.inv_hom_id, Category.comp_id]
    have h2 := u₀.ex_add (y - F w) (F w)
    rw [sub_add_cancel, h1] at h2
    have h3 : u₀.ex (y - F w) * u₀.ex y = 1 * u₀.ex y := by rw [← h2, _root_.one_mul]
    exact mul_right_cancel h3
  have hxe : IsTangent (x ≫ e.hom) := by
    have h₁ : η[A] ≫ e.hom = η[t'.G] := IsMonHom.one_hom e.hom
    unfold IsTangent at hx ⊢
    rw [Over.comp_left, ← Category.assoc, hx, ← Over.comp_left, h₁]
  obtain ⟨w₀, hw₀, -⟩ := ht₁ (x ≫ e.hom) hxe
  obtain ⟨w, rfl⟩ := hsurj w₀
  refine ⟨w, ?_⟩
  have a := isDerivAt0_of_isDiff u₀ hxe hw₀
  have b := GlobalTheory.FibreDeriv.isDerivAt0_comp a e.inv.left
  have hol' : IsHolTo (Set.univ : Set (Fin g₀ → ℂ)) (fun z => (u₀.ex z).left ≫ e.inv.left) :=
    GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u₀) e.inv.left
  have c := isDerivAt0_comp_linMap hol' F b
  have back : ∀ {T : Over (Sp ℂ)} (q : T ⟶ A), (q ≫ e.hom).left ≫ e.inv.left = q.left := fun q => by
    rw [← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
  have e1 : (fun z => (u₀.ex (F z)).left ≫ e.inv.left) = fun z => (u.ex z).left :=
    funext fun z => by rw [hF', back]
  rw [e1, back] at c
  exact fun U h f => c.2 U h f

end Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem fibreLatVec_of_fibreLat {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R : RiemLat E g Λ} (hz : HodgeMetric.PolarisedAt t z) (hF : FibreLat t z R) {A₀ : Type}
    (v : A₀ → (epsAt z ⟶ t.G)) (hv : ∀ i, IsTanAt t.G z (v i)) : ∃ x : A₀ → Fin g → ℂ, FibreLatVec t z R x v := by
  obtain ⟨t', m, hP, hA⟩ := hz
  obtain ⟨A, _, φ, u, χ, hp, hAH, hact, hinj, hmem, -⟩ := hF
  have key : ∀ i, ∃ (x : Fin g → ℂ) (v' : epsR ℂ ⟶ A), v'.left ≫ φ = (v i).left ∧ u.IsDiff x v' := fun i => by
    let Φ := HodgeLin.tanEquiv hp
    have hl : (Φ.symm (v i)).left ≫ φ = (v i).left := congrArg (fun q => q.left) (Φ.apply_symm_apply (v i))
    have ht : IsTangent (Φ.symm (v i)) := (HodgeLin.isTangent_iff hp _).2 (by
      change IsTanAt t.G z (Φ (Φ.symm (v i)))
      rw [Φ.apply_symm_apply]
      exact hv i)
    obtain ⟨w, hw⟩ := exists_isDiff t' m hP hA hp u ht
    exact ⟨w, _, hl, hw⟩
  choose x v' h1 h2 using key
  exact ⟨x, A, inferInstance, φ, u, χ, hp, hAH, hact, hinj, hmem, fun i => ⟨v' i, h1 i, h2 i⟩⟩

theorem hodgeInnerProduct_eq_pi_mul_riemannForm {X : Scheme.{0}} {t : SAB H X} {z : Sp ℂ ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R : RiemLat E g Λ} {A₀ : Type} {x : A₀ → Fin g → ℂ} {v : A₀ → (epsAt z ⟶ t.G)}
    (h : FibreLatVec t z R x v) (tan : ∀ i, IsTanAt t.G z (v i)) (i j : A₀) :
    HodgeIP t.G t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j)) := by
  obtain ⟨A, _, φ, u, χ, h1, h2, -, -, -, h3⟩ := h
  obtain ⟨v', e', d'⟩ := h3 i
  obtain ⟨w', f', g'⟩ := h3 j
  exact ⟨t.PP.isLB, tan i, tan j, A, inferInstance, φ, g, u, R.Hm, χ, v', w', x i, x j, h1, h2, e', f', d', g', rfl⟩

theorem val_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type} [CommRing R]
    [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (hg : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r)
    (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  have : s = s' := hg.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)
  rw [this]

theorem exists_fibreLat_rank : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type)
    [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (z : Sp ℂ ⟶ 𝔐.X), 1 ≤ D.p + D.q → 𝔐.Interior z →
    ∃ (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X) (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ)
      (R : RiemLat E g Λ), IsOver 𝔐 z κ p ∧ FibreLat 𝔐.t z R ∧
        ∀ s, Module.finrank ℂ (eigSp R.B (κ.comp (labelEmb c s))) = labelRk D s := by
  intro hG E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hD hz
  obtain ⟨κ, p, hO⟩ := exists_isOver E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  have hN : N1c := hG.1.2.2.1
  let j : KA l →+* c.F := (IntermediateField.inclusion c.le).toRingHom
  let ρF : c.F := j (baseKA l).ρ
  have hρF : (ρF : ℂ) = H.rt0 := rfl
  have hσ : p ≫ Xo.s = spMap (κ.comp j) := by
    obtain ⟨x, -, h1, h2⟩ := hO
    rw [← h1, Category.assoc, pullback.condition, ← Category.assoc, h2, Chg.spMap_comp']
  have hsq : (κ ρF) ^ 2 = H.rt0 ^ 2 := by
    have e : ρF ^ 2 = -((H.d : ℕ) : c.F) := Subtype.ext (by
      push_cast
      rw [hρF]
      exact H.sqrt_neg_disc_sq)
    rw [← map_pow, e, H.sqrt_neg_disc_sq]
    simp
  have hconj : starRingEnd ℂ H.rt0 = -H.rt0 := conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq
  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by
      have : (2 : ℂ) * H.rt0 = 0 := by linear_combination h
      simpa using this
    have h1 := H.sqrt_neg_disc_sq
    rw [h0] at h1
    have h2 : ((H.d : ℕ) : ℂ) = 0 := by simpa using h1.symm
    exact H.d_prime.pos.ne' (by exact_mod_cast h2)
  by_cases hρ : κ ρF = H.rt0
  · obtain ⟨FU⟩ := hN E H D l Xo (κ.comp j) g ty hD hρ hty
    obtain ⟨i, P, hP, hu⟩ := FU.onto p hσ
    obtain ⟨⟨R, -, hF, hr⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj E H D l Xo (κ.comp j) g ty FU i P hty hP
    refine ⟨κ, p, g, _, inferInstance, inferInstance, R, hO,
      _root_.GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver E H D l Xo c Y S Ω K J y 𝔐 z κ p g _ _ hO (hu ▸ hF), fun s => ?_⟩
    obtain ⟨τ, hτ, hτρ⟩ := exists_emb_label E H l c κ s
    have h := hτρ ρF hρF
    rw [hτ, hr τ]
    rcases s with s | s
    · have h' : τ (H.rt : E) = H.rt0 := h.trans hρ
      simp [h']
    · have h' : τ (H.rt : E) = -H.rt0 := h.trans (by simp [hρ])
      simp [h', hne.symm]
  · have hneg : κ ρF = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hρ
    have hρ₁ : ((starRingEnd ℂ).comp (κ.comp j)) (baseKA l).ρ = H.rt0 := by
      show starRingEnd ℂ (κ ρF) = H.rt0
      rw [hneg, map_neg, hconj, neg_neg]
    obtain ⟨FU⟩ := hN E H D l Xo ((starRingEnd ℂ).comp (κ.comp j)) g ty hD hρ₁ hty
    have hσ₁ : (spMap (starRingEnd ℂ) ≫ p) ≫ Xo.s = spMap ((starRingEnd ℂ).comp (κ.comp j)) := by
      rw [Category.assoc, hσ]
      exact (Chg.spMap_comp' _ _).symm
    obtain ⟨i, P, hP, hu⟩ := FU.onto _ hσ₁
    obtain ⟨-, R, -, hF, hr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.period_lattice_fibre_and_conj E H D l Xo _ g ty FU i P hty hP
    have hcc : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ p = p := by
      have e : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun x => by simp
      rw [← Category.assoc, ← Chg.spMap_comp', e]
      simp [spMap]
    rw [hu, hcc] at hF
    refine ⟨κ, p, g, _, inferInstance, inferInstance, R, hO,
      _root_.GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.fibreLat_of_isOver E H D l Xo c Y S Ω K J y 𝔐 z κ p g _ _ hO hF, fun s => ?_⟩
    obtain ⟨τ, hτ, hτρ⟩ := exists_emb_label E H l c κ s
    have h := hτρ ρF hρF
    rw [hτ, hr τ]
    rcases s with s | s
    · have h' : τ (H.rt : E) = -H.rt0 := h.trans hneg
      simp [h', hne.symm]
    · have h' : τ (H.rt : E) = H.rt0 := h.trans (by simp [hneg])
      simp [h']

theorem exists_riemLat_of_interior : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 1 ≤ D.p + D.q → 𝔐.Interior z → Top.Given → ∀ (A₀ : Type) (v : A₀ → (epsAt z ⟶ 𝔐.t.G)), (∀ i, IsTanAt 𝔐.t.G z (v i)) → ∃ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (R : RiemLat E g Λ) (x : A₀ → Fin g → ℂ), FibreLatVec 𝔐.t z R x v ∧ (∀ i j, HodgeIP 𝔐.t.G 𝔐.t.PP.L z (v i) (v j) (Real.pi * R.ip (x i) (x j))) ∧ ∀ σ, 𝔐.LabVal z id σ → ∀ s, Module.finrank ℂ (eigSp R.B (σ s)) = labelRk D s := by
  intro _ E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hD hz hG A₀ v hv
  obtain ⟨κ, p, g, Λ, i₁, i₂, R, hO, hF, hr⟩ := exists_fibreLat_rank hG E H D l Xo c Y S Ω K J y 𝔐 z hD hz
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hpol := HodgeMetric.polarisedAt_of_interior E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain ⟨x, hx⟩ := fibreLatVec_of_fibreLat hpol hF v hv
  refine ⟨g, Λ, i₁, i₂, R, x, hx, fun i j => hodgeInnerProduct_eq_pi_mul_riemannForm hx hv i j, fun σ hσ s => ?_⟩
  have e : σ s = κ.comp (labelEmb c s) := RingHom.ext fun a =>
    val_unique 𝔐.tie.gen (hσ s a) (val_cst E H D l Xo c Y S Ω K J y 𝔐 z κ p hO (labelEmb c s a))
  rw [e]
  exact hr s

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreEx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SabModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_obj_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → l.A = 1 → ∀ (ρ : L) (σ : L →+* ℂ),
    σ ρ = H.rt0 →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ D.q)) →
    TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)) →
    ∀ (F₀ : IntermediateField ℚ ℂ), FiniteDimensional ℚ F₀ → ∀ hK : KA l ≤ F₀,
    ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (hF : F₀ ≤ F) (e : L →+* F)
      (o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion (hK.trans hF)).toRingHom)),
      (∀ x, ((e x : F) : ℂ) = σ x) ∧ Nonempty (SABMap o.t t (spMap e)) := by
  intro E _ _ _ H D l L _ _ t ht hA ρ σ hσ hs I F₀ hF₀ hK
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨F₁, hF₁, e₁, he₁, hT⟩ := _root_.GlobalTheory.CompanionTheory.Ar.torsion_defined_over_numberField L σ (pol t ht) l.M hM
  have hfin : FiniteDimensional ℚ ↥(F₀ ⊔ F₁) := inferInstance
  let i₁ : F₁ →+* ↥(F₀ ⊔ F₁) := (IntermediateField.inclusion le_sup_right).toRingHom
  let e : L →+* ↥(F₀ ⊔ F₁) := i₁.comp e₁
  have he : ∀ x, ((e x : ↥(F₀ ⊔ F₁)) : ℂ) = σ x := he₁
  obtain ⟨t₂, ⟨m⟩⟩ := exists_sab (spMap e) t
  obtain ⟨w, gw, -⟩ := m.lin
  have hL₂ : LBIso t₂.PP.L (t.PP.L.pull m.cm.F) := ⟨w, gw⟩
  have ht₂ : IsPrincipal t₂ :=
    ⟨MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 ht.1,
      relAmple_pull m.cart.1 t.PP.isLB t₂.PP.isLB ((isGen_iff w).1 gw) ⊤ (isAffineOpen_top _) (fun _ => trivial) ht.2.1,
      kTriv_pull m.cart t.PP.isLB t₂.PP.isLB ((isGen_iff w).1 gw) ht.2.2⟩
  let x₂ : Sp ℂ ⟶ Sp ↥(F₀ ⊔ F₁) := spMap (algebraMap ↥(F₀ ⊔ F₁) ℂ)
  have hx : x₂ ≫ spMap e = spMap σ := by
    rw [← spMap_comp]
    exact congrArg spMap (RingHom.ext he)
  obtain ⟨Φ, hΦ, hW⟩ : ∃ Φ : (Over.mk x₂ ⟶ t₂.G) ≃* (Over.mk (spMap σ) ⟶ t.G),
      (∀ x, (Φ x).left = x.left ≫ m.φ) ∧ ∀ (k : ℕ) x y c, Out.WeilIs t.G t.PP.L k (Φ x) (Φ y) c →
        Out.WeilIs t₂.G t₂.PP.L k x y c := by
    have key : ∀ y : Sp ℂ ⟶ Sp L, x₂ ≫ spMap e = y → ∃ Φ : (Over.mk x₂ ⟶ t₂.G) ≃* (Over.mk y ⟶ t.G),
        (∀ x, (Φ x).left = x.left ≫ m.φ) ∧ ∀ (k : ℕ) x y c, Out.WeilIs t.G t.PP.L k (Φ x) (Φ y) c →
          Out.WeilIs t₂.G t₂.PP.L k x y c := by
      rintro _ rfl
      exact ⟨GlobalTheory.ObjPull.pushEquiv m.cart (Over.mk x₂), fun _ => rfl, fun k x y c h =>
        GlobalTheory.Relabel.weilIs_push t.PP.isLB t₂.PP.isLB m.cart hL₂ (Over.mk x₂) _ rfl k x y _ _ c rfl rfl h⟩
    exact key _ hx
  let I₂ : TateIso D ℂ (Over.mk x₂ ⟶ t₂.G) (fun a g => g ≫ t₂.act.act a)
      (fun n g g' c => Out.WeilIs t₂.G t₂.PP.L n g g' (unitOn c)) :=
    GlobalTheory.ObjPull.tateMove Φ (fun c x => Over.OverMorphism.ext (by
      show (Φ _).left = (Φ x ≫ _).left
      rw [hΦ, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc]
      exact congrArg _ (m.act c))) (fun n x y c h => hW n x y _ h) I
  have hsec : ∀ a : D.La, ∃ s : 𝟙_ (Over (Sp ↥(F₀ ⊔ F₁))) ⟶ t₂.G, toUnit _ ≫ s = I₂.ev l.M a := fun a => by
    obtain ⟨y₁, hy₁, hy₂⟩ : ∃ y : Sp F₁ ⟶ t.G.left, y ≫ t.G.hom = spMap e₁ ∧
        spMap (algebraMap F₁ ℂ) ≫ y = (I.ev l.M a).left := hT (I.ev l.M a) ((I.onto l.M hM _).2 ⟨a, rfl⟩)
    have hw₁ : (spMap i₁ ≫ y₁) ≫ t.G.hom = 𝟙 _ ≫ spMap e := by
      rw [Category.assoc]
      refine (congrArg (spMap i₁ ≫ ·) hy₁).trans ?_
      rw [Category.id_comp]
      exact (spMap_comp _ _).symm
    refine ⟨Over.homMk (m.cart.1.lift _ _ hw₁) (m.cart.1.lift_snd _ _ _), ?_⟩
    apply Φ.injective
    show Φ _ = Φ (Φ.symm _)
    rw [MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rw [hΦ, Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    show (x₂ ≫ m.cart.1.lift _ _ hw₁) ≫ m.φ = _
    rw [Category.assoc]
    refine (congrArg (x₂ ≫ ·) (m.cart.1.lift_fst _ _ hw₁)).trans ?_
    rw [← hy₂, ← Category.assoc]
    exact congrArg (· ≫ y₁) (spMap_comp _ _).symm
  have hK₂ : KA l ≤ F₀ ⊔ F₁ := hK.trans le_sup_left
  have hρ : IntermediateField.inclusion hK₂ (baseKA l).ρ = e ρ := Subtype.ext (by
    refine Eq.trans ?_ (he ρ).symm
    rw [hσ]
    rfl)
  obtain ⟨o, ho⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SabModel.obj_of_sections E H D l (F₀ ⊔ F₁) hK₂ t₂ ht₂ hA (fun k _ _ g τ => by
    have hp : ∀ n, LieMult t₂.act (spMap g) τ n ↔ LieMult t.act (spMap (g.comp e)) τ n := fun n =>
      (GlobalTheory.LiePull.lieMult_pull (𝓞 E) _ _ _ _ _ _ t.act t₂.act m.cart m.act k (spMap g) τ n).trans
        (iff_of_eq (congrArg (fun x => LieMult t.act x τ n) (spMap_comp _ _).symm))
    have h := hs k (g.comp e) τ
    rw [hρ, hp, hp]
    exact h) I₂ hsec
  refine ⟨F₀ ⊔ F₁, hfin, le_sup_left, e, o, he, ?_⟩
  rw [ho]
  exact ⟨m⟩

theorem exists_embedding_rt0 {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {L : Type} [Field L]
    [NumberField L] (ρ : L) (hρ : ρ ^ 2 = -(H.d : L)) : ∃ σ : L →+* ℂ, σ ρ = H.rt0 := by
  obtain ⟨σ₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  have h : (σ₀ ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨σ₀, h⟩
  · refine ⟨(starRingEnd ℂ).comp σ₀, ?_⟩
    have hc : starRingEnd ℂ H.rt0 = -H.rt0 := by
      have hre : H.rt0.re = 0 := by
        have h1 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
          have := congrArg Complex.im H.sqrt_neg_disc_sq
          simpa [pow_two, Complex.mul_im] using this
        have h2 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
          have := congrArg Complex.re H.sqrt_neg_disc_sq
          simpa [pow_two, Complex.mul_re] using this
        have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
        rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by linarith) with h3 | h3
        · exact h3
        · rw [h3] at h2
          nlinarith [mul_self_nonneg H.rt0.re]
      apply Complex.ext <;> simp [hre]
    show starRingEnd ℂ (σ₀ ρ) = _
    rw [h, map_neg, hc, neg_neg]

theorem exists_sab_model : N1ab → PartI → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∃ (ρ : L) (p' q' : ℕ), ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g ρ → LieMult t.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ q')) → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (t' : SAB H (Sp (𝓞 L'))) (tK : SAB H (Sp L')), Nonempty (SABMap tK t' (spMap (algebraMap (𝓞 L') L'))) ∧ Nonempty (SABMap tK t (spMap e)) := by
  intro hN hP E _ _ _ H L _ _ t ht ⟨ρ, p', q', hρ, hs⟩
  by_cases h0 : p' + q' = 0
  · obtain ⟨rfl, rfl⟩ : p' = 0 ∧ q' = 0 := by omega
    obtain ⟨t', ⟨m⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero E H L t ht fun σ τ => by
      by_cases h : τ H.rt = σ ρ
      · exact (hs ℂ σ τ).1 h
      · exact (hs ℂ σ τ).2 h
    exact ⟨L, inferInstance, inferInstance, RingHom.id L, t', t, ⟨m⟩,
      ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast (GlobalTheory.ObjComp.sabMapId t) (Spec.map_id _).symm⟩⟩
  · obtain ⟨σ, hσ⟩ := exists_embedding_rt0 H ρ hρ
    obtain ⟨D, rfl, rfl, ⟨I⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SabModel.datum_tate E H L t ht σ p' q' fun τ => by
      have := hs ℂ σ τ
      rwa [hσ] at this
    have hD : 1 ≤ D.p + D.q := by omega
    let Xo : ∀ l : Level H, Moduli D l := fun l => (hN E H D l hD).some
    obtain ⟨l, hA, hg⟩ := GlobalTheory.GlobalModelGuards.exists_good_level H
    obtain ⟨c⟩ := GlobalTheory.ModuliProbe.coeff_nonempty l
    haveI := c.fin
    obtain ⟨Yl, -, h6⟩ := hP.2 E H D hD Xo
    obtain ⟨Y, -, -⟩ := h6 l c hg hA
    obtain ⟨F, hfin, hF, e, o, -, ⟨m⟩⟩ := exists_obj_ext E H D l L t ht hA ρ σ hσ hs I c.F c.fin c.le
    haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
    obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := (Xo l).rep (Sp F) _ inferInstance o
    let bF : c.F →+* F := (IntermediateField.inclusion hF).toRingHom
    let y : Sp F ⟶ (Xo l).XF c := pullback.lift f (spMap bF) (by
      rw [hf, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun x => Subtype.ext rfl))
    have hy1 : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
    have hy2 : y ≫ pullback.snd _ _ = spMap bF := pullback.lift_snd _ _ _
    obtain ⟨yt, hyt⟩ := _root_.GlobalTheory.CompanionTheory.Ar.model_point_extends_to_integers E H D l (Xo l) c c.fin Y F bF y hy2
    obtain ⟨t', ⟨m'⟩⟩ := exists_sab yt Y.t
    rw [← hy1] at mf
    obtain ⟨m₁, -⟩ := ObjComp.objMap_cancel Y.m0 mf
    obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m m₁.toSABMap
    have n' : SABMap o.t Y.t (spMap (algebraMap (𝓞 F) F) ≫ yt) := ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n (by
      rw [hyt]; rfl)
    obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m' n'
    exact ⟨F, inferInstance, inferInstance, e, t', o.t, ⟨k⟩, ⟨m⟩⟩

end GlobalTheory.CompanionTheory.Ar.SabModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionDifferentiable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem isFn_differentiable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) (a : ArchFrame P z g) (n : ℕ) (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ), a.IsFn s θ → Differentiable ℂ θ := by
  intro S G _ _ P z g a n s θ hθ w₀
  have hm : a.pt w₀ (default : PrimeSpectrum ℂ) ∈ ⨆ i, P.L.U i := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  have hi : ⊤ ≤ a.pt w₀ ⁻¹ᵁ P.L.U i := (GlobalTheory.top_le_preimage_iff_mem _ _).2 hi'
  let W : G.left.Opens := LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i)
  let Q : a.A.left.Opens := (P.L.pull a.φ).U (fun _ => i)
  let C : Set (Fin g → ℂ) := {w | ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ Q}
  have hCpt : ∀ w, w ∈ C → ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i := fun w h y hy =>
    Set.mem_iInter.1 (h hy) PUnit.unit
  have hptC : ∀ w, ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i → w ∈ C := fun w h y hy =>
    Set.mem_iInter.2 fun _ => h hy
  have hCV : ∀ w, w ∈ C → ⊤ ≤ (a.u.ex w).left ⁻¹ᵁ (a.φ ⁻¹ᵁ W) := fun w h y hy =>
    Set.mem_iInter.2 fun _ => hCpt w h hy
  have ho : IsOpen C := (a.u.hol Q 0).1
  have hv : DifferentiableOn ℂ (fun w => valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i))) C :=
    (a.u.hol _ _).2.mono hCV
  have hfr : DifferentiableOn ℂ (fun w => a.u.fr (fun _ => i) w ^ n) C := (a.u.fr_hol _).pow n
  have hne : ∀ w ∈ C, a.u.fr (fun _ => i) w ^ n ≠ 0 := fun w hw => pow_ne_zero n (a.u.fr_ne _ w hw)
  have hq : DifferentiableOn ℂ θ C := by
    refine (hv.mul (hfr.inv hne)).congr fun w hw => ?_
    have e := hθ i w (hCpt w hw)
    have e' : valF (a.pt w) W (s.f fun _ => i) = valAt' (a.pt w) W (s.f fun _ => i) := rfl
    have e4 : valAt' (a.u.ex w).left (a.φ ⁻¹ᵁ W) ((a.φ.app W).hom (s.f fun _ => i)) = θ w * a.u.fr (fun _ => i) w ^ n :=
      (GlobalTheory.valAt'_comp (a.u.ex w).left a.φ W (s.f fun _ => i)).trans (e'.symm.trans e)
    exact (mul_inv_cancel_right₀ (hne w hw) (θ w)).symm.trans (congrArg (· * (a.u.fr (fun _ => i) w ^ n)⁻¹) e4.symm)
  exact (hq.differentiableAt (ho.mem_nhds (hptC w₀ hi)))

end GlobalTheory.CompanionTheory.Ar.Sl
end

