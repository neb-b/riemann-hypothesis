module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0182
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0160
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpan
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0100
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0181
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

theorem isTan_comp {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {R : Type}
    [CommRing R] {x : Sp R ⟶ S} {v : epsAt x ⟶ G} (h : IsTanAt G x v) : IsTanAt G' x (v ≫ f) := by
  unfold IsTanAt at h ⊢
  rw [Over.comp_left, ← Category.assoc, h, ← Over.comp_left]
  congr 1
  exact MonObj.one_comp f

theorem geo_height_arch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H → CMType H ⊕ CMType H) (r k m : ℕ) (h : r + k = m) (v : Fin r → V) (q : CMType H → Fin k → A.Λ) (b : CMType H → Fin m → 𝔐.Li) (bL : CMType H → Fin m → V) (T : CMType H → Matrix (Fin m) (Fin m) L), 𝔐.IsLinPtOf z P MV A → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (lab τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (lab τ)) → (∀ τ, IsValues 𝔐 z P MV (b τ) (bL τ)) → (∀ τ i, A.fam (lab τ) v (q τ) i = ∑ j, T τ j (Fin.cast h i) • bL τ j) → (∀ τ, (T τ).det ≠ 0) → ∀ e : L →+* ℂ, (∀ τ, 0 < A.gramDet e (q τ)) ∧ ∃ ν : ℝ, 𝔐.GeoPhi lab (spMap e ≫ spMap (algebraMap (𝓞 L) L) ≫ z) b ν ∧ 0 < ν ∧ ν = (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) * ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2 := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 L _ _ z P V _ _ _ _ MV A lab r k m h v q b bL T hA hv hq hb hT hdet e
  obtain ⟨hact, hlab, hΛ, hcoch, hprin, t', m', MB, hfib, hlift⟩ := hA
  have hgram : ∀ τ, 0 < A.gramDet e (q τ) := fun τ =>
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.gramDet_pos_of_adapted E L _ V A (lab τ) r k v (q τ) hv (hq τ).1 (hq τ).2 e
  refine ⟨hgram, ?_⟩
  obtain ⟨P', mK, mB, h1, h2, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.exists_abPart_baseChange E H _ 𝔐.t L ℂ (spMap (algebraMap (𝓞 L) L) ≫ z) P e
  haveI := P.tK.semi.smooth
  obtain ⟨V', _, _, MV', j, hjs, hji, hjpt, hjspan⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieBc.main L ℂ e P.tK.G P'.tK.G mK.φ mK.cart V MV
  obtain ⟨ρ', hρa, hρ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ActBC.exists_act_extends L ℂ e _ _ mK.φ mK.cart (𝓞 E) P.tK.act P'.tK.act mK.act V V' MV MV' j hjpt hjspan
    A.ρ hact
  have hcoch' : P'.IsCochars MV' (A.I.map j) :=
    GlobalTheory.T.torus_over_lie_model_base_change L ℂ e _ _ mK.φ P.τ P'.τ mK.cart h3 V V' MV MV' j hjpt A.I hcoch
  letI := P'.τ.grpB
  haveI := P'.τ.q_hom
  haveI := P'.e_hom
  obtain ⟨hbF, hbI, hbv⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeBC.main E H L t' P.tB P'.tB e m' mB A.Bq MB hfib V'
    (fun x => MV'.pt x ≫ P'.τ.q ≫ P'.e.hom) (fun x => isTan_comp _ (MV'.tan x))
  have hover : ∀ x : A.Λ, (MV'.pt (j x) ≫ P'.τ.q ≫ P'.e.hom).left ≫ mB.φ ≫ m'.φ =
      spMap (dualMap (e.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt (A.f x)).left := fun x => by
    have e1 := hlift x
    unfold LieModel.Lifts at e1
    rw [dualMap_comp]
    have e3 : spMap ((dualMap e).comp (dualMap (algebraMap (𝓞 L) L))) =
        spMap (dualMap e) ≫ spMap (dualMap (algebraMap (𝓞 L) L)) := by
      simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e3, Category.assoc, ← e1, Over.comp_left, Category.assoc]
    rw [← Category.assoc (P'.τ.q ≫ P'.e.hom).left, ← h2, Category.assoc, ← Category.assoc _ mK.φ, hjpt]
    simp [Over.comp_left]
  have heig : ∀ τ a, eigComp ρ' (e.comp (A.σ (lab τ))) (j (v a)) = j (eigComp A.ρ (A.σ (lab τ)) (v a)) := fun τ a => by
    refine GlobalTheory.T.eigen_component_map_compat L ℂ V V' (𝓞 E) e j hjs A.ρ ρ' hρ (A.σ (lab τ)) (v a) ?_
    have h0 := (hq τ).1.1.ne_zero (Fin.castAdd k a)
    simpa [LinPt.fam] using h0
  have hpos : 0 < (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) *
      ∏ τ, (4 * Real.pi)⁻¹ ^ r * A.gramDet e (q τ) / ‖e (T τ).det‖ ^ 2 := by
    refine mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hv.2.2)) (Finset.prod_pos fun τ _ => ?_)
    have hne : e (T τ).det ≠ 0 := fun h0 => hdet τ ((map_eq_zero e).1 h0)
    have hp : (0 : ℝ) < 4 * Real.pi := by positivity
    have := hgram τ
    positivity
  refine ⟨_, ⟨P', V', _, _, MV', ρ', A.I.map j, hbF, fun τ => e.comp (A.σ (lab τ)), fun τ i => j (bL τ i), hρa, hcoch',
    fun τ a => GlobalTheory.CompanionTheory.Ar.RootHt.PullVal.valAt_of_field_map _ _ _ e rfl (hlab (lab τ) a), hbI, fun τ i => ?_,
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.PhiBaseChange.phiNormSq_baseChange E L _ V A lab r k m h v q bL T hv hq hT hdet e V' j hjs hji ρ' hρ heig hbF (fun τ c c' =>
      hbv _ _ _ _ (hover _) (hover _))⟩, hpos, rfl⟩
  obtain ⟨v₀, hv₀, e₀⟩ := hb τ i
  refine ⟨LieSigma.pullEps e _ ≫ v₀, _root_.GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC.valAt_field_map _ _ _ _ _ 𝔐.M _ _ _ e _ _ hv₀, ?_⟩
  rw [← h1, ← Category.assoc, hjpt, Category.assoc, e₀]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeSpecializationValue
section
open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt

open MvPolynomial

theorem norm_le_one_of_monic_eval₂ {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜] {R : Type} [CommRing R]
    (φ : R →+* 𝕜) (hφ : ∀ r, ‖φ r‖ ≤ 1) {f : Polynomial R} (hmon : f.Monic) {x : 𝕜}
    (hf : f.eval₂ φ x = 0) : ‖x‖ ≤ 1 := by
  by_contra! h
  rw [hmon.as_sum] at hf
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hf
  have hsum : x ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left hf
  have hpos : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
    · rw [h0] at hsum
      simp at hsum
    · exact h0
  have hle : ‖∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (f.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ f.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖φ (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (f.natDegree - 1) :=
          mul_le_mul (hφ _) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (f.natDegree - 1) := one_mul _
  have h1 : ‖x‖ ^ f.natDegree ≤ ‖x‖ ^ (f.natDegree - 1) := by
    rw [← norm_pow, hsum, norm_neg]
    exact hle
  have h2 : ‖x‖ ^ (f.natDegree - 1) < ‖x‖ ^ f.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

section Ring

variable {Ω : Type} [Field Ω] {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜]

def unitBall (A : Subring Ω) (ev : A →+* 𝕜) : Subring Ω where
  carrier := {x | ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1}
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have e : (⟨a * b, A.mul_mem ha hb⟩ : A) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, norm_mul]
    exact mul_le_one₀ ha1 (norm_nonneg _) hb1
  one_mem' := by
    refine ⟨A.one_mem, ?_⟩
    have e : (⟨1, A.one_mem⟩ : A) = 1 := rfl
    rw [e, map_one, norm_one]
  add_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.add_mem ha hb, ?_⟩
    have e : (⟨a + b, A.add_mem ha hb⟩ : A) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 hb1)
  zero_mem' := by
    refine ⟨A.zero_mem, ?_⟩
    have e : (⟨0, A.zero_mem⟩ : A) = 0 := rfl
    rw [e, map_zero, norm_zero]
    exact zero_le_one
  neg_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨A.neg_mem ha, ?_⟩
    have e : (⟨-a, A.neg_mem ha⟩ : A) = -⟨a, ha⟩ := rfl
    rw [e, map_neg, norm_neg]
    exact ha1

theorem norm_ev_le_one (A : Subring Ω) (ev : A →+* 𝕜) (R : Subalgebra ℤ Ω)
    (hR : ∀ x ∈ R, ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1) {t : Ω} (ht : t ∈ integralClosure R Ω) (hb : t ∈ A) :
    ‖ev ⟨t, hb⟩‖ ≤ 1 := by
  obtain ⟨f, hmon, hf⟩ := ht
  let ψ : R →+* A :=
    { toFun := fun r => ⟨r, (hR r r.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h1 : f.eval₂ ψ ⟨t, hb⟩ = 0 := by
    apply Subtype.ext
    exact (Polynomial.hom_eval₂ f ψ A.subtype ⟨t, hb⟩).trans hf
  have h2 : f.eval₂ (ev.comp ψ) (ev ⟨t, hb⟩) = 0 := by
    rw [← Polynomial.hom_eval₂, h1, map_zero]
  exact norm_le_one_of_monic_eval₂ (ev.comp ψ) (fun r => (hR r r.2).2) hmon h2

end Ring

section Pt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}

theorem isMultiHomog_X_single [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm b
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hb : b = k
  · subst hb
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (by simpa using h.symm)
    · simp
  · rw [Pi.single_eq_of_ne hb]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (congrArg Sigma.fst h).symm

theorem hasVal_coord [DecidableEq K] (k : K) (i : ι k) :
    Small.HasVal y (Pi.single k 1) (y ⟨k, i⟩) z (z ⟨k, i⟩) := by
  refine ⟨Pi.single k 1, 0, X ⟨k, i⟩, 1, isMultiHomog_X_single k i, ?_, fun b => ?_, by simp, by simp, by simp⟩
  · exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one
  · by_cases hb : b = k
    · subst hb
      simp
    · simp [Pi.single_eq_of_ne hb]

theorem hasVal_ratio_coord {k : K} (i c : ι k) (hy : y ⟨k, c⟩ ≠ 0) (hz : z ⟨k, c⟩ ≠ 0) :
    Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c⟩) z (z ⟨k, i⟩ / z ⟨k, c⟩) := by
  classical
  refine ⟨Pi.single k 1, Pi.single k 1, X ⟨k, i⟩, X ⟨k, c⟩, isMultiHomog_X_single k i, isMultiHomog_X_single k c,
    fun b => by simp, ?_, by simpa using hz, ?_⟩
  · simp only [aeval_X]
    field_simp
  · simp only [aeval_X]
    field_simp

theorem coord_ne_zero (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) (p : Σ k, ι k) (h : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  have hm : (X p : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (X p) = 0
    simp [mConeMap, h0]
  exact h (by simpa using hz.2 _ hm)

end Pt

theorem exists_hasVal_norm_le_supMet :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [NormedField 𝕜] [IsUltrametricDist 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → ∀ (A : Subring Ω) (ev : A →+* 𝕜) (a : K → ℤ), ∀ s ∈ chartLatNm y a 1, (∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k i, ∃ hb : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A, Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (ev ⟨_, hb⟩)) ∧ ∃ hb : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ A, Small.HasVal y 0 (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) z (ev ⟨_, hb⟩)) → ∃ w, Small.HasVal y a s z w ∧ ‖w‖ ≤ Small.supMet a z := by
  classical
  intro K _ ι _ Ω _ y 𝕜 _ _ z hz A ev a s hs H
  have hc : ∀ k, ∃ c : ι k, ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c⟩‖ := fun k => by
    obtain ⟨i0, -⟩ := hz.1 k
    haveI : Nonempty (ι k) := ⟨i0⟩
    exact Finite.exists_max (fun i => ‖z ⟨k, i⟩‖)
  choose c hc using hc
  have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have h1 := hc k i0
    rw [h0, norm_zero] at h1
    exact hi0 (norm_le_zero_iff.1 h1)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => coord_ne_zero hz _ (hzc k)
  obtain ⟨hr, hb, hv⟩ := H c hyc
  have hle : chartRingZ y c ≤ subalgebraOfSubring (unitBall A ev) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    obtain ⟨hb', hv'⟩ := hr k i
    have e := Small.ReadFinTest.hasVal_unique hz hv' (hasVal_ratio_coord i (c k) (hyc k) (hzc k))
    refine ⟨hb', ?_⟩
    rw [e, norm_div]
    exact div_le_one_of_le₀ (hc k i) (norm_nonneg _)
  have hn : ‖ev ⟨_, hb⟩‖ ≤ 1 := norm_ev_le_one A ev _ (fun x hx => hle hx) (hs c hyc) hb
  refine ⟨ev ⟨_, hb⟩ * ∏ k, z ⟨k, c k⟩ ^ a k, ?_, ?_⟩
  · have hp : ∀ k ∈ (Finset.univ : Finset K), Small.HasVal y (a k • (Pi.single k 1 : K → ℤ)) (y ⟨k, c k⟩ ^ a k) z
        (z ⟨k, c k⟩ ^ a k) := fun k _ => hv_zpow hz (hasVal_coord k (c k)) (hyc k) (hzc k) (a k)
    have h3 := hv_mul hv (hv_prod Finset.univ hp)
    have e1 : (0 : K → ℤ) + ∑ k, a k • (Pi.single k 1 : K → ℤ) = a := by
      funext b
      simp [Finset.sum_apply, Pi.single_apply]
    have e2 : (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ a k = s := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      have : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) * y ⟨k, c k⟩ ^ a k = 1 := fun k => by
        rw [← zpow_add₀ (hyc k)]
        simp
      rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_const_one, mul_one]
    rw [e1, e2] at h3
    exact h3
  · have hm : Small.supMet a z = ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := by
      unfold Small.supMet
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (hc k))
        (norm_le_pi_norm (fun i => z ⟨k, i⟩) (c k))]
    rw [norm_mul, norm_prod, hm]
    simp only [norm_zpow]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun k _ => by positivity) hn

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsWithConstantsMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_with_constants_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] [CharZero Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω₀) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω₀ Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω₀ Li) (L : CMType H ⊕ CMType H → Lat ξ Li) (bd : Ideal (MRing J)), IsCptGen ξ₀ → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ξ ≫ f = ξ₀ → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ s, (L s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s)))) → (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) → Cmp.IsSncModel y D.dim bd → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G)) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (_ : Algebra Ω₀ Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) (_ : AddCommGroup Li) (_ : Module Ω Li) (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module Ω₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (bd : Ideal (MRing J)), (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) ∧ ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) ∧ M.IsActOf t.act.act ρ ∧ (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) ∧ IsGenericFlag (Ω' := Ω) j V₀ b 1 ∧ (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) ∧ Cmp.IsSncModel y (Top.dimFl (CMType H) (D.p + D.q)) bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_flagStep | exact GlobalTheory.CompanionTheory.Ar.exists_flagStep | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_flagStep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsFiniteNonempty
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Comps

theorem finite_maximal_points (X : Type) [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    [QuasiSober X] [T0Space X] : {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Finite := by
  refine Set.Finite.of_injOn (f := fun x : X => closure {x}) (t := irreducibleComponents X) ?_ ?_
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents)
  · intro x hx
    have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
    have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
    have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
    have hg := hirr.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hg
    have hs : hirr.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hg.def]
      exact mem_irreducibleComponent
    have he := hx _ hs
    show closure {x} ∈ irreducibleComponents X
    rw [← he, hg.def]
    exact hZ
  · intro x _ y _ h
    exact (inseparable_iff_closure_eq.2 h).eq

theorem nonempty_maximal_points (X : Type) [TopologicalSpace X] [QuasiSober X] [T0Space X] [Nonempty X] :
    {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hg := hirr.isGenericPoint_genericPoint_closure
  rw [hcl.closure_eq] at hg
  refine ⟨hirr.genericPoint, fun x' hx' => ?_⟩
  have hm : Maximal IsIrreducible (irreducibleComponent x) := hZ
  have hsub : irreducibleComponent x ⊆ closure {x'} := by
    rw [← hg.def]
    exact hx'.closure_subset
  have hirr' : IsIrreducible (closure {x'}) := isIrreducible_singleton.closure
  have heq : closure {x'} = irreducibleComponent x := (hm.eq_of_subset hirr' hsub).symm
  exact (inseparable_iff_closure_eq.2 (heq.trans hg.def.symm)).eq

theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have key : ∀ τ : E →+* ℂ, Nat.card {i // (e.symm i).1 = τ} = m τ := by
    intro τ
    have e1 : {i // (e.symm i).1 = τ} ≃ Fin (m τ) :=
      (e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype τ)
    rw [Nat.card_congr e1, Nat.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [key]; simp [m, h]
  · rw [key]; simp [m, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}

theorem moduli_nonempty (hc : N1c) (Xo : Moduli D l) : Nonempty Xo.X := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
  · obtain ⟨f, -, -⟩ := Xo.rep (Sp (KA l)) (𝟙 _) inferInstance (GlobalTheory.Models.RankZero.zeroObj h l _)
    exact ⟨f (IsLocalRing.closedPoint (KA l))⟩
  · obtain ⟨g, ty, hty⟩ := exists_typeFn H D.p D.q
    obtain ⟨F⟩ := hc E H D l Xo (KA l).val.toRingHom g ty h rfl hty
    exact ⟨F.u ⟨0, F.n_pos⟩ 0 (IsLocalRing.closedPoint ℂ)⟩

theorem model_nonempty {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (h : Nonempty Xo.X) : Nonempty Y.X := by
  obtain ⟨x⟩ := h
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Xo.s) (g := spMap (IntermediateField.inclusion c.le).toRingHom) x (IsLocalRing.closedPoint c.F)
    (Subsingleton.elim _ _)
  exact ⟨Y.j z⟩

theorem finite_nonempty_maximal : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)),
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := model_nonempty Y (moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨finite_maximal_points Y.X, nonempty_maximal_points Y.X⟩

end GlobalTheory.CompanionTheory.Ar.Comps
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

open AlgebraicGeometry CategoryTheory

abbrev gen {X : Scheme.{0}} (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Spec (CommRingCat.of T.Fr) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ zV

def ReadsPt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (A : Subring Ω) (T : CDVR)
    (evT : A →+* T.Fr) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Prop :=
  ∀ a : A, ValAt ξ (gen T zV) (a : Ω) (evT a)

def TriIn {F EC : Type} [Field F] [AddCommGroup EC] [Module F EC] {r : ℕ} (u : Fin r → EC) (d : Fin r → F)
    (v : Fin r → EC) : Prop :=
  ∀ i, ∃ cf : Fin r → F, cf i = d i ∧ (∀ j, i < j → cf j = 0) ∧ v i = ∑ j, cf j • u j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

def IsFrameVec (Or : RootOrigin Y SS RM Fx) {T : CDVR} (io : c.F →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type} [AddCommGroup EC] [Module T.Fr EC]
    (MC : LieModel Or.𝔐.t.G (gen T zV) EC) (w : EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)) : Prop :=
  letI := io.toAlgebra
  (MC.pt w).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Small.labelFin Dw s i)

def lieEig (Or : RootOrigin Y SS RM Fx) {T : CDVR} {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type}
    [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] (MC : LieModel Or.𝔐.t.G (gen T zV) EC)
    [IsScalarTower T.V T.Fr EC] (ρC : 𝓞 E →+* Module.End T.Fr EC) (σ : 𝓞 E →+* T.V) : Submodule T.V EC :=
  Or.𝔐.M.fibAt Or.𝔐.M.lat zV MC ⊓ (eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

