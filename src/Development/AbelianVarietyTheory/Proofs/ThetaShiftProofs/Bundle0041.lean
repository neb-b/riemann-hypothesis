module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralElemOfIsAlgebraicInt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieComb
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsHomogeneousOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTermWeightZeroSectionLevelOneFormalSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0040

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumArcLieBasis
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ.DatumBasis

open MonoidalCategory CartesianMonoidalCategory MonObj Matrix

section Coord

open GlobalTheory.Serre

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (a : OAct O G)
  {g : ℕ} {B : Fin g → (epsR R ⟶ G)} (hB : IsLieBasis B)
include hB

theorem comb_iff_symm (z : Fin g → R) (w : epsR R ⟶ G) :
    IsLieComb z B w ↔ w = ((Lie.basis a hB).equivFun.symm z).hom := by
  have e : B = fun i => (Lie.basis a hB i).hom := funext fun i => (Lie.hom_basis hB i).symm
  rw [Module.Basis.equivFun_symm_apply, ← Lie.isLieComb_iff, ← e]


include a in
theorem exists_comb (z : Fin g → R) : ∃ w, IsTangent w ∧ IsLieComb z B w :=
  ⟨_, Lie.isTangent _, (comb_iff_symm a hB z _).2 rfl⟩


include a in
theorem comb_coord {m : ℕ} {U : Fin m → Fin g → R} {u : Fin m → (epsR R ⟶ G)} (hU : ∀ k, IsLieComb (U k) B (u k))
    {z : Fin g → R} {w : epsR R ⟶ G} (hz : IsLieComb z B w) (cf : Fin m → R) :
    IsLieComb cf u w ↔ z = ∑ k, cf k • U k := by
  obtain rfl : u = fun k => ((Lie.basis a hB).equivFun.symm (U k)).hom :=
    funext fun k => (comb_iff_symm a hB _ _).1 (hU k)
  obtain rfl := (comb_iff_symm a hB _ _).1 hz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Lie.isLieComb_iff, ← (Lie.basis a hB).equivFun.symm.injective.eq_iff, map_sum]
  simp only [map_smul]
  exact ⟨fun h => Lie.ext h, fun h => congrArg Lie.hom h⟩

theorem eig_coord {x : O} {M : Matrix (Fin g) (Fin g) R} (hM : ∀ i, IsLieComb (M i) B (B i ≫ a.act x))
    {z : Fin g → R} {w : epsR R ⟶ G} (hz : IsLieComb z B w) (s : R) :
    (w ≫ a.act x).left = spMap (epsScaleR s) ≫ w.left ↔ z ᵥ* M = s • z := by
  obtain rfl := (comb_iff_symm a hB _ _).1 hz
  have h1 : ∀ i, x • Lie.basis a hB i = (Lie.basis a hB).equivFun.symm (M i) := fun i => Lie.ext (by
    rw [Lie.hom_act_smul, Lie.hom_basis]; exact (comb_iff_symm a hB _ _).1 (hM i))
  have h2 : x • (Lie.basis a hB).equivFun.symm z = (Lie.basis a hB).equivFun.symm (z ᵥ* M) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.vecMul_eq_sum, map_sum, Module.Basis.equivFun_symm_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm x, h1, map_smul]
  rw [← Lie.hom_act_smul, ← Lie.hom_smul_left, h2, ← map_smul,
    ← (Lie.basis a hB).equivFun.symm.injective.eq_iff]
  exact ⟨fun h => Lie.ext (Over.OverMorphism.ext h), fun h => by rw [h]⟩

theorem eigBasis_coord {M : O → Matrix (Fin g) (Fin g) R} (hM : ∀ x i, IsLieComb (M x i) B (B i ≫ a.act x))
    {m : ℕ} {U : Fin m → Fin g → R} {u : Fin m → (epsR R ⟶ G)} (hU : ∀ k, IsLieComb (U k) B (u k)) (ρ : O → R) :
    (∀ w : epsR R ⟶ G, IsTangent w → (∀ x, (w ≫ a.act x).left = spMap (epsScaleR (ρ x)) ≫ w.left) →
      ∃! cf : Fin m → R, IsLieComb cf u w) ↔
    ∀ z : Fin g → R, (∀ x, z ᵥ* M x = ρ x • z) → ∃! cf : Fin m → R, z = ∑ k, cf k • U k := by
  constructor
  · intro h z hz
    obtain ⟨w, hw, hc⟩ := exists_comb a hB z
    exact (existsUnique_congr (comb_coord a hB hU hc)).1
      (h w hw fun x => (eig_coord a hB (hM x) hc _).2 (hz x))
  · intro h w hw he
    obtain ⟨z, hc, -⟩ := hB.2 w hw
    exact (existsUnique_congr (comb_coord a hB hU hc)).2
      (h z fun x => (eig_coord a hB (hM x) hc _).1 (he x))

end Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem dual_over {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) :
    spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap φ := by
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  exact RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

section Descent

variable {R S : Type} [CommRing R] [CommRing S] {io : R →+* S} {t : SAB H (Sp R)} {t' : SAB H (Sp S)}
  (m : SABMap t' t (spMap io))

theorem exists_bc (v : epsR R ⟶ t.G) : ∃ q : epsR S ⟶ t'.G, q.left ≫ m.φ = spMap (dualMap io) ≫ v.left := by
  have hv : v.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w v
  have cond : (spMap (dualMap io) ≫ v.left) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ spMap io := by
    rw [Category.assoc, hv, dual_over]
  exact ⟨Over.homMk (m.cart.1.lift _ _ cond) (m.cart.1.lift_snd _ _ _), m.cart.1.lift_fst _ _ _⟩

theorem tangent_of_bc [IsDomain R] (hio : Function.Injective io) {v : epsR R ⟶ t.G} {q : epsR S ⟶ t'.G}
    (h : q.left ≫ m.φ = spMap (dualMap io) ≫ v.left) (hq : IsTangent q) : IsTangent v := by
  have hv : v.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) := Over.w v
  have := t.semi.separated
  have : IsDominant (spMap io) := ⟨by
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical io).2 ?_
    rw [(RingHom.injective_iff_ker_eq_bot io).1 hio]; exact bot_le⟩
  refine ext_of_isDominant_of_isSeparated t.G.hom ?_ (spMap io) ?_
  · have a : η[t.G].left ≫ t.G.hom = 𝟙 _ := Over.w η[t.G]
    rw [Category.assoc, hv, a, ← spMap_comp]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; simp
    rw [this]
    exact Spec.map_id _
  · have e := m.cm.e_comm
    rw [m.base] at e
    have sq : spMap io ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom =
        spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (dualMap io) := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext fun a => by simp [dualMap]
    rw [← Category.assoc, sq, Category.assoc, ← h, ← Category.assoc]
    exact (congrArg (· ≫ m.φ) hq).trans e

end Descent

theorem eigBasis_descent {K S : Type} [Field K] [CommRing S] [Nontrivial S] {io : PowerSeries K →+* S}
    {t : SAB H (Sp (PowerSeries K))} {t' : SAB H (Sp S)} (m : SABMap t' t (spMap io))
    {g : ℕ} {B : Fin g → (epsR (PowerSeries K) ⟶ t.G)} (hB : IsLieBasis B) {M : 𝓞 E → Matrix (Fin g) (Fin g) K}
    (hM : ∀ x i, IsLieComb (fun k => PowerSeries.C (R := K) (M x i k)) B (B i ≫ t.act.act x))
    {n : ℕ} {U : Fin n → Fin g → K} {v : Fin n → (epsR (PowerSeries K) ⟶ t.G)}
    (hU : ∀ k, IsLieComb (fun i => PowerSeries.C (R := K) (U k i)) B (v k)) {q : Fin n → (epsR S ⟶ t'.G)}
    (hq : ∀ k, (q k).left ≫ m.φ = spMap (dualMap io) ≫ (v k).left) (ρ : 𝓞 E → K)
    (he : ∀ k x, (q k ≫ t'.act.act x).left = spMap (epsScaleR (io (PowerSeries.C (R := K) (ρ x)))) ≫ (q k).left)
    (hb : ∀ w : epsR S ⟶ t'.G, IsTangent w →
      (∀ x, (w ≫ t'.act.act x).left = spMap (epsScaleR (io (PowerSeries.C (R := K) (ρ x)))) ≫ w.left) →
      ∃! cf : Fin n → S, IsLieComb cf q w) :
    (∀ k x, (v k ≫ t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := K) (ρ x))) ≫ (v k).left) ∧
    ∀ w : epsR (PowerSeries K) ⟶ t.G, IsTangent w →
      (∀ x, (w ≫ t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := K) (ρ x))) ≫ w.left) →
      ∃! cf : Fin n → PowerSeries K, IsLieComb cf v w := by
  let _ : Algebra K S := (io.comp (PowerSeries.C (R := K))).toAlgebra
  have := t.semi.smooth
  choose B' hB' using fun i => exists_bc m (B i)
  have hBS : IsLieBasis B' := Chart.isLieBasis_baseChange io m.cart hB hB'
  have hMS : ∀ x i, IsLieComb (((M x).map (algebraMap K S)) i) B' (B' i ≫ t'.act.act x) := fun x i =>
    Chart.comb_baseChange io m.cart (hM x i) hB' (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc, hB', Category.assoc]; rfl)
  have hUS : ∀ k, IsLieComb (fun j => algebraMap K S (U k j)) B' (q k) := fun k =>
    Chart.comb_baseChange io m.cart (hU k) hB' (hq k)
  have hMR : ∀ x i, IsLieComb (((M x).map (algebraMap K (PowerSeries K))) i) B (B i ≫ t.act.act x) := hM
  have hUR : ∀ k, IsLieComb (fun j => algebraMap K (PowerSeries K) (U k j)) B (v k) := hU
  have key : ∀ (T : Type) [CommRing T] (f : K →+* T) (k : Fin n) (x : 𝓞 E) (j : Fin g),
      f ((U k ᵥ* M x) j) = ((fun j => f (U k j)) ᵥ* (M x).map f) j := fun T _ f k x j =>
    RingHom.map_vecMul f (M x) (U k) j
  have hK : ∀ k x, U k ᵥ* M x = ρ x • U k := fun k x => funext fun j => (algebraMap K S).injective (by
    rw [key, (eig_coord t'.act hBS (hMS x) (hUS k) (algebraMap K S (ρ x))).1 (he k x)]
    simp)
  refine ⟨fun k x => (eig_coord t.act hB (hMR x) (hUR k) (algebraMap K _ (ρ x))).2 (funext fun j => ?_),
    (eigBasis_coord t.act hB hMR hUR fun x => algebraMap K _ (ρ x)).2 ?_⟩
  · rw [← key, hK]; simp
  · exact (GlobalTheory.commonEigenvectors_flat_baseChange K (𝓞 E) g n M ρ).1 S U hK
      ((eigBasis_coord t'.act hBS hMS hUS fun x => algebraMap K S (ρ x)).1 hb) (PowerSeries K)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Push

variable {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {t' : SAB H (Sp S)} (m : SABMap t' Xo.univ.t x)

theorem tan_iff (w : epsR S ⟶ t'.G) : IsTanAt x (w.left ≫ m.φ) ↔ IsTangent w := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  exact ⟨fun h => (Chart.tan_push m.cart w).2 h.2,
    fun h => ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hw], (Chart.tan_push m.cart w).1 h⟩⟩

theorem eig_iff (w : epsR S ⟶ t'.G) (a : 𝓞 E) (s : S) :
    (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul s) ≫ w.left ≫ m.φ ↔
      (w ≫ t'.act.act a).left = spMap (epsScaleR s) ≫ w.left := by
  have hw : w.left ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) := Over.w w
  have e : (w.left ≫ m.φ) ≫ (Xo.univ.t.act.act a).left = (w ≫ t'.act.act a).left ≫ m.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc, m.act]
  have sc : spMap (epsScaleR s) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
    rw [← spMap_comp]
    congr 1
    ext r <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  constructor
  · intro h
    apply m.cart.1.hom_ext
    · rw [Category.assoc]; exact h
    · rw [Over.w, Category.assoc, hw, sc]; rfl
  · intro h
    rw [h, Category.assoc]; rfl

theorem comb_iff {n : ℕ} (v : Fin n → (epsR S ⟶ t'.G)) (cf : Fin n → S) (w : epsR S ⟶ t'.G) :
    IsCombAt x (fun i => (v i).left ≫ m.φ) cf (w.left ≫ m.φ) ↔ IsLieComb cf v w :=
  (Chart.comb_push m.cart cf v w).symm

end Push

end GlobalTheory.ArcQ.DatumBasis


open GlobalTheory.ArcQ.DatumBasis in
theorem GlobalTheory.ArcQ.arcDatum_arcLieBasis : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁), (∀ τ k, GtTanR (d.e τ k)) → ArcLieBasis d.W d.e := by
  intro hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ d htan
  have hNormal := @_root_.GlobalTheory.ArcQ.exists_normalForm
    hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ _ d
  obtain ⟨ζ, -, -, -, hN, -⟩ := hNormal
  obtain ⟨y, hy, -⟩ := hN htan
  obtain ⟨-, G, m1, m2, -, -, -, -, -, -, h, -⟩ := hy
  choose v p hv hp1 hp2 hp3 using h
  let q : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (ArcS Dw K₁) ⟶ G.G) := fun τ k => Over.homMk (p τ k) (hp3 τ k)
  have hq1 : ∀ τ k, (q τ k).left ≫ m1.φ = y.u τ k := hp1
  have hq2 : ∀ τ k, (q τ k).left ≫ m2.φ = spMap (dualMap (arcι Dw K₁)) ≫ (v τ k).left := hp2
  have hι : Function.Injective (arcι Dw K₁) := (GlobalTheory.ArcConst.algebraMap_injective Dw K₁).comp
    ((MvPolynomial.C_injective _ _).comp HahnSeries.ofPowerSeries_injective)
  have := GlobalTheory.ArcConst.isDomain Dw K₁
  have tq : ∀ τ k, IsTangent (q τ k) := fun τ k => (tan_iff m1 _).1 (hq1 τ k ▸ y.tan τ k)
  have tv : ∀ τ k, IsTangent (v τ k) := fun τ k => tangent_of_bc m2 hι (hq2 τ k) (tq τ k)
  obtain ⟨g, e₀, B, M, h₀, hB, hc, hM⟩ := GlobalTheory.ConstLie.exists_const_basis hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W
  have hU : ∀ τ k, ∃ U : Fin g → K₁, IsLieComb (fun i => PowerSeries.C (R := K₁) (U i)) B (v τ k) := fun τ k => by
    obtain ⟨U, hU, -⟩ := hc (d.e τ k)
      (((GlobalTheory.ConstLie.main hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W (d.e τ k)).2 _ (hv τ k)).2 (tv τ k))
    exact ⟨U, (GlobalTheory.ConstLin.lieImg_iff_isLieComb hL.globalFns E H Dw l Xo c _ _ d.Y K₁ _ _ d.χ d.W g U e₀ (d.e τ k) B (v τ k)
      (fun i => (h₀ i).2) hU).1 (hv τ k)⟩
  choose U hU using hU
  have eig : ∀ (τ : E →+* ℂ) (w : epsR (ArcS Dw K₁) ⟶ G.G), IsEigAt c τ (w.left ≫ m1.φ) ↔
      ∀ x : 𝓞 E, (w ≫ G.act.act x).left = spMap (epsScaleR (arcι Dw K₁
        (PowerSeries.C (R := K₁) (algebraMap c.F K₁ (embK c τ x))))) ≫ w.left :=
    fun τ w => forall_congr' fun x => by rw [← arcS_pin]; exact eig_iff m1 w x _
  refine ⟨v, hv, fun τ => ?_⟩
  have hu : y.u τ = fun k => (q τ k).left ≫ m1.φ := funext fun k => (hq1 τ k).symm
  obtain ⟨a₁, a₂⟩ := eigBasis_descent m2 hB hM (hU τ) (hq2 τ) (fun x => algebraMap c.F K₁ (embK c τ x))
    (fun k => (eig τ _).1 (hq1 τ k ▸ y.eig τ k)) fun w hw he =>
      (existsUnique_congr fun cf => by rw [hu]; exact comb_iff m1 (q τ) cf w).1
        (y.basis τ _ ((tan_iff m1 w).2 hw) ((eig τ w).2 he))
  exact ⟨fun k => ⟨tv τ k, a₁ k⟩, a₂⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointValueIsHomogeneousLetters
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_letters_equivariant (h1 : Out.Laws) (h2 : Out.Laws2) (hev : GlobalTheory.Reg.EvLaws Xo c)
    {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (hY : Mono Y.j)
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] {b₀ : O →+* K₁} {A : ArcIn Dw l β K₁ b₀}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X} (W : Wit Y A χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt A.D₀ (epsR K₁)) (th : A.D₀.P.L.Sec) (hth : ThNZ th)
    (ζ : K₁) (y₀ yF : FrPt Xo c (ArcS Dw K₁)) (hy₀ : IsArcFr W e th (arcι Dw K₁) y₀)
    (hchg : FrChg (letM Dw K₁) (cst Dw ζ) y₀ yF)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c) (hF : F ∈ sec Xo c a n)
    (T : Type) [Field T] (φ ψ : ArcS Dw K₁ →+* T) (b : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T)
    (hφψ : ∀ g : LaurentSeries K₁, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C g)) =
      ψ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) _ (MvPolynomial.C g)))
    (hb : ∀ τ i j, i < j → b τ i j = 0)
    (hX : ∀ τ i k, ψ (arcX Dw K₁ τ i k) = ∑ j, b τ i j * φ (arcX Dw K₁ τ j k)) :
    ψ (evR Xo c F yF) = (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) * φ (evR Xo c F yF) := by
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  obtain ⟨hdom, -, -, hconst⟩ := GlobalTheory.ArcConst.algebraic_const E H Dw K₁
  obtain ⟨f₀, hf₀⟩ := hconst c.F (algebraMap c.F (ArcS Dw K₁))
  have hι : φ.comp (arcι Dw K₁) = ψ.comp (arcι Dw K₁) := RingHom.ext fun p => hφψ _
  letI : Algebra c.F T := (φ.comp (algebraMap c.F (ArcS Dw K₁))).toAlgebra
  let φ' : ArcS Dw K₁ →ₐ[c.F] T := { φ with commutes' := fun _ => rfl }
  let ψ' : ArcS Dw K₁ →ₐ[c.F] T :=
    { ψ with
      commutes' := fun r => by
        change ψ (algebraMap c.F (ArcS Dw K₁) r) = φ (algebraMap c.F (ArcS Dw K₁) r)
        rw [hf₀]
        exact (RingHom.congr_fun hι _).symm }
  obtain ⟨y₁, hy₁⟩ := hev.bc _ _ φ' y₀
  obtain ⟨y₂, hy₂⟩ := hev.bc _ _ ψ' y₀
  obtain ⟨z₁, hz₁⟩ := hev.bc _ _ φ' yF
  obtain ⟨z₂, hz₂⟩ := hev.bc _ _ ψ' yF
  have hS := GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c O β Y K₁ b₀ A χ W e th hth _ _ y₀ hy₀
  have a₁ : IsArcFr W e th (φ.comp (arcι Dw K₁)) y₁ := hS.2 hY T φ' y₁ hy₁
  have a₂ : IsArcFr W e th (ψ.comp (arcι Dw K₁)) y₂ := hS.2 hY T ψ' y₂ hy₂
  rw [← hι] at a₂
  obtain rfl : y₂ = y₁ :=
    (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c O β Y K₁ b₀ A χ W e th hth _ _ y₁ a₁).1 hY y₂ a₂
  have cS := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c (ArcS Dw K₁)
  have cT := GlobalTheory.Frames.frChg_calculus E H Dw l Xo c T
  have c₁ := (cS.2.2.1 T φ' _ _ _ _ _ _ hchg hy₁).1 hz₁
  have c₂ := (cS.2.2.1 T ψ' _ _ _ _ _ _ hchg hy₂).1 hz₂
  have hM : ∀ τ, (letM Dw K₁ τ).map ψ' = b τ * (letM Dw K₁ τ).map φ' := fun τ => by
    ext i k
    exact hX τ i k
  have hζ : ψ' (cst Dw ζ) = 1 * φ' (cst Dw ζ) := by
    rw [one_mul]
    exact (RingHom.congr_fun hι _).symm
  rw [funext hM, hζ] at c₂
  have c₃ : FrChg b 1 z₁ z₂ := (cT.1 _ b _ 1 _ _ _ c₁).2 c₂
  have hbu : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
    have hu := ((GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c T b 1 z₁).2.2.1 z₂ c₃).1 τ
    have htri : (b τ).IsLowerTriangular := fun i j hij => hb τ i j hij
    exact (htri.det_ne_zero_iff.mp hu.ne_zero) i
  let t : Ix Dw → Tˣ := fun o => match o with
    | none => 1
    | some x => Units.mk0 (b x.1 x.2 x.2) (hbu x.1 x.2)
  have hbor : FrBor t z₁ z₂ := (cT.2.2.2 t z₁ z₂).2 ⟨b, fun _ _ => rfl, hb, c₃⟩
  have eS := (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hF (ArcS Dw K₁)).1
  have eT := ((GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hev a n F hF T).2 inferInstance).1 t z₁ z₂ hbor
  rw [eS T φ' yF z₁ hz₁, eS T ψ' yF z₂ hz₂] at eT
  have hw : wchar (ex Dw a n) t = ∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ)) := by
    rw [wchar, Fintype.prod_option, Fintype.prod_sigma]
    simp [t, ex]
  rw [hw] at eT
  exact eT

theorem ArcDatum.exists_normal_tangent (h1 : Out.Laws) (h2 : Out.Laws2)
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) :
    ∃ (ζ : K₁) (e₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt (d.a.restrict (c.V d.Wp).subtype).D₀ (epsR K₁))
      (y₀ : FrPt Xo c (ArcS Dw K₁)), IsArcFr d.W e₀ d.th (arcι Dw K₁) y₀ ∧
        FrChg (letM Dw K₁) (cst Dw ζ) y₀ d.yF := by
  obtain ⟨ζ, -, -, -, -, e₀, y₀, -, hy₀, hc⟩ := GlobalTheory.ArcQ.exists_normalForm h1 h2 E H Dw l Xo c K₁ d
  exact ⟨ζ, e₀, y₀, hy₀, hc⟩

theorem evR_arc_isHomogeneous : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (K₁ : Type) [Field K₁] [Algebra c.F K₁] [Algebra c.F (ArcS Dw K₁)] (d : ArcDatum Xo c K₁) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries K₁), algebraMap _ (ArcS Dw K₁) P = evR Xo c F d.yF ∧ P.IsHomogeneous (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))) := by
  intro h1 h2 E _ _ _ H Dw l Xo c hev K₁ _ _ _ d a n F hF
  obtain ⟨ζ, e₀, y₀, hy₀, hc⟩ := d.exists_normal_tangent h1 h2
  have hth : ThNZ d.th := by
    obtain ⟨_, _, _, _, hne, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.nonzero_generates h1 h2 K₁ _ d.th).1.1 hne
  exact GlobalTheory.BorelAlg.exists_isHomogeneous_of_equivariant E H Dw K₁ a _ fun T _ φ ψ b hφψ hb hX =>
    evR_letters_equivariant h1 h2 hev (GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)) d.W e₀ d.th hth ζ y₀ d.yF hy₀ hc
      a n F hF T φ ψ b hφψ hb hX

end GlobalTheory.ArcQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantTermWeightZeroSectionLevelOneFormalSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTermWeightZero_section_levelOne_formalSum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x) (θ : (Fin Λ.A.gB → ℂ) → ℂ), ThetaHyp W th σ fam → θ ∈ Λ.A.Theta 1 0 → Λ.u.IsFn th θ → Ξ.Vals σ (fun v => Λ.A.FSum 1 0 θ v) := by
  first | exact @GlobalTheory.ArcPts.WeightZero.vals_FSum | exact GlobalTheory.ArcPts.WeightZero.vals_FSum | (intros; apply GlobalTheory.ArcPts.WeightZero.vals_FSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroupStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constantLieBasis_arcGroup : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ), ∃ (g : ℕ) (e : Fin g → Out.GtPt a.D₀ (epsR A)) (v : Fin g → (epsR (PowerSeries A) ⟶ W.t.G)) (M : 𝓞 E → Matrix (Fin g) (Fin g) A), (∀ i, GtTanR (e i) ∧ LieImg W (e i) (v i)) ∧ IsLieBasis v ∧ (∀ ν, GtTanR ν → ∃! cf : Fin g → A, GtComb cf e ν) ∧ ∀ (x : 𝓞 E) i, IsLieComb (fun k => PowerSeries.C (R := A) (M x i k)) v (v i ≫ W.t.act.act x) := by
  first | exact @GlobalTheory.ConstLie.exists_const_basis | exact GlobalTheory.ConstLie.exists_const_basis | (intros; apply GlobalTheory.ConstLie.exists_const_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GenericPointsConstantPointsFormalSumValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoints_constantPoints_formalSum_values : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (b : O →+* ℂ) (a : ArcIn D l β ℂ b) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (Ξ : ConstPts W Λ) , ∃ Φ : GenPts Λ.A W.t gen, Ξ.IsGen Φ := by
  first | exact @GlobalTheory.GenericPoints.main | exact GlobalTheory.GenericPoints.main | (intros; apply GlobalTheory.GenericPoints.main <;> assumption)
end

