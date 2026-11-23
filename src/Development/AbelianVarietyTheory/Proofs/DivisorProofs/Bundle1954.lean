module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenChartAffineOpenWithin
section
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open Matrix

section Alg

theorem exists_factor_idem {L : Type} [Field L] {n m : ℕ} (e : Matrix (Fin n) (Fin n) L) (he : e * e = e)
    (N : Submodule L (Fin n → L)) (hN : ∀ v, v ∈ N ↔ e.mulVec v = v) (hr : Module.finrank L N = m) :
    ∃ (U : Matrix (Fin n) (Fin m) L) (V : Matrix (Fin m) (Fin n) L), U * V = e ∧ V * U = 1 := by
  classical
  let b : Module.Basis (Fin m) L N := Module.finBasisOfFinrankEq L N hr
  have hmem : ∀ v, e.mulVec v ∈ N := fun v => (hN _).2 (by rw [Matrix.mulVec_mulVec, he])
  let P : (Fin n → L) →ₗ[L] N := e.mulVecLin.codRestrict N hmem
  refine ⟨LinearMap.toMatrix' (N.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ P), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have : (N.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ P) = e.mulVecLin := by
      apply LinearMap.ext
      intro v
      simp [P, LinearMap.codRestrict_apply]
      rfl
    rw [this]
    exact LinearMap.toMatrix'_toLin' e
  · rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ P) ∘ₗ (N.subtype ∘ₗ b.equivFun.symm.toLinearMap) = LinearMap.id := by
      apply LinearMap.ext
      intro a
      have h1 : P (b.equivFun.symm a : N) = b.equivFun.symm a :=
        Subtype.ext ((hN _).1 (b.equivFun.symm a).2)
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Submodule.coe_subtype, h1,
        LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
    rw [this, LinearMap.toMatrix'_id]

theorem sum_minors_of_factor {T : Type} [CommRing T] {n m : ℕ} (U : Matrix (Fin n) (Fin m) T)
    (V : Matrix (Fin m) (Fin n) T) (h : V * U = 1) :
    ∑ S : Set.powersetCard (Fin n) m,
      ((U * V).submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1 := by
  have h0 := GlobalTheory.det_mul_eq_sum_minors V U
  rw [h, det_one] at h0
  rw [h0]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, det_mul, mul_comm]

theorem det_smul_of_factor {T : Type} [CommRing T] {n m : ℕ} (U : Matrix (Fin n) (Fin m) T)
    (V : Matrix (Fin m) (Fin n) T) (s : Fin m → Fin n) :
    ((U * V).submatrix s s).det • (U * V) =
      (U * V).submatrix id s * ((U * V).submatrix s s).adjugate * (U * V).submatrix s id := by
  rw [Matrix.submatrix_mul _ _ s id s Function.bijective_id, Matrix.submatrix_mul _ _ id id s Function.bijective_id,
    Matrix.submatrix_mul _ _ s id id Function.bijective_id, adjugate_mul_distrib, det_mul]
  simp only [Matrix.submatrix_id_id]
  have e1 : U * V.submatrix id s * ((V.submatrix id s).adjugate * (U.submatrix s id).adjugate) *
      (U.submatrix s id * V) = U * (V.submatrix id s * (V.submatrix id s).adjugate) *
        ((U.submatrix s id).adjugate * U.submatrix s id) * V := by
    simp only [Matrix.mul_assoc]
  rw [e1, mul_adjugate, adjugate_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_comm]

theorem idem_minors {R L : Type} [CommRing R] [Field L] (φ : R →+* L) (hφ : Function.Injective φ) {n m : ℕ}
    (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) (N : Submodule L (Fin n → L))
    (hN : ∀ v, v ∈ N ↔ (e.map φ).mulVec v = v) (hr : Module.finrank L N = m) :
    (∑ S : Set.powersetCard (Fin n) m, (e.submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1) ∧
      ∀ s : Fin m → Fin n, (e.submatrix s s).det • e = e.submatrix id s * (e.submatrix s s).adjugate *
        e.submatrix s id := by
  obtain ⟨U, V, hUV, hVU⟩ := exists_factor_idem (e.map φ) (by rw [← Matrix.map_mul, he]) N hN hr
  have hdet : ∀ s : Fin m → Fin n, φ (e.submatrix s s).det = ((e.map φ).submatrix s s).det := fun s => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]
  refine ⟨hφ ?_, fun s => Matrix.map_injective hφ ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one]
    simp only [hdet, ← hUV]
    exact sum_minors_of_factor U V hVU
  · dsimp only
    have h2 := det_smul_of_factor U V s
    rw [hUV] at h2
    have hs : ((e.submatrix s s).det • e).map φ = φ (e.submatrix s s).det • e.map φ := by
      ext i j; simp
    have ha : (e.submatrix s s).adjugate.map φ = ((e.map φ).submatrix s s).adjugate := by
      rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, Matrix.submatrix_map]
    rw [hs, hdet, h2, Matrix.map_mul, Matrix.map_mul, ← Matrix.submatrix_map, ← Matrix.submatrix_map, ha]

theorem exists_split {R S : Type} [CommRing R] [CommRing S] {n m : ℕ} (e : Matrix (Fin n) (Fin n) R)
    (he : e * e = e) (s : Fin m → Fin n)
    (hid : (e.submatrix s s).det • e = e.submatrix id s * (e.submatrix s s).adjugate * e.submatrix s id)
    (φ : R →+* S) (hu : IsUnit (φ (e.submatrix s s).det)) :
    ∃ (u : Matrix (Fin n) (Fin m) S) (w : Matrix (Fin m) (Fin n) S), w * u = 1 ∧ u * w = e.map φ := by
  refine ⟨(e.submatrix id s).map φ,
    (hu.unit⁻¹ : Sˣ).val • ((e.submatrix s s).adjugate * e.submatrix s id).map φ, ?_, ?_⟩
  · have h1 : e.submatrix s id * e.submatrix id s = e.submatrix s s := by
      rw [← Matrix.submatrix_mul _ _ s id s Function.bijective_id, he]
    rw [Matrix.smul_mul, ← Matrix.map_mul, Matrix.mul_assoc, h1, adjugate_mul]
    have hs : ((e.submatrix s s).det • (1 : Matrix (Fin m) (Fin m) R)).map φ =
        φ (e.submatrix s s).det • (1 : Matrix (Fin m) (Fin m) S) := by
      ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [hs, smul_smul, IsUnit.val_inv_mul, one_smul]
  · rw [Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.mul_assoc, ← hid]
    have hs : ((e.submatrix s s).det • e).map φ = φ (e.submatrix s s).det • e.map φ := by
      ext i j; simp
    rw [hs, smul_smul, IsUnit.val_inv_mul, one_smul]

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pm_minors (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : MChart Y) (σ : E →+* ℂ) :
    LowRank.pm p M σ * LowRank.pm p M σ = LowRank.pm p M σ ∧
    (∑ S : Set.powersetCard (Fin M.n) (Dw.mult σ),
      ((LowRank.pm p M σ).submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1) ∧
      ∀ s : Fin (Dw.mult σ) → Fin M.n, ((LowRank.pm p M σ).submatrix s s).det • LowRank.pm p M σ =
        (LowRank.pm p M σ).submatrix id s * ((LowRank.pm p M σ).submatrix s s).adjugate *
          (LowRank.pm p M σ).submatrix s id := by
  obtain ⟨L, _, _, y, h, hy, hi⟩ := LowRank.genIn_id Y M
  obtain ⟨h1, h2⟩ := LowRank.pm_gen p M σ hy h
  have he : LowRank.pm p M σ * LowRank.pm p M σ = LowRank.pm p M σ :=
    Matrix.map_injective hi (Matrix.map_mul.trans h2)
  obtain ⟨Λ⟩ := MChart.nonempty_lift E H Dw l Xo c c.F (RingHom.id c.F) Y M L (ev _ M.U h) y hy
    (spMap_ev _ M.hU h).symm
  let N : Submodule L (Fin M.n → L) := Module.End.eigenspace ((LowRank.pm p M σ).map (ev _ M.U h)).mulVecLin 1
  have hN : ∀ v, v ∈ N ↔ ((LowRank.pm p M σ).map (ev _ M.U h)).mulVec v = v := fun v =>
    Module.End.mem_eigenspace_iff.trans (by rw [one_smul]; rfl)
  exact ⟨he, idem_minors _ hi _ he N hN
    (finrank_chart_eig E H Dw l Xo c c.F (RingHom.id c.F) Y M L _ _ Λ σ N fun v => (hN v).trans (h1 v).symm)⟩

theorem exists_eCh_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : GChart Y)
    (x : Y.X), x ∈ M.U → ∀ W : Y.X.Opens, x ∈ W → ∃ k : ECh Y p, k.M = M ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ W := by
  intro E _ _ _ H Dw l Xo c Y p M x hx W hW
  classical
  have ex : ∀ σ : E →+* ℂ, ∃ s : Fin (Dw.mult σ) → Fin M.n,
      Y.X.evaluation M.U x hx ((LowRank.pm p M.toMChart σ).submatrix s s).det ≠ 0 := fun σ => by
    by_contra h
    push_neg at h
    have := congrArg (Y.X.evaluation M.U x hx) (pm_minors Y p M.toMChart σ).2.1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one, Finset.sum_eq_zero fun S _ => h _] at this
    exact zero_ne_one this
  choose s hs using ex
  let d := fun σ => ((LowRank.pm p M.toMChart σ).submatrix (s σ) (s σ)).det
  have hxf : x ∈ Y.X.basicOpen (∏ σ, d σ) := by
    refine (Y.X.evaluation_ne_zero_iff_mem_basicOpen x hx _).1 ?_
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun σ _ => hs σ
  obtain ⟨g, hg, hxg⟩ := M.hU.exists_basicOpen_le (V := W ⊓ Y.X.basicOpen (∏ σ, d σ)) ⟨x, hW, hxf⟩ hx
  have hle : Y.X.basicOpen g ≤ M.U := Y.X.basicOpen_le g
  have hVf : Y.X.basicOpen g ≤ Y.X.basicOpen (∏ σ, d σ) := hg.trans inf_le_right
  have hf : IsUnit (resG Y.X hle (∏ σ, d σ)) := by
    have h1 : IsUnit (resG Y.X (Y.X.basicOpen_le (∏ σ, d σ)) (∏ σ, d σ)) :=
      RingedSpace.isUnit_res_basicOpen Y.X.toRingedSpace _
    have h2 : resG Y.X hle (∏ σ, d σ) = resG Y.X hVf (resG Y.X (Y.X.basicOpen_le (∏ σ, d σ)) (∏ σ, d σ)) := by
      simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [h2]
    exact h1.map _
  have hu : ∀ σ, IsUnit (resG Y.X hle (d σ)) := fun σ =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem d (Finset.mem_univ σ))) hf
  choose u w hwu huw using fun σ => exists_split _ (pm_minors Y p M.toMChart σ).1 (s σ)
    ((pm_minors Y p M.toMChart σ).2.2 (s σ)) (resG Y.X hle) (hu σ)
  exact ⟨⟨M, Y.X.basicOpen g, hle, u, w, hwu, huw⟩, rfl, hxg, M.hU.basicOpen g, hg.trans inf_le_left⟩

end Geo

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisedChartScale
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtScale


set_option maxHeartbeats 1000000 in
theorem exists_ext_chart_scale : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ φ : ℝ, HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), y'.IsAlg ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ HasPhi y' (r * φ) ∧ (∀ (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ), OverLa la T.V io e → OverLa la T'.V io' (r * e)) ∧ (∀ m : ℕ, m ≠ 0 → vV T'.V (m : T'.Fr) = (r : ℤ) * vV T.V (m : T.Fr)) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y hy φ hφ
  obtain ⟨S', io', z', r, hz', hr, hU, ψA, hv, hm⟩ := GlobalTheory.T.exists_extension_all_models_uniformized _ _ _ _ Xo c T io y hy
  have hphi : ∀ φ' : ℝ, HasPhi z' φ' → φ' = r * φ := fun φ' h' =>
    GlobalTheory.T.balancedPeriodSlope_mul_ramificationIndex _ _ _ _ Xo c T S' io io' y z' r hr ⟨ψA, hv, hm⟩ φ φ' hφ h'
  letI := io.toAlgebra
  let ψ : T.Fr →+* S'.Fr := letI := io'.toAlgebra; ψA.toRingHom
  have hio : io' = ψ.comp io := by
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (ψA.commutes a).symm
  have hv' : ∀ a : T.Fr, vV S'.V (ψ a) = (r : ℤ) * vV T.V a := fun a => by
    by_cases ha : a = 0
    · simp [ha, vV]
    · exact hv a ha
  have hev : ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      ∀ f ∈ thGen Xo c nab a n, ψ (evI y f) = evI z' f := fun nab hn a n f hf =>
    GlobalTheory.T.thetaRule_integralPoint_value_baseChange _ _ _ _ Xo c nab hn T S' io io' y z' ψA hm a n f hf
  clear_value ψ
  clear hm hv ψA
  subst hio
  obtain ⟨C, hCh⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists _ H _ _ Xo c (fun _ => rfl) S' _ z'
  obtain ⟨P, hP⟩ := hU C.I
  obtain ⟨φ', hφ'⟩ := exists_hasPhi z' C.I.G C.I.t' C.I.m1 C.I.m2 P
  have e1 := hphi φ' hφ'
  subst e1
  refine ⟨S', ψ.comp io, z', r, C, P, hz', hr, hCh, hP, hφ', fun la e ho => ho.bc ψ hr hv', fun m _ => ?_,
    fun nab hn a n e s f hf => ?_⟩
  · rw [← hv' (m : T.Fr), map_natCast]
  · rw [← hev nab hn a n f hf, RingHom.comp_apply, ← map_mul, nval_bc ψ hr hv']

end GlobalTheory.ExtScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionPSpace
section
namespace GlobalTheory.ZMain

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem finite_integralClosure_field (R L : Type*) [CommRing R] [Algebra.FiniteType ℤ R] [Field L]
    [Algebra R L] [Algebra.EssFiniteType R L] : Module.Finite R (integralClosure R L) := by
  rcases CharP.char_is_prime_or_zero L (ringChar L) with hp | h0
  · let p := ringChar L
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : CharP L p := ringChar.charP L
    let I := RingHom.ker (algebraMap R L)
    let R' := R ⧸ I
    letI : Algebra R' L := (Ideal.Quotient.lift I (algebraMap R L) fun _ h => h).toAlgebra
    haveI : IsScalarTower R R' L := .of_algebraMap_eq fun _ => rfl
    have hinj : Function.Injective (algebraMap R' L) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    haveI : IsDomain R' := hinj.isDomain _
    haveI : FaithfulSMul R' L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    haveI : CharP R' p := ⟨fun n => by
      rw [← map_eq_zero_iff _ hinj, map_natCast, CharP.cast_eq_zero_iff L]⟩
    letI : Algebra (ZMod p) R' := (ZMod.castHom dvd_rfl R').toAlgebra
    haveI : Algebra.FiniteType ℤ R' := .trans (S := R) inferInstance inferInstance
    haveI : Algebra.FiniteType (ZMod p) R' := .of_restrictScalars_finiteType ℤ (ZMod p) R'
    haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing (ZMod p) R'
    haveI : Module.Finite R R' := Module.Finite.of_surjective (Algebra.linearMap R R')
      Ideal.Quotient.mk_surjective
    let F := FractionRing R'
    letI : Algebra F L := FractionRing.liftAlgebra R' L
    haveI : Algebra.EssFiniteType R' L := .of_comp R R' L
    haveI : Algebra.EssFiniteType F L := .of_comp R' F L
    let E := algebraicClosure F L
    haveI : FiniteDimensional F E := finiteDimensional_algebraicClosure_of_essFiniteType F L
    haveI : Module.Finite R' (integralClosure R' E) :=
      NormFin.finite_integralClosure_of_perfectField (ZMod p) R' F E
    haveI : IsScalarTower R' E L := .of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R' F L x, IsScalarTower.algebraMap_apply R' F E x,
        ← IsScalarTower.algebraMap_apply F E L]
    have hmem : ∀ z : integralClosure R' L, (z : L) ∈ E := fun z =>
      mem_algebraicClosure_iff.mpr (z.2.tower_top (A := F)).isAlgebraic
    let ψ : integralClosure R' L →ₗ[R'] integralClosure R' E :=
      { toFun := fun z => ⟨⟨z, hmem z⟩, (isIntegral_algHom_iff (IsScalarTower.toAlgHom R' E L)
            (IsScalarTower.toAlgHom R' E L).toRingHom.injective).mp z.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    haveI : Module.Finite R' (integralClosure R' L) := Module.Finite.of_injective ψ
      fun a b h => Subtype.ext (congrArg (fun w : integralClosure R' E => ((w : E) : L)) h)
    exact finite_integralClosure_of_finite_tower R R' L
  · haveI : CharZero L := (CharP.ringChar_zero_iff_CharZero L).mp h0
    exact finite_integralClosure_of_essFiniteType_field ℤ R L

universe u

theorem isFinite_fromNormalization_int {X Y : Scheme.{u}} {o : CommRingCat.{u}}
    [Algebra.FiniteType ℤ o] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (g : Y ⟶ Spec o)
    [LocallyOfFiniteType g] [IsIntegral X]
    (hess : (f.residueFieldMap (genericPoint X)).hom.EssFiniteType) :
    IsFinite f.fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  letI := (f.app U).hom.toAlgebra
  letI : Algebra o Γ(Y, U) := ((Scheme.ΓSpecIso o).inv ≫ g.appLE ⊤ U le_top).hom.toAlgebra
  haveI : Algebra.FiniteType o Γ(Y, U) :=
    (g.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso o).inv).2)
  haveI : Algebra.FiniteType ℤ Γ(Y, U) := .trans (S := o) inferInstance inferInstance
  haveI : IsNoetherianRing Γ(Y, U) := Algebra.FiniteType.isNoetherianRing ℤ _
  let D : Set X := {genericPoint X}
  have hD : Dense D := dense_iff_closure_eq.mpr (genericPoint_spec X)
  let ι := ↥(D ∩ (f ⁻¹ᵁ U : X.Opens))
  haveI : Finite ι := ((Set.finite_singleton _).inter_of_left _).to_subtype
  letI (x : ι) : Algebra Γ(Y, U) (X.residueField x.1) :=
    (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.toAlgebra
  haveI (x : ι) : Algebra.EssFiniteType Γ(Y, U) (X.residueField x.1) := by
    change (f.app U ≫ X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom.EssFiniteType
    rw [← Scheme.evaluation_naturality f (V := U) x.1 x.2.2]
    have hx : x.1 = genericPoint X := x.2.1
    exact .comp (.comp (essFiniteType_germ hU (f x.1) x.2.2)
      (RingHom.FiniteType.of_surjective _ (Y.residue_surjective _)).essFiniteType)
      (by rw [hx] at *; exact hess)
  haveI (x : ι) := finite_integralClosure_field Γ(Y, U) (X.residueField x.1)
  haveI : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine finite_integralClosure_of_family (L := fun x : ι => X.residueField x.1)
      (fun x => { (X.evaluation (f ⁻¹ᵁ U) x.1 x.2.2).hom with commutes' := fun _ => rfl })
      fun b hb => ?_
    rw [← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxD⟩ := hD.inter_open_nonempty _ (X.basicOpen b).isOpen ⟨y, hy⟩
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen x (X.basicOpen_le b hx) b).mp
      (hb ⟨x, hxD, X.basicOpen_le b hx⟩) hx).elim
  rw [f.fromNormalization_app hU]
  exact RingHom.Finite.comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2)
    (RingHom.finite_algebraMap.mpr this)


open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem exists_finite_openImmersion_pSpace : ∀ (o : Type) [CommRing o] [IsNoetherianRing o]
    [Algebra.FiniteType ℤ o] (m : ℕ) (X : Scheme.{0}) (f : X ⟶ PSpace o m), IsIntegral X →
    Geo.Tor.IsNormalScheme X → LocallyOfFiniteType f → QuasiCompact f → IsSeparated f →
    LocallyQuasiFinite f → ∃ (Z : Scheme.{0}) (z : Z ⟶ PSpace o m) (i : X ⟶ Z), IsFinite z ∧
      IsOpenImmersion i ∧ i ≫ z = f ∧ Geo.Tor.IsNormalScheme Z ∧ IsIntegral Z ∧
      Dense (Set.range i) := by
  intro o _ _ _ m X f hX hN _ _ _ _
  haveI : Algebra.FiniteType ℤ (CommRingCat.of o) := ‹Algebra.FiniteType ℤ o›
  haveI := isProper_str o m
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  refine ⟨f.normalization, f.fromNormalization, f.toNormalization,
    isFinite_fromNormalization_int f (PSpace.str o m)
      (LocallyOfFiniteType.stalkMap f _).residueFieldMap,
    inferInstance, f.toNormalization_fromNormalization,
    (GlobalTheory.IsNormalScheme.normalization_of_isIntegral f).pred _, inferInstance,
    (inferInstance : IsDominant f.toNormalization).denseRange⟩

end GlobalTheory.ZMain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatSectionValueEqMulDetInv
section
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.FlatValue

theorem exists_reduced_frameRing (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) :
    ∃ (A : TRing K) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), (∀ τ, IsUnit (X τ).det) ∧
      ∀ (T : Type) [CommRing T] [Algebra K T] (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T) (a : Tˣ),
        (∀ τ, IsUnit (g τ).det) → ∃ k : A.R →ₐ[K] T, (∀ τ, (X τ).map k = g τ) ∧ k (s : A.R) = (a : T) := by
  let p : TRing K := ⟨0, ⊥, Ideal.isRadical_bot⟩
  obtain ⟨A, π, X, s, hA⟩ := _root_.GlobalTheory.exists_frameRing_testRing K J m p
  refine ⟨A, X, s, hA.1, fun T _ _ g a hg => ?_⟩
  let ψ : p.R →ₐ[K] T := Ideal.Quotient.liftₐ ⊥ (MvPolynomial.aeval Fin.elim0) (fun x hx => by
    rw [Ideal.mem_bot.1 hx, map_zero])
  obtain ⟨k, ⟨-, h1, h2⟩, -⟩ := hA.2 T ψ g a hg
  exact ⟨k, h1, h2⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exOf_flatWt (hq : Dw.q = 0) (τ : Psi H) (b : E →+* ℂ) (i : Fin (Dw.mult b)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨b, i⟩) = if b = τ.1 then -1 else 0 := by
  have hi := i.2
  by_cases h : b (H.rt : E) = H.rt0
  · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
    refine (wtOf_big _ 0 ⟨b, h⟩ i hp).trans ?_
    simp [flatWt, parWt, Subtype.ext_iff]
  · have hq' : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
    omega

theorem evR_mul_det_field (hq : Dw.q = 0) (τ : Psi H) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (K : Type) [Field K] [Algebra c.F K] (z y : FrPt Xo c K) (Y : Mats Dw K) (u : Kˣ) (hY : ∀ b, (Y b).det ≠ 0)
    (h : FrChg (fun b => (Y b)ᵀ) (u : K) z y) : evR Xo c f y * (Y τ.1).det = evR Xo c f z := by
  obtain ⟨G, hG, hev⟩ := GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ E H Dw l Xo c K z _
    (fun b => if b = τ.1 then 1 else 0) (fun _ _ => 0) rfl
    (fun b i => by rw [exOf_flatWt hq]; split_ifs <;> simp) f hf
  simp only [Finset.sum_const_zero] at hG
  have hC : G = MvPolynomial.C (G.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 hG.totalDegree_le)
  have h1 := hev y Y u hY h
  have h2 := hev z (fun _ => 1) 1 (fun _ => by simp) (by
    simpa using (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K z z z).1)
  rw [hC] at h1 h2
  simp only [Formalism.L2.LamCM.evalFr, MvPolynomial.eval_C, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq',
    Finset.mem_univ, if_true, Matrix.det_one, ite_self, Finset.prod_const_one, one_mul] at h1 h2
  rw [mul_comm, h1, h2]

theorem exists_evR_mul_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ), ∃ b : c.F, b ≠ 0 ∧ (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) := by
  intro E _ _ _ H Dw l Xo c r U ξ hD Z P τ s
  refine ⟨evR Xo c s.sig P.y₀,
    left_ne_zero_of_mul_eq_one (s.evR_mul_inv P.on (GlobalTheory.FlagTan.fromTest_of_isLocalRing _)), ?_⟩
  obtain ⟨A, X, t, hX, hA⟩ := exists_reduced_frameRing c.F (E →+* ℂ) Dw.mult
  haveI : _root_.IsReduced A.R := (Ideal.isRadical_iff_quotient_reduced _).1 A.rad
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.FlagTan.exists_frMap (Algebra.ofId c.F A.R) P.y₀
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c A.R w₀ (fun b => (X b)ᵀ) t
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  have step : ∀ (S : Type) [CommRing S] [Algebra c.F S] (k : A.R →ₐ[c.F] S) (z y : FrPt Xo c S),
      FrMap (Algebra.ofId c.F S) P.y₀ z → (FrMap k w y ↔ FrChg (fun b => ((X b).map k)ᵀ) (k t) z y) := by
    intro S _ _ k z y hz
    have h0 : FrMap k w₀ z := GlobalTheory.FlagTan.frMap_of_comp hw₀ hz fun a => k.commutes a
    exact GlobalTheory.FlagTan.frMap_iff_frChg hw h0
  have nat : ∀ (S : Type) [CommRing S] [Algebra c.F S] (k : A.R →ₐ[c.F] S) (y : FrPt Xo c S), FrMap k w y →
      evR Xo c s.sig y = k (evR Xo c s.sig w) := fun S _ _ k y h =>
    GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c s.sig s.sig_mem.1 k w y h
  have univ : evR Xo c s.sig w * (X τ.1).det = algebraMap c.F A.R (evR Xo c s.sig P.y₀) := by
    rw [← sub_eq_zero]
    refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun q hq => ?_)
    let K : Type := q.ResidueField
    let k : A.R →ₐ[c.F] K := IsScalarTower.toAlgHom c.F A.R K
    obtain ⟨z, hz⟩ := GlobalTheory.FlagTan.exists_frMap (Algebra.ofId c.F K) P.y₀
    obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frMap k w
    have hd : ∀ b, ((X b).map k).det = k (X b).det := fun b => (AlgHom.map_det k (X b)).symm
    have h1 := evR_mul_det_field hD.q τ s.sig_mem K z y (fun b => (X b).map k)
      (Units.map (k : A.R →* K) t) (fun b => by rw [hd]; exact ((hX b).map k).ne_zero) ((step K k z y hz).1 hy)
    rw [nat K k y hy, GlobalTheory.FlagTan.evR_frMap s.sig_mem.1 hz, hd] at h1
    rw [← Ideal.algebraMap_residueField_eq_zero]
    show k _ = 0
    rw [map_sub, map_mul, h1, k.commutes]
    exact sub_self _
  intro S _ _ z y Y u hY hu hz h
  obtain ⟨k, hk, hkt⟩ := hA S Y hu.unit hY
  have hy : FrMap k w y := (step S k z y hz).2 (by
    rw [hkt, IsUnit.unit_spec]
    simpa only [hk] using h)
  rw [nat S k y hy, ← hk τ.1, ← k.commutes, ← univ, map_mul]
  exact congrArg _ (AlgHom.map_det k (X τ.1)).symm

end GlobalTheory.FlatValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingFrameUnitChangeToChartStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generatingFrame_unit_change_to_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : GChart Y) (V K : Type) [CommRing V] [IsLocalRing V] [Field K] [CharZero K] [Algebra V K] (yt : Sp V ⟶ Y.X) (hz : ⊤ ≤ yt ⁻¹ᵁ M.U) (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w → ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) → Generates (X := t.G) θ → ∃ (x' : KeyIn K) (a d : Vˣ), KeyAt M (spMap (algebraMap V K) ≫ yt) (le_preimage_comp _ hz) x' ∧ ∀ κ : KeyRule, IsKeyRule κ → algebraMap V K a ^ 8 * (κ K x' : K) = algebraMap V K d ^ 4 * (κ K x : K) := by
  first | exact @GlobalTheory.KeyFramePoint.exists_keyAt_units | exact GlobalTheory.KeyFramePoint.exists_keyAt_units | (intros; apply GlobalTheory.KeyFramePoint.exists_keyAt_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfConjEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasMarkingPreservingTransport_of_conj_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ), HasTransport Xo c U ((starRingEnd ℂ).comp e) → HasTransport Xo c U e := by
  first | exact @GlobalTheory.hasTransport_of_conj | exact GlobalTheory.hasTransport_of_conj | (intros; apply GlobalTheory.hasTransport_of_conj <;> assumption)
end

