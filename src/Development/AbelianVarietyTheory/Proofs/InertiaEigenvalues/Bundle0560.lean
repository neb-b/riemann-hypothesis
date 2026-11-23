module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0006
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0546
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdaptedBasisThetaGaloisFixedPoles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

theorem GlobalTheory.MapSmul.mapSmul {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (a : R) (M : Matrix m n R) :
    (a • M).map f = f a • M.map f := by
  ext i j; simp


open GlobalTheory.MapSmul in
theorem GlobalTheory.BKLim.adaptedBasis_theta_and_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z → ∃ u : Matrix (Fin d) (Fin d) (ℂ_[l]), u * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) ∧ u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal fun i => z ^ ((H.p i : ℤ) - H.q)) ∧ ∀ N₀ : ℕ, N₀ ≤ N → (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → (∀ i j, bk.E ^ (N - N₀) ∣ F.A i j) ∧ ∀ i j, bk.E ^ (N - N₀) ∣ F.A' i j := by
  intro l _ K bk τ hτ C hC N d ρ F Y hDR hY H
  have hdom := GlobalTheory.MemLoc.BdRField.bdR_isField l
  haveI : IsDomain (Per.BdRp l) := hdom.1
  have hι : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := hdom.2.1
  obtain ⟨B, Q, hBu, hQu, hBl, hQ, hQi⟩ := _root_.GlobalTheory.BKLim.InvBasis.exists_invariant_basis l K bk τ hτ C N d ρ F Y hDR hY
  obtain ⟨Y₁, Y', hY₁, hYY'⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N d ρ F.toPre
  have hinj : Function.Injective (inclW l) := WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))
  have hY1 : Y₁ = Y := Matrix.ext fun i j => hinj (by simpa using congrFun (congrFun (hY₁.trans hY.symm) i) j)
  rw [hY1] at hYY'
  obtain ⟨c, c', hc, hc', hcc', hQH⟩ := GlobalTheory.T.hodgeAdaptedBasis_invariant_matrix_ratio l K bk C hC d ρ Q hQu hQi H
  have hθt : Per.θD l (aDp l τ) ≠ 0 := by simpa using _root_.GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero l K bk τ hτ 1
  have htu : IsUnit (aDp l τ) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ hθt
  obtain ⟨u, hu⟩ := htu
  have hYY'd : Y.map (aDp l) * Y'.map (aDp l) = aDp l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
    rw [← Matrix.map_mul, hYY', mapSmul, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  have hY'Yd : Y'.map (aDp l) * Y.map (aDp l) = aDp l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
    have h1 : ((↑u⁻¹ : Per.BdRp l) ^ (2 * N) • Y.map (aDp l)) * Y'.map (aDp l) = 1 := by
      rw [Matrix.smul_mul, hYY'd, smul_smul, ← hu, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have h2 := mul_eq_one_comm.1 h1
    rw [Matrix.mul_smul] at h2
    calc Y'.map (aDp l) * Y.map (aDp l) = (aDp l τ ^ (2 * N)) • ((↑u⁻¹ : Per.BdRp l) ^ (2 * N) • (Y'.map (aDp l) * Y.map (aDp l))) := by
          rw [smul_smul, ← hu, ← mul_pow, Units.mul_inv, one_pow, one_smul]
      _ = _ := by rw [h2]

  have hstar : aDp l (bk.ev bk.E) ^ H.q • (Y.map (aDp l) * (F.A.map bk.ev).map (aDp l) * B * c.map C.o) =
      (aDp l (bk.ev bk.E) * aDp l τ) ^ N • (H.V * Matrix.diagonal (fun j => aDp l (bk.ev bk.E) ^ H.p j)) := by
    refine GlobalTheory.T.transport_matrix_identity_injective_ringHom (algebraMap (Per.BdRp l) (Per.BdR l)) hι d N H.q H.p _ _ Q H.Q _ B _ H.V ?_ H.Q_eq ?_
    · rw [← Matrix.map_mul, ← map_mul]; exact hQ
    · rw [hQH]; rfl

  set V₀ : Matrix (Fin d) (Fin d) (Per.BdRp l) := (↑u⁻¹ : Per.BdRp l) ^ N • (Y'.map (aDp l) * H.V) with hV₀
  have h1 : Y.map (aDp l) * V₀ = aDp l τ ^ N • H.V := by
    rw [hV₀, Matrix.mul_smul, ← Matrix.mul_assoc, hYY'd, Matrix.smul_mul, Matrix.one_mul, smul_smul, ← hu]
    congr 1
    rw [two_mul, pow_add, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  have hY'V : Y'.map (aDp l) * H.V = aDp l τ ^ N • V₀ := by
    rw [hV₀, smul_smul, ← hu, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  have h2 : aDp l (bk.ev bk.E) ^ H.q • ((F.A.map bk.ev).map (aDp l) * B * c.map C.o) =
      aDp l (bk.ev bk.E) ^ N • (V₀ * Matrix.diagonal (fun j => aDp l (bk.ev bk.E) ^ H.p j)) := by
    have e := congrArg (fun M => Y'.map (aDp l) * M) hstar
    simp only [Matrix.mul_smul] at e
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hY'Yd, ← Matrix.mul_assoc, hY'V] at e
    simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul] at e
    have hu2 : IsUnit (aDp l τ ^ (2 * N)) := by rw [← hu]; exact (Units.isUnit u).pow _
    apply (hu2.smul_left_cancel).1
    rw [smul_smul, smul_smul, mul_comm, e, mul_pow, two_mul, pow_add]
    congr 1
    ring

  have h4 : ∀ (g : ↥(GK K)) (i j : Fin d), Per.σC (g : GQ l) (Per.θD l (V₀ i j)) = Per.θD l (V₀ i j) := by
    intro g i j
    obtain ⟨k, s, hs⟩ := GlobalTheory.T.approx_bdRPlus_fil_matrix_mul l K bk (N + H.p j + 1) d ((F.A.map bk.ev).map (aDp l) * B) (c.map C.o)
      (GlobalTheory.T.approx_bdRPlus_fil_matrix_mul l K bk (N + H.p j + 1) d ((F.A.map bk.ev).map (aDp l)) B
        ⟨0, F.A, fun i j => by rw [pow_zero, one_mul, Matrix.map_apply, Matrix.map_apply, sub_self]; exact zero_mem _⟩
        (hBl (N + H.p j + 1)))
      (GlobalTheory.T.exists_wittPowerSeries_approx_matrix_bdRPlus l K bk C d c hc (N + H.p j + 1))
    refine _root_.GlobalTheory.BKLim.theta_gal_fixed_of_congr l K bk (V₀ i j) (N + H.p j) k (bk.E ^ H.q * s i j) ?_ g
    have e := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul] at e
    have hm := Ideal.mul_mem_left _ (-(aDp l (bk.ev bk.E) ^ H.q)) (hs i j)
    have key : (l : Per.BdRp l) ^ k * aDp l (bk.ev bk.E) ^ (N + H.p j) * V₀ i j - aDp l (bk.ev (bk.E ^ H.q * s i j)) =
        -(aDp l (bk.ev bk.E) ^ H.q) * (aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * ((F.A.map bk.ev).map (aDp l) * B * c.map C.o) i j) := by
      rw [map_mul, map_mul, map_pow, map_pow]
      linear_combination -((l : Per.BdRp l) ^ k) * e
    rw [key]
    exact hm
  refine ⟨fun g z hz => ?_, fun N₀ hN₀ hp => ?_⟩
  · obtain ⟨w, hw, hzw⟩ := hz
    have hG1 := GlobalTheory.T.galois_tauPow_frame_ainf l K bk τ N d ρ F Y hY g
    have hG2 := GlobalTheory.T.hodgeAdaptedBasis_galois_action_bdRPlus l K bk C d ρ H g w hw
    have hb : Per.θD l (aDp l (Per.σA (g : GQ l) τ)) ≠ 0 := by
      rw [← GlobalTheory.MemLoc.ActLaws.σDp_aDp, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.2]
      intro h0
      exact hθt ((Per.σC (g : GQ l)).injective (h0.trans (map_zero _).symm))
    refine GlobalTheory.T.hodgeTate_operator_of_galois_relations d N H.q H.p (Per.θD l (aDp l τ)) (Per.θD l (aDp l (Per.σA (g : GQ l) τ))) z (Per.θD l (aDp l w))
      _ (Y'.map ((Per.θD l).comp (aDp l))) _ (V₀.map (Per.θD l)) _ (((ρ g).map ((aDp l).comp (Per.zA l))).map (Per.θD l))
      ((Y.map (Per.σA (g : GQ l))).map ((Per.θD l).comp (aDp l))) ((H.V.map (Per.σDp (g : GQ l))).map (Per.θD l))
      hθt hb hzw ?_ ?_ ?_ ?_ ?_
    · rw [← Matrix.map_mul, hYY', mapSmul, Matrix.map_one _ (map_zero _) (map_one _), map_pow]; rfl
    · rw [show Y.map ((Per.θD l).comp (aDp l)) = (Y.map (aDp l)).map (Per.θD l) from (Matrix.map_map).symm,
        ← Matrix.map_mul, h1, mapSmul, map_pow]
    · have e := congrArg (fun M => M.map ((Per.θD l).comp (aDp l))) hG1
      simp only [mapSmul, Matrix.map_mul, map_pow] at e
      have hr : ((ρ g).map ((aDp l).comp (Per.zA l))).map (Per.θD l) = ((ρ g).map (Per.zA l)).map ((Per.θD l).comp (aDp l)) := by
        ext i j; simp
      rw [hr]
      simpa only [RingHom.comp_apply] using e
    · have e := congrArg (fun M => M.map (Per.θD l)) hG2
      simp only [mapSmul, Matrix.map_mul, map_pow] at e
      rw [← e, Matrix.diagonal_map (map_zero _)]
      simp [Function.comp_def]
    · have e := congrArg (fun M => (M.map (Per.σDp (g : GQ l))).map (Per.θD l)) h1
      simp only [mapSmul, Matrix.map_mul, map_pow] at e
      have e1 : ((Y.map (aDp l)).map (Per.σDp (g : GQ l))).map (Per.θD l) = (Y.map (Per.σA (g : GQ l))).map ((Per.θD l).comp (aDp l)) := by
        ext i j; simp [GlobalTheory.MemLoc.ActLaws.σDp_aDp]
      have e2 : (V₀.map (Per.σDp (g : GQ l))).map (Per.θD l) = V₀.map (Per.θD l) := by
        ext i j; simp only [Matrix.map_apply]; rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.2, h4]
      rw [e1, e2, GlobalTheory.MemLoc.ActLaws.σDp_aDp] at e
      exact e
  · obtain ⟨B', hBB'⟩ := hBu.exists_right_inv
    obtain ⟨Vu, hVu⟩ := H.unit
    have hcp : c.map C.o * c'.map C.o = 1 := by
      rw [← Matrix.map_mul, hcc', Matrix.map_one _ (map_zero _) (map_one _)]
    have hVV : H.V * (↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l)) = 1 := by rw [← hVu]; exact Vu.mul_inv
    have hV₀' : V₀ * ((↑u⁻¹ : Per.BdRp l) ^ N • ((↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l)) * Y.map (aDp l))) = 1 := by
      calc V₀ * ((↑u⁻¹ : Per.BdRp l) ^ N • ((↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l)) * Y.map (aDp l)))
          = ((↑u⁻¹ : Per.BdRp l) ^ N * (↑u⁻¹ : Per.BdRp l) ^ N) • (Y'.map (aDp l) * (H.V * (↑Vu⁻¹ : Matrix (Fin d) (Fin d) (Per.BdRp l))) * Y.map (aDp l)) := by
            rw [hV₀, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; simp only [Matrix.mul_assoc]
        _ = ((↑u⁻¹ : Per.BdRp l) ^ N * (↑u⁻¹ : Per.BdRp l) ^ N) • (Y'.map (aDp l) * Y.map (aDp l)) := by rw [hVV, Matrix.mul_one]
        _ = 1 := by
            rw [hY'Yd, smul_smul, ← hu, ← pow_add, ← two_mul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hAA' : (F.A.map bk.ev).map (aDp l) * (F.A'.map bk.ev).map (aDp l) =
        aDp l (bk.ev bk.E) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.BdRp l)) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, F.A_mul, mapSmul, mapSmul, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_one _ (map_zero _) (map_one _), map_pow, map_pow]
    obtain ⟨hne, htr⟩ := _root_.GlobalTheory.BSP.DivTransfer.div_transfer l K bk
    obtain ⟨hdA, hdA'⟩ := GlobalTheory.T.pow_dvd_entries_of_mul_eq_diagonal_pow d N N₀ H.q H.p (aDp l (bk.ev bk.E)) _ _ B B' _ _ V₀ _ hne hBB' hcp hV₀' hAA' h2 hN₀ hp
    exact ⟨fun i j => htr _ _ (by simpa using hdA i j), fun i j => htr _ _ (by simpa using hdA' i j)⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
section
noncomputable section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Polynomial
open Formalism.MainNotions.N (GRep)

namespace GlobalTheory.FullCharpoly

section Lat
variable {G LL O V W : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
  {ρ : Representation LL G V} {σ : Representation LL G W}

def mapLat (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x)) (L : Lattice (O := O) ρ) :
    Lattice (O := O) σ where
  T := L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
  stable := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, L.stable g x hx, he g x⟩
  fg := L.fg.map _
  free := by
    have := L.free
    exact Module.Free.of_equiv ((e.restrictScalars O).submoduleMap L.T)
  span := by
    have h : ((L.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W) : Submodule O W) : Set W) =
        (e : V →ₗ[LL] W) '' (L.T : Set V) := rfl
    rw [h, Submodule.span_image, L.span, Submodule.map_top, LinearEquiv.range]

variable {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]

theorem quot_equiv_iff (L₁ L₂ : Lattice (O := O) ρ) (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    (∃ e : (E ⧸ LinearMap.ker p) ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype),
      ∀ (g : G) (x : E) (y : ↥L₁.T), e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
        e (Submodule.Quotient.mk (act g x)) = Submodule.Quotient.mk ⟨ρ g y, L₁.stable g y y.2⟩) ↔
    ∃ q : ↥L₁.T →ₗ[O] M, Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧
      ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T := by
  constructor
  · rintro ⟨e, he⟩
    let Φ := p.quotKerEquivOfSurjective hp
    refine ⟨(Φ.toLinearMap.comp e.symm.toLinearMap).comp (L₂.T.comap L₁.T.subtype).mkQ, ?_, ?_, ?_⟩
    · exact Φ.surjective.comp (e.symm.surjective.comp (Submodule.mkQ_surjective _))
    · intro g y
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk y))
      have h1 : e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
        rw [hx, LinearEquiv.apply_symm_apply]
      have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply]
      rw [h3, ← he g x y h1, LinearEquiv.symm_apply_apply, ← hx]
      simp only [Φ, LinearMap.quotKerEquivOfSurjective_apply_mk]
      exact hact g x
    · intro y
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.mkQ_apply,
        LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.coe_subtype]
  · rintro ⟨q, hq, hqe, hqk⟩
    have hker : LinearMap.ker q = L₂.T.comap L₁.T.subtype := by
      ext y
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype, hqk]
    let ψ : M ≃ₗ[O] (↥L₁.T ⧸ L₂.T.comap L₁.T.subtype) :=
      (q.quotKerEquivOfSurjective hq).symm.trans (Submodule.quotEquivOfEq _ _ hker)
    have hψ : ∀ y, ψ (q y) = Submodule.Quotient.mk y := by
      intro y
      simp only [ψ, LinearEquiv.trans_apply]
      rw [(LinearEquiv.symm_apply_eq _).2 (LinearMap.quotKerEquivOfSurjective_apply_mk q hq y).symm]
      rfl
    have hΦ : ∀ x, p.quotKerEquivOfSurjective hp (Submodule.Quotient.mk x) = p x :=
      LinearMap.quotKerEquivOfSurjective_apply_mk p hp
    refine ⟨(p.quotKerEquivOfSurjective hp).trans ψ, fun g x y h => ?_⟩
    simp only [LinearEquiv.trans_apply, hΦ] at h ⊢
    have hxy : p x = q y := ψ.injective (h.trans (hψ y).symm)
    have h3 : latRep L₁ g y = ⟨ρ g y, L₁.stable g y y.2⟩ := Subtype.ext (latRep_apply L₁ g y)
    rw [hact, hxy, ← hqe, h3, hψ]

end Lat

section Sum
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] {n : ℕ}
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)} {lam : O} {jT : ZMod n → ℤ → ℤ} {cT : G → Polynomial LL}

def ofFull (F : tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := F.V
  cadd := IsModuleTopology.toContinuousAdd LL F.V
  csmul := by have := IsModuleTopology.toContinuousSMul LL F.V; infer_instance
  ρ := F.ρ
  cont := F.full.1

def sumFull {m : ℕ} (F : Fin m → tableLineDegreeTwo.FullRep PD emb lam jT cT) : GRep G Qp LL O where
  V := ∀ j, (F j).V
  cadd := IsModuleTopology.toContinuousAdd LL _
  csmul := by have := IsModuleTopology.toContinuousSMul LL (∀ j, (F j).V); infer_instance
  ρ := tableLineDegreeTwo.piRep F
  cont := fun x => continuous_pi fun j => (F j).full.1 (x j)

def toFull (A : GRep G Qp LL O) (h : tableLineDegreeTwo.IsFull PD emb lam jT cT A.ρ) : tableLineDegreeTwo.FullRep PD emb lam jT cT where
  V := A.V
  ρ := A.ρ
  full := h

private theorem mapLattice_quotient_of_equivariant_equiv {G LL O V W M : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W]
    {ρ : Representation LL G V} {σ : Representation LL G W} [AddCommGroup M] [Module O M]
    (π : Representation O G M) (e : V ≃ₗ[LL] W) (he : ∀ g x, e (ρ g x) = σ g (e x))
    (L₁ L₂ : Lattice (O := O) ρ) (q : ↥L₁.T →ₗ[O] M) (hq : Function.Surjective q)
    (hqe : ∀ g x, q (latRep L₁ g x) = π g (q x)) (hqk : ∀ x, q x = 0 ↔ (x : V) ∈ L₂.T) :
    ∃ q' : ↥(mapLat e he L₁).T →ₗ[O] M, Function.Surjective q' ∧
      (∀ g x, q' (latRep (mapLat e he L₁) g x) = π g (q' x)) ∧
      ∀ x, q' x = 0 ↔ (x : W) ∈ (mapLat e he L₂).T := by
  let s : ↥L₁.T ≃ₗ[O] ↥(mapLat e he L₁).T := (e.restrictScalars O).submoduleMap L₁.T
  have hsx : ∀ x, (s x : W) = e x := fun x => rfl
  refine ⟨q.comp s.symm.toLinearMap, hq.comp s.symm.surjective, ?_, ?_⟩
  · intro g y
    obtain ⟨x, rfl⟩ := s.surjective y
    have hs : latRep (mapLat e he L₁) g (s x) = s (latRep L₁ g x) := by
      apply Subtype.ext
      rw [latRep_apply, hsx, hsx, latRep_apply, he]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact hqe g x
  · intro y
    obtain ⟨x, rfl⟩ := s.surjective y
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hqk, hsx]
    change (x : V) ∈ L₂.T ↔ e x ∈ L₂.T.map ((e.restrictScalars O : V ≃ₗ[O] W) : V →ₗ[O] W)
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨z, hz, hze⟩
      have hzx : z = (x : V) := e.injective hze
      rwa [← hzx]


omit [IsTopologicalRing LL] in
theorem admissible_quotient_ker_iff_full_lattices {E M : Type} [AddCommGroup E] [Module O E] [AddCommGroup M] [Module O M]
    (act : G → E → E) (π : Representation O G M)
    (p : E →ₗ[O] M) (hp : Function.Surjective p) (hact : ∀ g x, p (act g x) = π g (p x)) :
    tableLineDegreeTwo.AdmQ PD emb lam jT cT act (LinearMap.ker p) ↔
      ∃ (μ : ℕ) (F : Fin μ → GRep G Qp LL O) (A : GRep G Qp LL O)
      (e : A.V ≃ₗ[LL] (∀ j, (F j).V)) (L₁ L₂ : Lattice (O := O) A.ρ) (q : ↥L₁.T →ₗ[O] M),
      (∀ j, tableLineDegreeTwo.IsFull PD emb lam jT cT (F j).ρ) ∧ (∀ g x j, e (A.ρ g x) j = (F j).ρ g (e x j)) ∧ L₂.T ≤ L₁.T ∧
      Function.Surjective q ∧ (∀ g x, q (latRep L₁ g x) = π g (q x)) ∧ ∀ x, q x = 0 ↔ (x : A.V) ∈ L₂.T := by
  constructor
  · rintro ⟨m, F, L₁, L₂, hle, e, he⟩
    obtain ⟨q, hq, hqe, hqk⟩ := (quot_equiv_iff L₁ L₂ act π p hp hact).1 ⟨e, he⟩
    exact ⟨m, fun j => ofFull (F j), sumFull F, LinearEquiv.refl LL _, L₁, L₂, q,
      fun j => (F j).full, fun g x j => rfl, hle, hq, hqe, hqk⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, he, hle, hq, hqe, hqk⟩
    let F' : Fin μ → tableLineDegreeTwo.FullRep PD emb lam jT cT := fun j => toFull (F j) (hF j)
    let e' : A.V ≃ₗ[LL] (∀ j, (F' j).V) := e
    have he' : ∀ g x, e' (A.ρ g x) = tableLineDegreeTwo.piRep F' g (e' x) := fun g x => funext fun j => he g x j
    obtain ⟨q', hq', hqe', hqk'⟩ := mapLattice_quotient_of_equivariant_equiv π e' he' L₁ L₂ q hq hqe hqk
    exact ⟨μ, F', mapLat e' he' L₁, mapLat e' he' L₂, Submodule.map_mono hle,
      (quot_equiv_iff _ _ act π p hp hact).2 ⟨q', hq', hqe', hqk'⟩⟩


omit [TopologicalSpace G] [TopologicalSpace LL] [IsTopologicalRing LL] in
theorem resPoly_eq {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (χ : ℕ → G →* Oˣ) (t : ℕ) :
    tableLineDegreeTwo.resPoly ρ χ t = fun g => LinearMap.charpoly (ρ g) *
      ∏ c : Fin t, (X - C (algebraMap O LL (χ (c.val + 1) g))) := by
  funext g
  simp only [tableLineDegreeTwo.resPoly]
  congr 1
  symm
  refine Finset.prod_bij (fun (c : Fin t) _ => c.val + 1) ?_ ?_ ?_ ?_
  · intro c _
    simp only [Finset.mem_Icc]
    omega
  · intro a _ b _ hab
    exact Fin.ext (by simpa using hab)
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, by simp only; omega⟩
  · intro c _
    simp [tableLineDegreeTwo.charL]

end Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem isFull_iff_polyFull (jT : ZMod S.n → ℤ → ℤ) (A : GRep S.G ℚ_[l] ↥S.LL.1 S.O) :
    tableLineDegreeTwo.IsFull (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) A.ρ ↔ PolyFull S jT A := by
  unfold tableLineDegreeTwo.IsFull PolyFull
  rw [resPoly_eq]
  simp only [tableLineDegreeTwo.Over, AlgHom.ext_iff, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  exact ⟨fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨A.cont, h.1, h.2.1, h.2.2⟩⟩

theorem admissibleQuotient_iff_admissible_module : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ), (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) → ∀ (E M : Type) [AddCommGroup E] [Module S.O E] [AddCommGroup M] [Module S.O M] (act : S.G → E → E) (π : Representation S.O S.G M) (p : E →ₗ[S.O] M), Function.Surjective p → (∀ g x, p (act g x) = π g (p x)) → (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) act (LinearMap.ker p) ↔ S.admitted π) := by
  intro l _ P S jT hj E M _ _ _ _ act π p hp hact
  refine (admissible_quotient_ker_iff_full_lattices act π p hp hact).trans (Iff.trans ?_ (admissibleModule_iff_lattice_quotients S hj π).symm)
  constructor
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).1 (hF j), h⟩
  · rintro ⟨μ, F, A, e, L₁, L₂, q, hF, h⟩
    exact ⟨μ, F, A, e, L₁, L₂, q, fun j => (isFull_iff_polyFull S jT (F j)).2 (hF j), h⟩

end GlobalTheory.FullCharpoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRImageBcrisEqAinfHatCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open GlobalTheory.BKGal.HatVal in
private theorem gen {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) {W : Type} [AddCommGroup W] (Y : TW (OB l O) T →+ W)
    (act : OD l O →+ (W →+ W)) (hmul : ∀ x y w, act (x * y) w = act x (act y w)) (C : GlobalTheory.MemLoc.Core l)
    (hact : ∀ (b : OB l O) (y : OD l O), iotaO O C b = dRO l O y → ∀ z : TW (OB l O) T, Y (b • z) = act y (Y z))
    (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e)
    (hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) =
      ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) :
    ∑ k, act (ϖ.iD t K (s k)) (Y (jB (toBcris t ϖ P (m k)))) =
      ∑ j, act (ϖ.iD t K (fun τ => c τ j)) (Y (jB (Pi.single j 1))) := by
  have hco := UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix l a e O K t ϖ ι P n s m c hc
  have h1 : ∀ k, Y (jB (toBcris t ϖ P (m k))) = ∑ j, act (ϖ.iD t K
      (fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)))
      (Y (jB (Pi.single j 1))) := by
    intro k
    have h2 : toBcris t ϖ P (m k) = ∑ j, ϖ.iB t K
        (coordL P (invL l (S O K e)) (m k) j) • (Pi.single j 1 : ι → OB l O) := by
      funext i
      rw [toBcris_apply, Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro j _ hj
        rw [Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [jB.map_smul]
    exact hact _ _ (UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD l a e O K t ϖ C _) _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h1, hco, map_sum, map_mul, AddMonoidHom.finsetSum_apply, hmul]
  exact Finset.sum_comm

theorem _root_.GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (c τ j) = ∑ i, hat ↥(OL LL) l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => c τ j)) (X (jB (Pi.single j 1))) := by
  intro _ l _ a e _ _ ϖ LL _ _ _ ι _ _ P T jB Pl AI Td Y hY act hA n s m c hc
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  exact gen (thetaW a LL) ϖ P T jB Y act (_root_.GlobalTheory.BKGal.JumpDR.odAct_mul_one l LL T Pl AI Td act hA).1 C
    (UpperTheory.KN.crysLattice_bdRPlus_action_compat l LL T Pl AI Td Y hY act hA C) n s m c hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodModuleIsClosedLAdicStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_disc_period_module_isClosed_lAdic : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y : ℕ → Fin d → Ainf l, (∀ n, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) z := by
  first | exact @GlobalTheory.BSP.seed_module_lAdic_closed | exact GlobalTheory.BSP.seed_module_lAdic_closed | (intros; apply GlobalTheory.BSP.seed_module_lAdic_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionOfJumpsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_extension_of_jumps : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (T : QLat LL) (U : Finset ℤ), (0 : ℤ) ∈ U → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)) → ∀ z : ↥(latticeCocycles T.L), IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ → ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z).ρ τ (U : Set ℤ) := by
  first | exact @GlobalTheory.ExtJumps.jumps_extLat | exact GlobalTheory.ExtJumps.jumps_extLat | (intros; apply GlobalTheory.ExtJumps.jumps_extLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscSpanFrobeniusStableStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_discSpan_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  first | exact @GlobalTheory.BSP.seed_span_frobenius_stable | exact GlobalTheory.BSP.seed_span_frobenius_stable | (intros; apply GlobalTheory.BSP.seed_span_frobenius_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrixStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_frobenius_inverse_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  first | exact @GlobalTheory.BSP.seed_frob_inverse | exact GlobalTheory.BSP.seed_frob_inverse | (intros; apply GlobalTheory.BSP.seed_frob_inverse <;> assumption)
end

