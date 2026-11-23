module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ExpImm0Of
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR

namespace UpperTheory.Gal.W2

theorem expImm0_of : ExpImm0 := by
  intro X A _ g y e he w hw
  obtain ⟨v, hv, -⟩ := he.2.2.2.1 w
  have hv0 : IsDerivAt0 (fun z => Over.Hom.left (e z)) 0 (Over.Hom.left v) := by
    refine ⟨hv.1, fun U h f => (hv.2 U h f).trans ?_⟩
    have hb : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ Over.Hom.left v = Over.Hom.left (e 0) := hv.1
    have h' : ⊤ ≤ (Over.Hom.left (e 0)) ⁻¹ᵁ U := by
      rw [← hb]
      exact fun x _ => h trivial
    rw [hw U f h', map_zero]
  exact (he.2.2.2.2 v hv.1).unique hv hv0

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PAdExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem map_star_mul_spherical_coordinates {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j
  simp [Matrix.mul_apply]

private theorem det_map_star' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) :
    (A.map star).det = star A.det := by
  exact (RingHom.map_det (starRingEnd ℂ) A).symm

private theorem hermForm_mulVec_mulVec {g : ℕ} (M H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (H *ᵥ z) (H *ᵥ w) = hermForm (Hᵀ * M * H.map star) z w := by
  rw [PerCoordU.herm_mulVec_left, PerCoordU.herm_mulVec_right]

private theorem eq_of_mulVec_period_eq {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {P : D.La →+ Fin g → ℂ} (hP : PELU.IsPeriod D ρ P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, A *ᵥ P x = B *ᵥ P x) : A = B := by
  have e := PerCoordU.ext_per hP (f := PeriodCoord.realMap A 0) (f' := PeriodCoord.realMap B 0)
    (fun x => by simp [PeriodCoord.realMap_apply, h])
  exact (PeriodCoord.realMap_inj e).1

private theorem eq_of_hermForm_im_eq_on_periods {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {g : ℕ}
    {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {P : D.La →+ Fin g → ℂ} (hP : PELU.IsPeriod D ρ P)
    {N N' : Matrix (Fin g) (Fin g) ℂ}
    (h : ∀ x y, (hermForm N (P x) (P y)).im = (hermForm N' (P x) (P y)).im) : N = N' := by
  apply PerCoordU.sesq_ext
  have h1 : PeriodCoord.imForm N = PeriodCoord.imForm N' := by
    apply PerCoordU.ext_per hP
    intro x
    apply PerCoordU.ext_per hP
    intro y
    simp only [PeriodCoord.imForm_apply]
    exact h x y
  intro z w
  rw [← PeriodCoord.imForm_apply, ← PeriodCoord.imForm_apply, h1]

private theorem inv_mul_comm_of_mul_comm_of_det_unit {g : ℕ} (X N : Matrix (Fin g) (Fin g) ℂ) (hN : IsUnit N.det)
    (h : X * N = N * X) : N⁻¹ * X = X * N⁻¹ := by
  calc N⁻¹ * X = N⁻¹ * X * (N * N⁻¹) := by rw [Matrix.mul_nonsing_inv _ hN, Matrix.mul_one]
    _ = N⁻¹ * (X * N) * N⁻¹ := by simp only [Matrix.mul_assoc]
    _ = N⁻¹ * (N * X) * N⁻¹ := by rw [h]
    _ = X * N⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hN, Matrix.one_mul]

theorem UpperTheory.Gal.W2.adExists_of :
    UpperTheory.Gal.W2.AdExists := by
  intro O _ bar g ρ D P₀ M₀ hP hM ga H hF
  obtain ⟨⟨m, hm, hEF⟩, hga⟩ := hF
  obtain ⟨_, hpos, hIm⟩ := hM
  have hform : Hᵀ * M₀ * H.map star = (m : ℂ) • M₀ := by
    apply eq_of_hermForm_im_eq_on_periods hP
    intro x y
    have hs : hermForm ((m : ℂ) • M₀) (P₀ x) (P₀ y) = (m : ℂ) * hermForm M₀ (P₀ x) (P₀ y) := by
      simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]
    rw [← hermForm_mulVec_mulVec, ← hga x, ← hga y, hIm, hEF, hs, Complex.mul_im, hIm]
    simp
  have hdM : M₀.det ≠ 0 := PeriodCoord.det_ne_zero_of_pos hpos
  have hdet : H.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hform
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, det_map_star',
      Matrix.det_smul] at e
    simp [hdM, hm.ne'] at e
  have hcomm : ∀ a, ρ a * H = H * ρ a := by
    intro a
    apply eq_of_mulVec_period_eq hP
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hga x, ← hP.1 a (ga x), ← hP.1 a x,
      ← hga (a • x), LinearMap.map_smul]
  refine ⟨hdet, hcomm, ?_⟩
  intro C hC
  set N := H.map star with hNdef
  have hNu : IsUnit N.det := by
    rw [hNdef, det_map_star']
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hdet)
  have hNtu : IsUnit Nᵀ.det := by rwa [Matrix.det_transpose]
  have hc' : ∀ b, (ρ b).map star * N = N * (ρ b).map star := by
    intro b
    rw [hNdef, ← map_star_mul_spherical_coordinates, ← map_star_mul_spherical_coordinates, hcomm]
  have hC' : (Cᵀ * M₀)ᵀ = Cᵀ * M₀ ∧
      ∀ a, Cᵀ * M₀ * (ρ (bar a)).map star = (ρ a)ᴴ * (Cᵀ * M₀) := hC
  obtain ⟨hS1, hS2⟩ := hC'
  have hHM : Hᵀ * M₀ = (m : ℂ) • (M₀ * N⁻¹) := by
    calc Hᵀ * M₀ = Hᵀ * M₀ * N * N⁻¹ := by
          rw [Matrix.mul_assoc (Hᵀ * M₀), Matrix.mul_nonsing_inv _ hNu, Matrix.mul_one]
      _ = (m : ℂ) • (M₀ * N⁻¹) := by rw [hform, Matrix.smul_mul]
  have hkey : (H * C * N⁻¹)ᵀ * M₀ = (m : ℂ) • (N⁻¹ᵀ * (Cᵀ * M₀) * N⁻¹) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, hHM]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  show ((H * C * N⁻¹)ᵀ * M₀)ᵀ = (H * C * N⁻¹)ᵀ * M₀ ∧
    ∀ a, (H * C * N⁻¹)ᵀ * M₀ * (ρ (bar a)).map star = (ρ a)ᴴ * ((H * C * N⁻¹)ᵀ * M₀)
  rw [hkey]
  generalize Cᵀ * M₀ = S at hS1 hS2 ⊢
  constructor
  · simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hS1,
      Matrix.mul_assoc]
  · intro a
    have c1 : N⁻¹ * (ρ (bar a)).map star = (ρ (bar a)).map star * N⁻¹ :=
      inv_mul_comm_of_mul_comm_of_det_unit _ N hNu (hc' (bar a))
    have hX : (ρ a)ᴴ * Nᵀ = Nᵀ * (ρ a)ᴴ := by
      rw [← PerCoordU.map_star_transpose, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hc' a]
    have c2 : Nᵀ⁻¹ * (ρ a)ᴴ = (ρ a)ᴴ * Nᵀ⁻¹ := inv_mul_comm_of_mul_comm_of_det_unit _ _ hNtu hX
    rw [Matrix.transpose_nonsing_inv]
    calc (m : ℂ) • (Nᵀ⁻¹ * S * N⁻¹) * (ρ (bar a)).map star
        = (m : ℂ) • (Nᵀ⁻¹ * S * (N⁻¹ * (ρ (bar a)).map star)) := by
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = (m : ℂ) • (Nᵀ⁻¹ * (S * (ρ (bar a)).map star) * N⁻¹) := by
          rw [c1]; simp only [Matrix.mul_assoc]
      _ = (m : ℂ) • (Nᵀ⁻¹ * ((ρ a)ᴴ * S) * N⁻¹) := by rw [hS2 a]
      _ = (m : ℂ) • (Nᵀ⁻¹ * (ρ a)ᴴ * S * N⁻¹) := by simp only [Matrix.mul_assoc]
      _ = (ρ a)ᴴ * ((m : ℂ) • (Nᵀ⁻¹ * S * N⁻¹)) := by
          rw [c2]; simp only [Matrix.mul_smul, Matrix.mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PConjCharpoly
section
namespace UpperTheory.Gal.W2

theorem conjCharpoly_of : ConjCharpoly := by
  intro V _ _ _ d hd τ G A hτ hG
  let e : V ≃ₗ[ℂ] (Fin d → ℂ) := τ.linearEquivOfInjective hτ (by simp [hd])
  let b : Module.Basis (Fin d) ℂ V := (Pi.basisFun ℂ (Fin d)).map e.symm
  have hM : LinearMap.toMatrix b b G = A := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    have h1 : b j = e.symm (Pi.single j 1) := by simp [b]
    have h2 : ∀ v, b.repr v i = e v i := fun v => by simp [b, Pi.basisFun_repr]
    rw [h2, h1]
    change τ (G (e.symm (Pi.single j 1))) i = A i j
    rw [hG]
    have h3 : τ (e.symm (Pi.single j 1)) = Pi.single j 1 := by
      rw [← LinearMap.linearEquivOfInjective_apply hτ (by simp [hd])]
      exact e.apply_symm_apply _
    rw [h3, Matrix.mulVec_single_one]
    rfl
  rw [← hM, LinearMap.charpoly_toMatrix]

end UpperTheory.Gal.W2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCorrChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem map_star_inv_mul {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (hdet : H.det ≠ 0) :
    (H.map star)⁻¹ * H.map star = 1 := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hu
  have hb : H.map star * (H⁻¹).map star = 1 := by
    have h := congrArg (fun M => (starRingEnd ℂ).mapMatrix M) hHi
    simp only [map_mul, map_one] at h
    exact h
  have hi : (H.map star)⁻¹ = (H⁻¹).map star := Matrix.inv_eq_right_inv hb
  rw [hi]
  exact mul_eq_one_comm.mp hb

theorem UpperTheory.Gal.W2.corrChart_of :
    UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.PerLin → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.CorrChart := by
  intro hAd hLin hFib O _ bar g ρ D X s A _ S k Z c₁ c₂ P₀ M₀ hP₀ hM₀ ga H hH L hL C hC hC'' z
  obtain ⟨hdet, hcomm, -⟩ := hAd O bar g ρ D P₀ M₀ hP₀ hM₀ ga H hH
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hdet
  have hHi : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H hu
  have hiH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H hu
  have hbi := map_star_inv_mul H hdet
  set C'' := H * C * (H.map star)⁻¹ with hC''def

  let P'' : D.La →+ (Fin g → ℂ) := (Matrix.toLin' H⁻¹).toAddMonoidHom.comp (perC P₀ C'')
  have hP''apply : ∀ x, P'' x = H⁻¹ *ᵥ perC P₀ C'' x := fun x => by
    show Matrix.toLin' H⁻¹ (perC P₀ C'' x) = _
    rw [Matrix.toLin'_apply]
  have hdetInv : (H⁻¹).det ≠ 0 := by
    intro h0
    have h1 : (H⁻¹ * H).det = 1 := by rw [hiH, Matrix.det_one]
    rw [Matrix.det_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hcommInv : ∀ a, ρ a * H⁻¹ = H⁻¹ * ρ a := fun a => by
    calc ρ a * H⁻¹ = H⁻¹ * (H * ρ a) * H⁻¹ := by
            rw [← Matrix.mul_assoc, hiH, Matrix.one_mul]
      _ = H⁻¹ * (ρ a * H) * H⁻¹ := by rw [hcomm a]
      _ = H⁻¹ * ρ a * (H * H⁻¹) := by simp only [Matrix.mul_assoc]
      _ = H⁻¹ * ρ a := by rw [hHi, Matrix.mul_one]
  have hP'' : IsPeriod D ρ P'' :=
    hLin O bar g ρ D (perC P₀ C'') P'' H⁻¹ hC'' hdetInv hcommInv hP''apply
  have hga : ∀ x, P'' (ga x) = perC P₀ C x := fun x => by
    rw [hP''apply, perC_apply, perC_apply, hH.2 x, GlobalTheory.PerCoordU.star_mulVec_map,
      Matrix.mulVec_mulVec, hC''def]
    have e : H * C * (H.map star)⁻¹ * H.map star = H * C := by
      rw [Matrix.mul_assoc, hbi, Matrix.mul_one]
    rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hcorr := hL (perC P₀ C) P'' hC hP'' hga z
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear (Matrix.toLin' H) (Matrix.toLin' H⁻¹)
    (by rw [← Matrix.toLin'_mul, hHi, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, hiH, Matrix.toLin'_one])
  have happ : ∀ v, h v = H *ᵥ v := fun v => by
    show Matrix.toLin' H v = _
    rw [Matrix.toLin'_apply]
  have hfib := (hFib O bar g ρ D X s A S k P'' hP'').2.2.2.2 (perC P₀ C'') h hC''
    (fun x => by rw [happ, hP''apply, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]) (L z)
  have hz : fibMap H L z = fun j => h (L z j) := by
    funext j
    rw [happ]
    simp [fibMap, Matrix.toLin'_apply]
  rw [hz, hfib]
  exact hcorr
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDetOfCharpoly
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma det_one_sub_smul_matrix {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (y : ℂ) :
    (1 - y • M).det = Polynomial.eval y M.charpoly.reverse := by
  rw [Matrix.reverse_charpoly, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.one_apply]; ring
  · simp [Matrix.one_apply, h]; ring

private lemma det_one_sub_smul_linear {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V) (y : ℂ) :
    LinearMap.det (1 - y • f) = Polynomial.eval y f.charpoly.reverse := by
  classical
  let b := Module.finBasis ℂ V
  rw [← LinearMap.det_toMatrix b, map_sub, map_smul, LinearMap.toMatrix_one,
    det_one_sub_smul_matrix, LinearMap.charpoly_toMatrix]

theorem UpperTheory.Gal.W2.detOfCharpoly_of :
    UpperTheory.Gal.W2.DetOfCharpoly := by
  intro V W _ _ _ _ _ _ T Θ d A h y
  rw [det_one_sub_smul_linear, det_one_sub_smul_linear, ← Polynomial.eval_mul,
    ← Polynomial.reverse_mul_of_domain, ← h, det_one_sub_smul_matrix]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PDetReal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.detReal_of :
    UpperTheory.Gal.W2.DetReal := by
  intro W _ _ _ f
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq, Complex.mul_conj]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PExpImm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.expImm_of :
    UpperTheory.Gal.W2.FlatComp → UpperTheory.Gal.W2.FlatPre → UpperTheory.Gal.W2.PbFlat → UpperTheory.Gal.W2.ExpImm0 → UpperTheory.Gal.W2.ExpImm := by
  intro hcomp hpre hpb h0 X A _ g y e he z₀ w hw
  apply h0 X A g y e he w
  have hsplit : ∀ z, e z = e (-z₀) * e (z₀ + z) := by
    intro z
    rw [← he.1, neg_add_cancel_left]
  have hhol : IsHolTo Set.univ (fun z => Over.Hom.left (e (z₀ + z))) :=
    GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp (φ := fun z => z₀ + z) he.2.2.1 isOpen_univ
      (by fun_prop) (Set.mapsTo_univ _ _)
  have hflat : Flat (fun z => Over.Hom.left (e (z₀ + z))) 0 w := by
    have hd : HasFDerivAt (fun z : Fin g → ℂ => z₀ + z) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
      (hasFDerivAt_id 0).const_add z₀
    refine (hpre (Fin g → ℂ) (Fin g → ℂ) A.left Set.univ (fun z => Over.Hom.left (e z)) he.2.2.1
      (fun z => z₀ + z) _ 0 w hd (Set.mem_univ _)).2 ?_
    simpa using hw
  have hpbA : IsPullback (fst A A).left (snd A A).left A.hom A.hom :=
    Over.isPullback_of_binaryFan_isLimit _ (tensorProductIsBinaryProduct A A)
  have h1 : (fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (fst A A).left) =
      fun _ => (e (-z₀)).left := by
    funext z
    rw [← Over.comp_left, lift_fst]
  have h2 : (fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (snd A A).left) =
      fun z => (e (z₀ + z)).left := by
    funext z
    rw [← Over.comp_left, lift_snd]
  have hconstHol : IsHolTo Set.univ (fun _ : Fin g → ℂ => (e (-z₀)).left) := by
    intro U f
    refine ⟨?_, differentiableOn_const _⟩
    by_cases hU : ⊤ ≤ (e (-z₀)).left ⁻¹ᵁ U
    · simp [hU]
    · simp [hU]
  have hconstFlat : Flat (fun _ : Fin g → ℂ => (e (-z₀)).left) 0 w := by
    intro U f _
    simp
  have hs : Flat (fun z => (lift (e (-z₀)) (e (z₀ + z))).left) 0 w := by
    refine hpb (Fin g → ℂ) _ A.left A.left X (fst A A).left (snd A A).left A.hom A.hom hpbA Set.univ
      _ 0 w isOpen_univ (Set.mem_univ _) ?_ ?_ ?_ ?_
    · beta_reduce
      rw [h1]
      exact hconstHol
    · beta_reduce
      rw [h2]
      exact hhol
    · beta_reduce
      rw [h1]
      exact hconstFlat
    · beta_reduce
      rw [h2]
      exact hflat
  have hfe : (fun z => (e z).left) =
      fun z => (lift (e (-z₀)) (e (z₀ + z))).left ≫ (μ : A ⊗ A ⟶ A).left := by
    funext z
    rw [← Over.comp_left, ← Hom.mul_def, ← hsplit]
  rw [hfe]
  exact hcomp (Fin g → ℂ) _ A.left (μ : A ⊗ A ⟶ A).left _ 0 w hs
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

open GlobalTheory.HolHom in
theorem UpperTheory.Gal.W2.flatAffine_of :
    UpperTheory.Gal.W2.FlatAffine := by
  intro V _ _ Y B s v₀ w hB hv₀ hs W hW hsW hder U f hU
  have hhol := holAt_of_isHolTo hs hv₀
  have hpU := (le_preimage_iff _ _).1 hU
  have hpW := (le_preimage_iff _ _).1 hsW
  obtain ⟨g, hgle, hpg⟩ := hW.exists_basicOpen_le (V := U) ⟨_, hpU⟩ hpW
  have hDW : Y.basicOpen g ≤ W := Y.basicOpen_le g
  letI := (Y.presheaf.map (homOfLE hDW).op).hom.toAlgebra
  haveI := hW.isLocalization_basicOpen g
  obtain ⟨⟨h, ⟨_, k, rfl⟩⟩, e⟩ :=
    IsLocalization.surj (Submonoid.powers g) ((Y.presheaf.map (homOfLE hgle).op).hom f)
  simp only [RingHom.algebraMap_toAlgebra] at e
  have hD0 : ⊤ ≤ s v₀ ⁻¹ᵁ Y.basicOpen g := (le_preimage_iff _ _).2 hpg
  have hev : ∀ᶠ v in 𝓝 v₀, ⊤ ≤ s v ⁻¹ᵁ Y.basicOpen g := (hhol _ hD0).1
  have heq : (fun v => valAt' (s v) W h) =ᶠ[𝓝 v₀]
      (fun v => valAt' (s v) U f * valAt' (s v) W g ^ k) := by
    filter_upwards [hev] with v hv
    have e' := congrArg (HolHom.evalHom (s v) _ hv) e
    simp only [map_mul, map_pow, ← valR_eq] at e'
    rw [valR_res (s v) hgle f hv, valR_res (s v) hDW g hv, valR_res (s v) hDW h hv] at e'
    simp only [valAt'_eq_valR]
    exact e'.symm
  have hFd := (hhol U hU).2 f
  have hGd := (hhol W hsW).2 g
  have hHd := (hhol W hsW).2 h
  have hL := (hFd.hasFDerivAt.mul (hGd.hasFDerivAt.pow k)).congr_of_eventuallyEq heq
  have huniq := hL.unique hHd.hasFDerivAt
  have hw := congrArg (fun L => L w) huniq
  have hG0 : valAt' (s v₀) W g ≠ 0 := (le_basicOpen_iff _ hsW g).1 hD0
  simp [hder g, hder h, hG0] at hw
  exact hw
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.flatComp_of :
    UpperTheory.Gal.W2.FlatComp := by
  intro V _ _ Y Y' f s v₀ w h U a hU
  have hU' : ⊤ ≤ s v₀ ⁻¹ᵁ (f ⁻¹ᵁ U) := hU
  have e : (fun v => valAt' (s v ≫ f) U a) =
      fun v => valAt' (s v) (f ⁻¹ᵁ U) ((f.appLE U (f ⁻¹ᵁ U) le_rfl).hom a) :=
    funext fun v => GlobalTheory.ExpCoord.valAt'_comp (s v) f U a
  rw [e]
  exact h _ _ hU'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFlatPre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.flatPre_of :
    UpperTheory.Gal.W2.FlatPre := by
  intro V _ _ V' _ _ Y B s hs φ φ' v₀ w hφ hB
  have key : ∀ (U : Y.Opens) (f : Γ(Y, U)), ⊤ ≤ s (φ v₀) ⁻¹ᵁ U →
      fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ w =
        fderiv ℂ (fun b => valAt' (s b) U f) (φ v₀) (φ' w) := by
    intro U f hU
    obtain ⟨hopen, hdiff⟩ := hs U f
    have hmem : φ v₀ ∈ {b ∈ B | ⊤ ≤ s b ⁻¹ᵁ U} := ⟨hB, hU⟩
    have hd : DifferentiableAt ℂ (fun b => valAt' (s b) U f) (φ v₀) :=
      (hdiff _ hmem).differentiableAt (hopen.mem_nhds hmem)
    have hc := hd.hasFDerivAt.comp v₀ hφ
    have he : fderiv ℂ (fun v => valAt' (s (φ v)) U f) v₀ = _ := hc.fderiv
    rw [he]
    rfl
  constructor
  · intro h U f hU
    rw [← key U f hU]
    exact h U f hU
  · intro h U f hU
    rw [key U f hU]
    exact h U f hU
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTriCharpoly
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.triCharpoly_of :
    UpperTheory.Gal.W2.TriCharpoly := by
  intro V W _ _ _ _ _ _ T Θ R G hG
  let bV := Module.finBasis ℂ V
  let bW := Module.finBasis ℂ W
  have hM : LinearMap.toMatrix (bV.prod bW) (bV.prod bW) G =
      Matrix.fromBlocks (LinearMap.toMatrix bV bV T) 0 (LinearMap.toMatrix bV bW R)
        (LinearMap.toMatrix bW bW Θ) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Module.Basis.prod_apply, hG]
  rw [← LinearMap.charpoly_toMatrix G (bV.prod bW), ← LinearMap.charpoly_toMatrix T bV,
    ← LinearMap.charpoly_toMatrix Θ bW, hM, Matrix.charpoly_fromBlocks_zero₁₂]
end

