module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateLogNormParallelogramLaw
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetRootCong

theorem map_sigR {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem quot_fixed {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : B →+* B) (x Y : Aˣ) (u y y' : B)
    (hx : f x = u * s (f x)) (hy : y = u * s y) (hyy : y * y' = 1) (hY : f (Y⁻¹ : Aˣ) = y') :
    s ((Units.map f.toMonoidHom (x * Y⁻¹) : Bˣ) : B) = (Units.map f.toMonoidHom (x * Y⁻¹) : Bˣ) := by
  have hs : s y * s y' = 1 := by rw [← map_mul, hyy, map_one]
  change s (f ((x : A) * (Y⁻¹ : Aˣ))) = f ((x : A) * (Y⁻¹ : Aˣ))
  rw [map_mul, hY, map_mul]
  linear_combination (-y') * hx + (s (f x) * s y' * y') * hy - (s (f x) * s y') * hyy
    + (u * s (f x) * y') * hs

theorem finPart_sigR (D : D7) (x : AE D) :
    finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) :=
  map_sigR _ _ x

theorem exists_idele (D : D7) (y y' : Af D.host.F ⊗[D.host.F] D.host.E) (h : y * y' = 1) :
    ∃ Y : (AE D)ˣ, infPart D (Y : AE D) = 1 ∧ finPart D (Y : AE D) = y ∧
      finPart D ((Y⁻¹ : (AE D)ˣ) : AE D) = y' := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h1 : e.symm (1, y) * e.symm (1, y') = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, h, mul_one]
    exact map_one e.symm
  refine ⟨⟨e.symm (1, y), e.symm (1, y'), h1, by rw [mul_comm, h1]⟩,
    (he _).1.symm.trans ?_, (he _).2.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

theorem exists_idF (D : D7) (b : (Af D.host.F)ˣ) :
    ∃ a : (AF D.host.F)ˣ, finPart D (idF D a : AE D) =
      algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) b := by
  refine ⟨⟨(1, b), (1, (b⁻¹ : (Af D.host.F)ˣ)), Prod.ext (mul_one _) b.mul_inv,
    Prod.ext (mul_one _) b.inv_mul⟩, ?_⟩
  rfl

theorem char_root_eq_one : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle) (N : ℕ), Odd N → (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → (∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1) → ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → (∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) → c x = 1 := by
  intro D V c N hN hF hinf hcong g x hx ⟨w, hw, hwe⟩
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hwe
  have hn := GlobalTheory.RecDict.det_finHom_norm V g
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := _root_.GlobalTheory.OddRoot.exists_root_odd D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_idele D y y' hyy
  have hcY : c Y = 1 := hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V g).1.det = finPart D (matHom V g).1.det := ((finPart D).map_det _).symm
  have hxf : finPart D (x : AE D) =
      (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hdet, ← finPart_sigR, ← RingHom.map_mul]
    exact congrArg _ hx
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom (x * Y⁻¹)) (quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)
  obtain ⟨a, ha⟩ := exists_idF D b
  have hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D) :=
    ha.trans (congrArg Units.val hb)
  have h1 := hinf (x * Y⁻¹ * (idF D a)⁻¹) (by
    rw [Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  simpa [hcY, hF a] using h1

end GlobalTheory.DetRootCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeries
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTransl

theorem intMv_iff {p : ℕ} [Fact p.Prime] (f : PowerSeries ℂ_[p]) : IntegralMv f ↔ GlobalTheory.EvenTheta.IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

theorem transl_holds : ∀ D : D7, GL3Theta.transl D := by
  intro D p _ cc δ g hg t ht
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, -⟩ := hg'
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, -, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  rw [← hΛ] at hlat huse
  have hlat' : GlobalTheory.EvenTheta.IsLat g.abelian₂ := hlat
  have hred := _root_.GlobalTheory.TorsionAbscissa.norm_xAt_le D p cc δ g hg
  have hun := _root_.GlobalTheory.ThetaUnit.tau_eq_C_mul D p cc δ g hg hred
  obtain ⟨n, hn, hnp, hnt⟩ := ht.2
  have hM : logc g t = 0 := by
    refine _root_.GlobalTheory.torsion_parallelogram_vanish g.abelian₂ hlat' n hn (logc g) (fun s hs => by simp [logc, hs]) ?_ ?_ t hnt
    · intro s ω hs hω
      by_cases h1 : s ∈ g.abelian₂
      · simp [logc, h1, add_mem h1 hω]
      · have h2 : s + ω ∉ g.abelian₂ := fun h => h1 (by simpa using sub_mem h hω)
        simp only [logc, h1, h2, if_false]
        rw [_root_.GlobalTheory.ThetaTransl.cval_norm_periodic D p cc δ g hg s ω ⟨n, hn, hs⟩ hω]
    · intro P Q hP hQ hQ'
      exact _root_.GlobalTheory.ThetaPar.par_holds D p cc δ g hg hred hun P Q ⟨n, hn, hnp, hP⟩ ⟨hQ', n, hn, hnp, hQ⟩
  have hA : GlobalTheory.EvenTheta.AlgEnt (U1 g.abelian₂ t (sgStar g.abelian₂)) := ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse t ⟨n, hn, hnt⟩⟩
  obtain ⟨hq, hc0⟩ := (GlobalTheory.SerTransport.transport p g).2.2.1 _ hA
  have hne : U1 g.abelian₂ t (sgStar g.abelian₂) 0 ≠ 0 := by
    simp only [U1, zero_add, ne_eq, mul_eq_zero, Complex.exp_ne_zero, or_false]
    exact fun h => ht.1 ((hlat'.sg_eq_zero t).1 h)
  have hcne : cval g t ≠ 0 := by
    unfold cval lamC
    rw [dite_eq_left hq]
    exact (map_ne_zero g.lam).2 fun h => hne (congrArg Subtype.val h)
  have hc1 : ‖cval g t‖ = 1 := by
    simp only [logc, ht.1, if_false] at hM
    rcases Real.log_eq_zero.1 hM with h | h | h
    · exact absurd (norm_eq_zero.1 h) hcne
    · exact h
    · linarith [norm_nonneg (cval g t)]
  obtain ⟨w, hw, -, hτ⟩ := hun t ht
  refine ⟨?_, ?_⟩
  · rw [intMv_iff]
    change GlobalTheory.EvenTheta.IntSer (tau g t)
    intro k
    rw [hτ, PowerSeries.coeff_C_mul, norm_mul, hc1, one_mul]
    exact hw k
  · rw [hc0]; exact hc1

end GlobalTheory.ThetaTransl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetColumnOperationsModelParameter
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
namespace GlobalTheory.FrobStick

theorem det_column_alg {R : Type*} [CommRing R] (x e w q : Fin 3 → R) (ε r a₁ a₃ S D1 D2 D3 : R)
    (hq : ∀ i, q i * w i = 1) (hu : IsUnit (2 * ε ^ 4))
    (h : Matrix.det (Matrix.of fun i j => (![ε ^ 3 * x i ^ 3 * e i ^ 3,
      ε * e i ^ 3 * (x i * q i + ε ^ 2 * r * x i ^ 3),
      e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)] : Fin 3 → R) j) =
      2 * (ε * S) * (ε * D1) * (ε * D2) * (ε * D3)) :
    (x 0 ^ 3 * w 0 * (x 2 - x 1) + x 1 ^ 3 * w 1 * (x 0 - x 2) + x 2 ^ 3 * w 2 * (x 1 - x 0))
      * e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 = w 0 * w 1 * w 2 * S * D1 * D2 * D3 := by
  have hrow : ∀ i, e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)
      = e i ^ 3 * (a₁ * x i * q i + a₃ * x i ^ 3 - 2 * q i) := fun i => by
    linear_combination e i ^ 3 * a₃ * x i ^ 3 * hq i
  simp only [hrow] at h
  rw [Matrix.det_fin_three] at h
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  have h2 : 2 * ε ^ 4 * (e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 *
      (x 0 ^ 3 * (q 1 * q 2) * (x 2 - x 1) + x 1 ^ 3 * (q 0 * q 2) * (x 0 - x 2)
        + x 2 ^ 3 * (q 0 * q 1) * (x 1 - x 0))) = 2 * ε ^ 4 * (S * D1 * D2 * D3) := by
    linear_combination h
  have h3 := hu.mul_left_cancel h2
  have h12 : q 1 * q 2 * (w 1 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h02 : q 0 * q 2 * (w 0 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h01 : q 0 * q 1 * (w 0 * w 1) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  linear_combination w 0 * w 1 * w 2 * h3
    - e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 * (x 0 ^ 3 * w 0 * (x 2 - x 1) * h12
      + x 1 ^ 3 * w 1 * (x 0 - x 2) * h02 + x 2 ^ 3 * w 2 * (x 1 - x 0) * h01)

theorem det_column_ops : ∀ (p : ℕ) [Fact p.Prime] (E wq : PowerSeries ℂ_[p]) (ε r a₁ a₃ : ℂ_[p]) (s d₁ d₂ d₃ : MvPowerSeries (Fin 3) ℂ_[p]), ε ≠ 0 → PowerSeries.constantCoeff wq = 1 → MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff d₁ = 0 → MvPowerSeries.constantCoeff d₂ = 0 → MvPowerSeries.constantCoeff d₃ = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (![PowerSeries.C (ε ^ 3) * PowerSeries.X ^ 3 * E ^ 3, PowerSeries.C ε * E ^ 3 * (PowerSeries.X * wq⁻¹ + PowerSeries.C (ε ^ 2 * r) * PowerSeries.X ^ 3), E ^ 3 * wq⁻¹ * (PowerSeries.C a₁ * PowerSeries.X + PowerSeries.C a₃ * PowerSeries.X ^ 3 * wq - 2)] j) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst s (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₁ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₂ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₃ (PowerSeries.C ε * PowerSeries.X * E) → ((GL3Theta.Xv 0) ^ 3 * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 2 - GL3Theta.Xv 1) + (GL3Theta.Xv 1) ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 0 - GL3Theta.Xv 2) + (GL3Theta.Xv 2) ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 1 - GL3Theta.Xv 0)) * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 = PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (s * PowerSeries.subst s E) * (d₁ * PowerSeries.subst d₁ E) * (d₂ * PowerSeries.subst d₂ E) * (d₃ * PowerSeries.subst d₃ E) := by
  intro p _ E wq ε r a₁ a₃ s d₁ d₂ d₃ hε hw hs h1 h2 h3 h
  have hC : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), HasSubst a → ∀ c : ℂ_[p],
      PowerSeries.subst a (PowerSeries.C c : PowerSeries ℂ_[p]) = MvPowerSeries.C c := by
    intro a ha c
    rw [← coe_substAlgHom ha]
    exact (substAlgHom ha).commutes c
  have hlin : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (PowerSeries.C ε * PowerSeries.X * E) =
        MvPowerSeries.C ε * (a * PowerSeries.subst a E) := by
    intro a ha
    have ha' : HasSubst a := HasSubst.of_constantCoeff_zero ha
    rw [subst_mul ha', subst_mul ha', hC a ha', subst_X ha', mul_assoc]
  have hX : ∀ i : Fin 3, HasSubst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) := fun i =>
    HasSubst.of_constantCoeff_zero (by simp [GL3Theta.Xv])
  rw [hlin s hs, hlin d₁ h1, hlin d₂ h2, hlin d₃ h3] at h
  refine det_column_alg (fun i => (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]))
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) E)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq⁻¹)
    (MvPowerSeries.C ε) (MvPowerSeries.C r) (MvPowerSeries.C a₁) (MvPowerSeries.C a₃) _ _ _ _
    ?_ ?_ ?_
  · intro i
    rw [← subst_mul (hX i), PowerSeries.inv_mul_cancel _ (by rw [hw]; exact one_ne_zero),
      ← coe_substAlgHom (hX i), map_one]
  · have : (2 * MvPowerSeries.C ε ^ 4 : MvPowerSeries (Fin 3) ℂ_[p]) =
        MvPowerSeries.C (2 * ε ^ 4) := by
      rw [map_mul, map_pow, map_ofNat]
    rw [this]
    exact (IsUnit.mk0 _ (mul_ne_zero two_ne_zero (pow_ne_zero _ hε))).map _
  · rw [← h]
    congr 1
    ext1 i j
    have hCi := hC _ (hX i)
    have hXi := subst_X (R := ℂ_[p]) (hX i)
    rw [← coe_substAlgHom (hX i)] at hCi hXi
    simp only [Matrix.of_apply]
    rw [← coe_substAlgHom (hX i)]
    fin_cases j
    all_goals
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, map_mul, map_pow, map_add, map_sub, map_ofNat, hCi, hXi]

end GlobalTheory.FrobStick
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactImageEqUniv
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.AutomorphicL2Cocompact

theorem isOpenMap_mk {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) :
    IsOpenMap (mk Γ) := by
  intro U hU
  have h : mk Γ ⁻¹' (mk Γ '' U) = ⋃ γ : Γ, (fun x => ((γ : G))⁻¹ * x) ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, e⟩
      obtain ⟨γ, rfl⟩ := mk_eq_iff.1 e
      exact ⟨γ, by simpa using hy⟩
    · rintro ⟨γ, hγ⟩
      exact ⟨_, hγ, mk_eq_iff.2 ⟨γ, by simp⟩⟩
  refine isOpen_coinduced.2 ?_
  change IsOpen (mk Γ ⁻¹' (mk Γ '' U))
  rw [h]
  exact isOpen_iUnion fun γ => hU.preimage (by fun_prop)

theorem exists_compact_image_eq_univ {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (Γ : Subgroup G) [CompactSpace (Quot Γ)] :
    ∃ C : Set G, IsCompact C ∧ mk Γ '' C = Set.univ := by
  classical
  choose K hK hK' using fun x : G => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : G => mk Γ '' interior (K x))
    (fun x => isOpenMap_mk Γ _ isOpen_interior) (fun q _ => by
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      exact Set.mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hK' x), rfl⟩)
  refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hK x, Set.eq_univ_of_forall fun q => ?_⟩
  obtain ⟨x, hx, y, hy, e⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
  exact ⟨y, Set.mem_iUnion₂.2 ⟨x, hx, interior_subset hy⟩, e⟩

theorem cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], CompactSpace (Quot Γ) → IsFiniteMeasure (quotMeasure Γ μ) ∧ (∃ C : Set G, IsCompact C ∧ mk Γ '' C = Set.univ) ∧ ∀ φ : G → ℂ, LeftInv Γ φ → Continuous φ → MemL2Quotient Γ μ φ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ hc
  obtain ⟨C, hC, hCe⟩ := exists_compact_image_eq_univ Γ
  have hfin : IsFiniteMeasure (quotMeasure Γ μ) :=
    ⟨(quotMeasure_le MeasurableSet.univ hCe.ge).trans_lt hC.measure_lt_top⟩
  refine ⟨hfin, ⟨C, hC, hCe⟩, fun φ hφ hcont => ⟨hφ, ?_⟩⟩
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  refine MemLp.of_bound ?_ B (Filter.Eventually.of_forall fun q => ?_)
  · rw [aestronglyMeasurable_quotMeasure_iff_lift, hφ.lift_descend]
    exact hcont.aestronglyMeasurable
  · obtain ⟨x, hx, rfl⟩ := hCe.ge (Set.mem_univ q)
    rw [hφ.descend_mk]
    exact hB x hx

end GlobalTheory.AutomorphicL2Cocompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitPart
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.VacuumEven

open GlobalTheory.VacuumScalar GlobalTheory.NormSum.VacMove

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem exists_scalar (hc : Crv D cc δ) {e0 : VC D N N' → ℂ}
    (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (W : WeilO D cc δ N N' e0) {g : GA D N} {g' : GA D N'}
    {L L'} (hL : Moves D (g : GL (Fin N) (AE D)) L) (hL' : Moves D (g' : GL (Fin N') (AE D)) L') :
    ∃ c : ℂ, W.Om g g' e0 = c •
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') e0 := by
  have hg1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, sd_of_moves hL, sd_of_moves hL', rfl⟩
  obtain ⟨-, hTh, -, -⟩ := _root_.GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _ k0 k1 e0 he
  obtain ⟨a1, -, a3, a4, -, a6, -⟩ := lattice_facts hc he W.nz hL hL'
  obtain ⟨hline, hW, -⟩ := _root_.GlobalTheory.ThetaLine.theta_line D hg1 cc δ hc N N' _ k1
  have heT : e0 ∈ TT D (tor0 D cc δ) N N' := ⟨he.1, 1, one_pos, fun y hy => by rw [one_smul]; exact a6 y hy⟩
  have hF := W.maps g g' e0 heT
  refine hline _ ⟨hF.1, fun x hx => ?_⟩ _ hTh a1
  suffices hs : Wd D (tor0 D cc δ) x (W.Om g g' e0) = W.Om g g' e0 by
    rw [hW x hx] at hs; exact congrFun hs
  have hWT : Wd D (tor0 D cc δ) x (W.Om g g' e0) ∈ TT D (tor0 D cc δ) N N' := by
    obtain ⟨hd, m, hm, hfix⟩ := hF
    refine ⟨Wd_differentiable _ hd, _, Nat.mul_pos hm (Nat.pos_of_ne_zero a4), fun y hy => ?_⟩
    have h1 := AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_relIndex_mem (La D (tor0 D cc δ) L L') hy) m
    have h2 := hfix _ (AddSubgroup.nsmul_mem _ hy
      ((La D (tor0 D cc δ) L L').relIndex (La0 D (tor0 D cc δ) N N')))
    rw [smul_smul] at h1 h2
    rw [← Wl_apply, ← Wl_apply, ← Module.End.mul_apply, ← a3 _ h1 _ hx, add_comm, a3 _ hx _ h1,
      Module.End.mul_apply, Wl_apply, Wl_apply, h2]
    rfl
  obtain ⟨y, hy, hyW⟩ := _root_.GlobalTheory.WeilEquiv.om_wd_moved D hg1 cc δ hc.1.1 N N' e0 W g⁻¹ g g'⁻¹ g' L _ L' _ hL hL'
    (by rw [inv_mul_cancel]; exact moves_one D N) (by rw [inv_mul_cancel]; exact moves_one D N') x hx _ hF
  rw [← W.mul _ _ _ _ _ heT, inv_mul_cancel, inv_mul_cancel, W.one _ heT, ← Wl_apply y, a6 y hy] at hyW
  have := congrArg (W.Om g g') hyW
  rwa [← W.mul _ _ _ _ _ hWT, mul_inv_cancel, mul_inv_cancel, W.one _ hWT] at this

end GlobalTheory.VacuumEven
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtremalNegativeSets
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.FWT

namespace GlobalTheory.Cmp.ExtremalNegativeSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Idx

variable {n : ℕ} {ε : Fin n → Bool}

theorem mem_negS {a : Fin n} : a ∈ negS ε ↔ ε a = false := by simp [negS]

theorem revNeg_anti {a b : Fin n} (hab : a < b) (ha : ε a = false) (hb : ε b = false) :
    revNeg ε b < revNeg ε a := by
  have ha' : a ∈ negS ε := mem_negS.2 ha
  have hb' : b ∈ negS ε := mem_negS.2 hb
  rw [show revNeg ε a = (revOn ε ⟨a, ha'⟩ : Fin n) from Equiv.Perm.ofSubtype_apply_of_mem _ ha',
    show revNeg ε b = (revOn ε ⟨b, hb'⟩ : Fin n) from Equiv.Perm.ofSubtype_apply_of_mem _ hb']
  have h1 : ((negS ε).orderIsoOfFin rfl).symm ⟨a, ha'⟩ < ((negS ε).orderIsoOfFin rfl).symm ⟨b, hb'⟩ :=
    (OrderIso.lt_iff_lt _).2 (Subtype.mk_lt_mk.2 hab)
  exact ((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h1)

end Idx

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end GlobalTheory.Cmp.ExtremalNegativeSets

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusOneDatumModelLatticeAlgebraicData
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStick.AtData

theorem weierstrass_translate_zero_eq_self (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

theorem half_gen {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) : ∃ v : ℂ, v ∉ Λ ∧ InRationalLattice Λ v := by
  obtain ⟨w₁, w₂, hli, rfl⟩ := hlat
  refine ⟨w₁ / 2, ?_, ⟨2, by norm_num, ?_⟩⟩
  · intro h
    rw [AddSubgroup.mem_closure_pair] at h
    obtain ⟨m, n, hmn⟩ := h
    have key := (LinearIndependent.pair_iff.1 hli) ((m : ℝ) - 1 / 2) (n : ℝ) (by
      have e : (m : ℂ) * w₁ + (n : ℂ) * w₂ = w₁ / 2 := by simpa [zsmul_eq_mul] using hmn
      simp only [Complex.real_smul]
      push_cast
      linear_combination e)
    have h1 : (m : ℝ) = 1 / 2 := by linarith [key.1]
    have h2 : (2 * m : ℝ) = 1 := by linarith
    have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
    omega
  · have : (2 : ℂ) * (w₁ / 2) = w₁ := by ring
    push_cast
    rw [this]
    exact AddSubgroup.subset_closure (by simp)

theorem atData : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → IsWq g.W g.wq ∧ IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧ AlgEnt (sgStar g.abelian₂) ∧ ∃ v : ℂ, v ∉ g.abelian₂ ∧ wpF g.abelian₂ v ∈ Qbar := by
  intro D p _ cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  obtain ⟨v, hv, hvq⟩ := half_gen hlat'
  refine ⟨hok.2.1, hlat', h2, h3, ⟨hlat'.differentiable, fun n => ?_⟩, v, hv, (hwp v hvq hv).1⟩
  have := huse 0 ⟨1, one_pos, by simp⟩ n
  rwa [weierstrass_translate_zero_eq_self] at this

end GlobalTheory.FrobStick.AtData
end

