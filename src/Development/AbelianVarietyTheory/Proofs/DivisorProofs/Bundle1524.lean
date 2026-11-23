module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointPrescribedFrameImages
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem cT_add' {a b : Type} (M N : Matrix a b S) : cT s (M + N) = cT s M + cT s N := by
  ext i k; simp [cT]

theorem cT_zero' {a b : Type} : cT s (0 : Matrix a b S) = 0 := by
  ext i k; simp [cT]

theorem cT_cT' (hs : ∀ x, s (s x) = x) {a b : Type} (M : Matrix a b S) : cT s (cT s M) = M := by
  ext i k; simp [cT, hs]

theorem cT_gram {n a b : ℕ} (hs : ∀ x, s (s x) = x) (J : Matrix (Fin n) (Fin n) S) (hJ : cT s J = J)
    (M : Matrix (Fin n) (Fin a) S) (N : Matrix (Fin n) (Fin b) S) :
    cT s (cT s M * J * N) = cT s N * J * M := by
  rw [cT_mul, cT_mul, cT_cT' s hs, hJ, Matrix.mul_assoc]

theorem gram_comb {n j m : ℕ} (J : Matrix (Fin n) (Fin n) S) (J0 : Matrix (Fin m) (Fin m) S)
    (A B : Matrix (Fin n) (Fin j) S) (Z : Matrix (Fin n) (Fin m) S)
    (pX pY : Matrix (Fin j) (Fin n) S) (p0 : Matrix (Fin m) (Fin n) S)
    (aa : cT s A * J * A = 0) (bb : cT s B * J * B = 0) (ab : cT s A * J * B = 1) (ba : cT s B * J * A = 1)
    (az : cT s A * J * Z = 0) (bz : cT s B * J * Z = 0) (za : cT s Z * J * A = 0) (zb : cT s Z * J * B = 0)
    (zz : cT s Z * J * Z = J0) :
    cT s (A * pX + Z * p0 + B * pY) * J * (A * pX + Z * p0 + B * pY) =
      cT s pX * pY + cT s p0 * J0 * p0 + cT s pY * pX := by
  have h1 : cT s A * (J * (A * pX + Z * p0 + B * pY)) = pY := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, aa, az, ab, Matrix.zero_mul, Matrix.one_mul, zero_add]
  have h2 : cT s Z * (J * (A * pX + Z * p0 + B * pY)) = J0 * p0 := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, za, zz, zb, Matrix.zero_mul, zero_add, add_zero]
  have h3 : cT s B * (J * (A * pX + Z * p0 + B * pY)) = pX := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, ba, bz, bb, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero]
  rw [cT_add', cT_add', cT_mul, cT_mul, cT_mul]
  simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, h3]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_invol (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (e : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => simp [sigR, hσ]

theorem cT_adMat (σ : E →ₐ[F] E) {a b : Type} (X : Matrix a b E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k; simp [cT, adMat, sigR, inclR]

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem images_ring {n j m : ℕ} (Ja Jai : Matrix (Fin n) (Fin n) S) (j0 k0 : Matrix (Fin m) (Fin m) S)
    (hJi : Jai * Ja = 1) (hk0 : k0 * j0 = 1)
    (c d C' D' : Matrix (Fin n) (Fin j) S) (z Z' : Matrix (Fin n) (Fin m) S)
    (cc : cT s c * Ja * c = 0) (dd : cT s d * Ja * d = 0) (cd : cT s c * Ja * d = 1) (dc : cT s d * Ja * c = 1)
    (cz : cT s c * Ja * z = 0) (dz : cT s d * Ja * z = 0) (zc : cT s z * Ja * c = 0) (zd : cT s z * Ja * d = 0)
    (zz : cT s z * Ja * z = j0)
    (sum : c * (cT s d * Ja) + z * (k0 * (cT s z * Ja)) + d * (cT s c * Ja) = 1)
    (cc' : cT s C' * Ja * C' = 0) (dd' : cT s D' * Ja * D' = 0) (cd' : cT s C' * Ja * D' = 1) (dc' : cT s D' * Ja * C' = 1)
    (cz' : cT s C' * Ja * Z' = 0) (dz' : cT s D' * Ja * Z' = 0) (zc' : cT s Z' * Ja * C' = 0) (zd' : cT s Z' * Ja * D' = 0)
    (zz' : cT s Z' * Ja * Z' = j0) :
    ∃ u : GL (Fin n) S, cT s u.1 * Ja * u.1 = Ja ∧ u.1 * c = C' ∧ u.1 * z = Z' ∧ u.1 * d = D' := by
  obtain ⟨pX, hpX⟩ : ∃ p, p = cT s d * Ja := ⟨_, rfl⟩
  obtain ⟨p0, hp0⟩ : ∃ p, p = k0 * (cT s z * Ja) := ⟨_, rfl⟩
  obtain ⟨pY, hpY⟩ : ∃ p, p = cT s c * Ja := ⟨_, rfl⟩
  rw [← hpX, ← hp0, ← hpY] at sum
  have Xc : pX * c = 1 := by rw [hpX, dc]
  have Xz : pX * z = 0 := by rw [hpX, dz]
  have Xd : pX * d = 0 := by rw [hpX, dd]
  have Yc : pY * c = 0 := by rw [hpY, cc]
  have Yz : pY * z = 0 := by rw [hpY, cz]
  have Yd : pY * d = 1 := by rw [hpY, cd]
  have Oc : p0 * c = 0 := by rw [hp0, Matrix.mul_assoc, zc, Matrix.mul_zero]
  have Oz : p0 * z = 1 := by rw [hp0, Matrix.mul_assoc, zz, hk0]
  have Od : p0 * d = 0 := by rw [hp0, Matrix.mul_assoc, zd, Matrix.mul_zero]
  obtain ⟨g, hg⟩ : ∃ g, g = C' * pX + Z' * p0 + D' * pY := ⟨_, rfl⟩
  have gram : cT s g * Ja * g = Ja := by
    rw [hg, gram_comb s Ja j0 C' D' Z' pX pY p0 cc' dd' cd' dc' cz' dz' zc' zd' zz',
      ← gram_comb s Ja j0 c d z pX pY p0 cc dd cd dc cz dz zc zd zz, sum, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hl : (Jai * cT s g * Ja) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g), gram, hJi]
  have hr : g * (Jai * cT s g * Ja) = 1 := mul_eq_one_comm.1 hl
  refine ⟨⟨g, Jai * cT s g * Ja, hr, hl⟩, gram, ?_, ?_, ?_⟩
  · change g * c = C'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xc, Oc, Yc, Matrix.mul_zero, Matrix.mul_one, add_zero]
  · change g * z = Z'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xz, Oz, Yz, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]
  · change g * d = D'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xd, Od, Yd, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adMat_gram (σ : E →ₐ[F] E) {n a b : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin a) E)
    (Y : Matrix (Fin n) (Fin b) E) (R : Matrix (Fin a) (Fin b) E) (h : cT (σ : E →+* E) X * J * Y = R) :
    cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F Y = adMat F R := by
  rw [cT_adMat, adMat, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem adMat_zero' {a b : Type} : adMat F (0 : Matrix a b E) = 0 := Matrix.map_zero _ (map_zero _)

theorem adMat_one' {a : Type} [DecidableEq a] : adMat F (1 : Matrix a a E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_mul' {a b c : Type} [Fintype b] (X : Matrix a b E) (Y : Matrix b c E) :
    adMat F (X * Y) = adMat F X * adMat F Y := Matrix.map_mul

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

theorem exists_point_images :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (C' D' : Matrix (Fin n) (Fin j) (AF F ⊗[F] E)) (Z' : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)), cT (sigR (AF F) σ) C' * adMat F J * C' = 0 → cT (sigR (AF F) σ) D' * adMat F J * D' = 0 → cT (sigR (AF F) σ) C' * adMat F J * D' = 1 → cT (sigR (AF F) σ) C' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) D' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) Z' * adMat F J * Z' = adMat F J₀ → ∃ g : GAd σ J, (matHom _ σ J g).1 * adMat F C = C' ∧ (matHom _ σ J g).1 * adMat F Z = Z' ∧ (matHom _ σ J g).1 * adMat F D = D' := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr C' D' Z' cc dd cd cz dz zz
  have hσ : ∀ x, σ (σ x) = x := sig_invol fr.cm
  have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := sigR_invol σ hσ
  have hJ : cT (sigR (AF F) σ) (adMat F J) = adMat F J := by rw [cT_adMat, cT_form fr.herm]
  have dc : cT (sigR (AF F) σ) D' * adMat F J * C' = 1 := by
    rw [← cT_gram _ hs _ hJ, cd, cT_one]
  have zc : cT (sigR (AF F) σ) Z' * adMat F J * C' = 0 := by rw [← cT_gram _ hs _ hJ, cz, cT_zero']
  have zd : cT (sigR (AF F) σ) Z' * adMat F J * D' = 0 := by rw [← cT_gram _ hs _ hJ, dz, cT_zero']
  have acc := adMat_gram (F := F) σ J C C 0 fr.cc
  have add := adMat_gram (F := F) σ J D D 0 fr.dd
  have acd := adMat_gram (F := F) σ J C D 1 fr.cd
  have adc := adMat_gram (F := F) σ J D C 1 fr.dc
  have acz := adMat_gram (F := F) σ J C Z 0 fr.cz
  have adz := adMat_gram (F := F) σ J D Z 0 fr.dz
  have azc := adMat_gram (F := F) σ J Z C 0 fr.zc
  have azd := adMat_gram (F := F) σ J Z D 0 fr.zd
  have azz := adMat_gram (F := F) σ J Z Z J₀ fr.zz
  rw [adMat_zero'] at acc add acz adz azc azd
  rw [adMat_one'] at acd adc
  have hJ0 : adMat F J₀⁻¹ * adMat F J₀ = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm₀), adMat_one']
  have hJi : adMat F J⁻¹ * adMat F J = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm), adMat_one']
  have hsum : adMat F C * (cT (sigR (AF F) σ) (adMat F D) * adMat F J) +
      adMat F Z * (adMat F J₀⁻¹ * (cT (sigR (AF F) σ) (adMat F Z) * adMat F J)) +
      adMat F D * (cT (sigR (AF F) σ) (adMat F C) * adMat F J) = 1 := by
    have := congrArg (adMat F) fr.sum
    rw [adMat_one'] at this
    rw [← this, cT_adMat, cT_adMat, cT_adMat]
    simp only [adMat_mul', adMat, Matrix.map_add _ (map_add _)]
  obtain ⟨u, hu, h1, h2, h3⟩ := images_ring (sigR (AF F) σ) (adMat F J) (adMat F J⁻¹) (adMat F J₀) (adMat F J₀⁻¹) hJi hJ0
    (adMat F C) (adMat F D) C' D' (adMat F Z) Z' acc add acd adc acz adz azc azd azz hsum cc dd cd dc cz dz zc zd zz
  exact ⟨(show HA (AF F) σ J from (⟨u, hu⟩ : HR (AF F) σ J)), h1, h2, h3⟩

end GlobalTheory.SphEis.ColImg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLatOfOfLowerBound
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.IntCuspLat

theorem exists_dataX (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) :
    ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ Xx.k0 = 2 * xiR D := by
  obtain ⟨-, -, -, hx0, hx1, -⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have habs := h.xiAbs j hj σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
    (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((T.U j σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((T.U j σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hM : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((T.U j σ).X k) D.host.AA D.host.AAbar
    (xiR D) T.Q.l.M
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (fun γ => gamAt_of_lawsM D T h j hj σ hσ k γ)
  exact ⟨{ Xx with
    k0 := 2 * xiR D
    minWeight_pos := by positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((T.U j σ).X k).ξ0 from congrArg _ h1, habs]; ring }, h1, h2, h3, rfl⟩

theorem exists_lowerBound (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) :
    ∃ B : ℝ, ∀ F ∈ T.C j w, (∀ la, ∀ v ∈ T.Vs j la, 0 ≤ v F) → F ≠ 0 →
      -B ≤ ∑ σ : T.Q.c.F →+* ℂ, Real.log (T.Ns j w σ F) := by
  classical
  obtain ⟨C0, hC0, hroom⟩ := GlobalTheory.room_of_constants
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := (h.unf j hj T.σ₀ T.good_σ₀).1.symm
  have hf := GlobalTheory.WtSizes.fdeg_eq D
  have hd1 := GlobalTheory.WtSizes.one_le_dE D
  have hts := GlobalTheory.WtSizes.tot_le_size w
  have hwf : ∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ w.size := fun k => by
    refine (Finset.sum_le_sum fun τ _ => GlobalTheory.WtSizes.spread_laU_le T hr w k τ).trans (le_trans ?_ hts)
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact_mod_cast GlobalTheory.WtSizes.sum_cm_le ((T.U j T.σ₀).X k) (GlobalTheory.WtSizes.tot w)
    · rw [Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (T.U j T.σ₀).X k), hf, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_mul_of_pos_right _ hr
  have hsz : ((∑ b : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult b), wtA w (b, i) : ℕ) : ℝ) +
      ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
    refine le_trans (add_le_add ?_ le_rfl) hts
    exact_mod_cast Finset.sum_le_sum fun b _ => GlobalTheory.WtSizes.sum_wtA_le_tot w b _
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd4 : D.host.d % 4 = 3 := by
    have := T.Q.H.d_mod
    rw [h.pins.1.1] at this
    omega
  obtain ⟨_, χ, hχ, -⟩ := GlobalTheory.LamF.exists_kronecker_logOm_re D.host.E h.pins.1.1 hd4
  have g0 := (D.host.g_prime 0).pos
  have g1 := (D.host.g_prime 1).pos
  have hdpos : 0 < D.host.d := lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ((D.host.g 0 * D.host.g 1 * (Ideal.absNorm D.host.ccK * D.host.d) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hM : (0 : ℝ) < M := by
    rw [hMdef]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos g0 g1) (Nat.mul_pos hN hdpos)
  refine ⟨(C0 * ((fdeg D.host.E : ℝ) * D.R.r + |Real.log (M * (2 * xiR D))| + Real.log (dE D.host.E) +
    |(GlobalTheory.CM.logOm D.host.E χ).re|) ^ (2 : ℝ) * (1 + Real.log w.size) * w.size) *
      (Module.finrank ℚ T.Q.c.F : ℝ), fun F hFC hF hF1 => ?_⟩
  have hhol : rdU (T.U j T.σ₀) F ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) :=
    ((mem_cusp _ _ _ _ _ F).1 hFC).2 T.σ₀ T.good_σ₀
  have hSS := Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) hhol
  have hfin : supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) ≠ ⊤ :=
    supE_cusp_ne_top T.good_σ₀ hFC
  have hpos : 0 < supN (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
      (rdU (T.U j T.σ₀) F)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (h.supDef j hj (wtA w) w.n (dom_wtA w) T.σ₀ T.good_σ₀ F hFC heq.symm) hF1
  obtain ⟨k, z0, hz0, hlt⟩ := Formalism.L2.Pj.abelian₂.half_max (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
    (rdU (T.U j T.σ₀) F) hpos hfin
  have hhalf : ∀ x ∈ ((T.U j T.σ₀).X k).dom, ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k)
      (rdU (T.U j T.σ₀) F k) x ≤
      2 * ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0 :=
    fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0 := by
    linarith
  obtain ⟨Xx, hX, hXg, hΛ, hk0⟩ := exists_dataX D T h j hj T.σ₀ T.good_σ₀ k
  have habs : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xx.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← GlobalTheory.TransvModel.xiR_eq, ← h.xiAbs j hj T.σ₀ T.good_σ₀ k τ, ← hX]
  have htr : ∀ v ∈ Xx.L', FD.herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∀ τ : ((T.U j T.σ₀).X k).Ψ,
        (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j T.σ₀).X k).flowMat v τ ((M : ℂ) * τ.1 b) := by
    rw [← hX]
    intro v hv hiso b hb hbi
    have := GlobalTheory.TransvModel.transv_mem_of_span Xx (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (GlobalTheory.TransvModel.isIntegral_level_mul_kappa Xx.toData hN hdpos D.host.φ₀ (habs _)) v hv hiso b hb hbi
    rwa [hXg.trans h.pins.2.1.1, ← hMdef] at this
  obtain ⟨x, lam, hx, hLB, hPx⟩ := Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((T.U j T.σ₀).X k) hX _ _ z0 M w.size (hSS k) hM
    (hwf k) w.one_le_size hr (fun v hv hvv b hb hbi => by
      obtain ⟨γ, hγ, hγ'⟩ := htr v hv hvv b hb hbi
      exact ⟨γ, hγ, h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA w) k γ hγ, hγ'⟩) hz0 hhalf hposz
  have hf1 : 1 ≤ fdeg D.host.E := by
    have h2 := finrank_eq_two_mul_half_degree (E := D.host.E)
    have h3 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E := by exact_mod_cast h2
    omega
  have hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * (2 * xiR D))| + 3 + Real.log (dE D.host.E) := by
    rw [hk0]
    have := le_abs_self (Real.log (M * (2 * xiR D)))
    have := abs_nonneg (Real.log (M * (2 * xiR D)))
    have := Real.log_nonneg hd1
    linarith
  obtain ⟨hLa1, hr'⟩ := hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) _ (GlobalTheory.CM.logOm D.host.E χ).re M Xx.k0 w.size
    hf1 hr Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos w.one_le_size hlog
  have hr'' := hr' _ _ (Nat.cast_nonneg _) (by positivity) hsz C0 2 le_rfl le_rfl
  have hNs : ∀ σ, IsNormOn (T.C j w) σ (T.Ns j w σ) := fun σ =>
    (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf
  have hSpos : ∀ σ, 0 < supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n F := fun σ =>
    lt_of_le_of_ne ((hNs σ).nonneg F hFC) fun h0 => hF1 ((hNs σ).defin F hFC h0.symm)
  have h5 := GlobalTheory.LamT.meanLogSup_lowerBound D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D)
    (h.unf j hj) (h.xiAbs j hj) (by rw [hpq]; exact hr) χ hχ (wtA w) w.n (dom_wtA w) F hFC hF hSpos k ⟨x, hx⟩ Xx hX
    D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx
  have hf' : Module.finrank ℚ D.host.E / 2 = D.R.f := hf
  rw [hf'] at h5
  have hK : (0 : ℝ) < Module.finrank ℚ T.Q.c.F := by exact_mod_cast Module.finrank_pos
  rw [← neg_mul, ← le_div_iff₀ hK]
  refine le_trans ?_ h5
  linarith

theorem fg_latOf_of_lowerBound {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] (C : Submodule K R) [FiniteDimensional K C]
    (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (N : (K →+* ℂ) → R → ℝ) (hN : ∀ σ, IsNormOn C σ (N σ)) (B : ℝ)
    (hB : ∀ F ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v F) → F ≠ 0 → -B ≤ ∑ σ : K →+* ℂ, Real.log (N σ F)) :
    (latOf C Vs hV).FG := by
  let Nf : TB.NormFam K C :=
    { N := fun σ F => N σ F
      nonneg := fun σ F => (hN σ).nonneg _ F.2
      eq_zero := fun σ F h0 => Subtype.ext ((hN σ).defin _ F.2 h0)
      smul := fun σ a F => (hN σ).smul a _ F.2
      add := fun σ F G => (hN σ).add _ F.2 _ G.2 }
  exact formalGroup_of_discriminant _ _ Nf _ (discriminant_of_product_lower _ _ Nf _ B fun F hF h0 =>
    hB F.1 F.2 hF fun h1 => h0 (Subtype.ext h1))

end GlobalTheory.IntCuspLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinUA

theorem hermA_neg_transpose {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) x y =
      -((fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) ⬝ᵥ
        ((J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) *ᵥ x)) := by
  unfold GlobalTheory.AdLat.hermA
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply,
    TensorProduct.tmul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hermA_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (h : (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c))ᵀ *
      (J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) * g =
      J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E))
    (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) (g *ᵥ x) (g *ᵥ y) = GlobalTheory.AdLat.hermA c (-Jᵀ) x y := by
  rw [hermA_neg_transpose, hermA_neg_transpose]
  congr 1
  have e : (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ((g *ᵥ y) b)) =
      (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ
        (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
    funext b
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e]
  conv_rhs => rw [← h]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (Matrix.transpose _),
    Matrix.vecMul_transpose]

theorem isUA_finHom : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (g : GA D V),
    GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) := by
  intro D V g
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 (finHom V g).isUnit, fun x y => hermA_mulVec _ _ _ ?_ x y⟩
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1 * JR (AF D.host.F) V.gram * g.1.1
      = JR (AF D.host.F) V.gram := g.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hc : ∀ t, D.sp.cm.sig t = IsCMField.complexConj D.host.E t :=
    (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.2.2.1
  have hφ : ∀ z, φ (sigR (AF D.host.F) D.sp.cm.sig z) =
      GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E) (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [φ, sigR, GlobalTheory.AdLat.sg, hc]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hJ : (JR (AF D.host.F) V.gram).map φ =
      V.gram.map fun t => ((1 : Af D.host.F) ⊗ₜ[D.host.F] t : Af D.host.F ⊗[D.host.F] D.host.E) := by
    ext a b
    simp [φ, JR, inclR]
  have h2 := congrArg (fun M => Matrix.map M φ) h
  simp only [Matrix.map_mul] at h2
  rw [hJ] at h2
  have hg : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1).map φ =
      ((g.1.1.map φ).map (GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E)))ᵀ := by
    ext a b
    exact hφ _
  rw [hg] at h2
  exact h2

end GlobalTheory.FinUA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMemCuspFormsOfActionLawsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAction_mem_cuspForms_of_action_laws : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → ∀ g, (∀ a, (lev g).2 a = a) → ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := by
  first | exact @GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev | exact GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev | (intros; apply GlobalTheory.LevelCusp.actLev_mem_cuspA_of_actLev <;> assumption)
end

