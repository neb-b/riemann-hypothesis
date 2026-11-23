module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0085
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarAdelicUpperUnitriangularEntryTranslateInvari
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace
open IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

set_option synthInstance.maxHeartbeats 200000 in
theorem compAt_cA (D : D7) (v : Pl D) (a : AE D) : compAt D v (cA D a) = sigV D v (compAt D v a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), map_add (f := _), hx, hy]
  | tmul a m => rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem tmul_algebraMap (D : D7) (v : Pl D) (c : Fv D.host.F v) (f : D.host.F) :
    c ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) = (algebraMap D.host.F (Fv D.host.F v) f * c) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem fixed_unit_norm : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) →
    (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ u ∈ intAt D (· = v), cA D u = u →
    (∃ y ∈ intAt D (· = v), u * y = ε) → ∃ x ∈ intAt D (· = v), x * cA D x = u := by
  intro D v ε hT _ _ _ hid u hu hcu ⟨y, hy, huy⟩
  obtain ⟨w, t, n, h1, h2, h3⟩ := GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem D.host.F D.host.E D.sp.cm.sig
    (GlobalTheory.AdelicU.isCMExt_host D) v (fun P hP => @hT.1 P.asIdeal P.isPrime hP)
  have hw : ∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w := by
    intro f hf
    apply h3
    have hs : D.sp.cm.sig w = w := by rw [← hf, AlgHom.commutes]
    have e : algebraMap D.host.F D.host.E ((t : D.host.F) ^ 2 - 4 * n) = 0 := by
      rw [map_sub, map_pow, map_mul, ← h1, ← h2, hs, map_ofNat]; ring
    have e2 : ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) = 0 := by
      have := (FaithfulSMul.algebraMap_injective D.host.F D.host.E) (e.trans (map_zero _).symm)
      push_cast; exact this
    have e3 : t ^ 2 - 4 * n = 0 := RingOfIntegers.coe_eq_zero_iff.1 e2
    rw [e3]; exact v.asIdeal.zero_mem
  obtain ⟨W, hW⟩ := _root_.GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral D w t n h1 h2

  have hone : (1 : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intV D v :=
    AddSubgroup.subset_closure ⟨1, (v.adicCompletionIntegers D.host.F).one_mem, 1, by simp [Algebra.TensorProduct.one_def]⟩
  have hε1 : compAt D v ε = 1 := by
    obtain ⟨z, hz, hz1⟩ := _root_.GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq D v 1 hone
    have h := congrArg (compAt D v) ((hid z).1 hz.1)
    rwa [RingHom.map_mul, hz1, mul_one] at h

  obtain ⟨a, ha, b, hb, hU⟩ := _root_.GlobalTheory.FixedUnitNorm.Coords.mem_intV_coords D v w t n h1 h2 h3 _ (_root_.GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt D v u hu)
  have hsig : sigV D v (compAt D v u) = compAt D v u := by rw [← compAt_cA, hcu]
  have hsw : D.sp.cm.sig w = algebraMap D.host.F D.host.E t - w := by rw [← h1]; ring
  have hb0 : b = 0 := by
    have e : sigV D v (a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w) -
        (a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w) = 0 := by rw [← hU, hsig, sub_self]
    have e' : (algebraMap D.host.F (Fv D.host.F v) t * b) ⊗ₜ[D.host.F] (1 : D.host.E) + (-(2 * b)) ⊗ₜ[D.host.F] w = 0 := by
      rw [← e, sigV, map_add (f := _), Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        map_one, hsw, TensorProduct.tmul_sub, tmul_algebraMap, TensorProduct.neg_tmul]
      rw [show (2 : Fv D.host.F v) * b = b + b by ring, TensorProduct.add_tmul]
      abel
    have := (_root_.GlobalTheory.CoordUnique.coords_unique D v w hw _ _ e').2
    have h2b : (2 : Fv D.host.F v) * b = 0 := neg_eq_zero.1 this
    have h2ne : (2 : Fv D.host.F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := D.host.F)
      apply (algebraMap D.host.F (Fv D.host.F v)).injective
      rw [map_ofNat, map_zero]; exact h
    exact (mul_eq_zero.1 h2b).resolve_left h2ne
  rw [hb0, TensorProduct.zero_tmul, add_zero] at hU
  obtain ⟨a', ha', b', hb', hY⟩ := _root_.GlobalTheory.FixedUnitNorm.Coords.mem_intV_coords D v w t n h1 h2 h3 _ (_root_.GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt D v y hy)
  have haa : a * a' = 1 := by
    have e : compAt D v u * compAt D v y = 1 := by rw [← RingHom.map_mul, huy, hε1]
    rw [hU, hY, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul] at e
    have e' : (a * a' - 1) ⊗ₜ[D.host.F] (1 : D.host.E) + (a * b') ⊗ₜ[D.host.F] w = 0 := by
      rw [TensorProduct.sub_tmul, ← Algebra.TensorProduct.one_def, ← e]; abel
    exact sub_eq_zero.1 (_root_.GlobalTheory.CoordUnique.coords_unique D v w hw _ _ e').1
  let A : v.adicCompletionIntegers D.host.F := ⟨a, ha⟩
  have hAu : IsUnit A := ⟨⟨A, ⟨a', ha'⟩, Subtype.ext haa, Subtype.ext (by rw [mul_comm]; exact haa)⟩, rfl⟩
  have hD : IsUnit (algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) t ^ 2 -
      4 * algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) n) := by
    have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3
    rwa [map_sub, map_pow, map_mul, map_ofNat] at this
  obtain ⟨r, s, hrs⟩ := _root_.GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers D.host.F v _ _ A hD hAu

  set x' : Fv D.host.F v ⊗[D.host.F] D.host.E := (r : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E) + (s : Fv D.host.F v) ⊗ₜ[D.host.F] w
  have hx'i : x' ∈ intV D v := by
    refine AddSubgroup.add_mem _ (AddSubgroup.subset_closure ⟨r, r.2, 1, by simp⟩)
      (AddSubgroup.subset_closure ⟨s, s.2, W, by rw [hW]⟩)
  have hcoe : ∀ c : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) c : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) =
      algebraMap D.host.F (Fv D.host.F v) c := fun c => rfl
  have hnorm : x' * sigV D v x' = compAt D v u := by
    have hrs' : (r : Fv D.host.F v) ^ 2 + algebraMap D.host.F (Fv D.host.F v) t * r * s +
        algebraMap D.host.F (Fv D.host.F v) n * (s : Fv D.host.F v) ^ 2 = a := by
      have := congrArg (fun q : v.adicCompletionIntegers D.host.F => (q : Fv D.host.F v)) hrs
      exact this
    have e1 : sigV D v x' = (r : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E) + (s : Fv D.host.F v) ⊗ₜ[D.host.F] D.sp.cm.sig w := by
      simp only [x', sigV, map_add (f := _), Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    rw [e1, hU]
    simp only [x', add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have e2 : ((s : Fv D.host.F v) * r) ⊗ₜ[D.host.F] w = ((r : Fv D.host.F v) * s) ⊗ₜ[D.host.F] w := by rw [mul_comm]
    rw [e2, h2, tmul_algebraMap, hsw, TensorProduct.tmul_sub, tmul_algebraMap]
    have key : ∀ P Q R S : Fv D.host.F v ⊗[D.host.F] D.host.E, P + S + (Q - S + R) = P + Q + R := fun P Q R S => by abel
    rw [key, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]
    congr 1
    rw [← hrs']; ring
  obtain ⟨x, hxi, hxc⟩ := _root_.GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq D v x' hx'i
  refine ⟨x, hxi, ?_⟩
  have hx0 := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ x).1 hxi.1
  have hu0 := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ u).1 hu.1
  rw [← sub_eq_zero]
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_sub, RingHom.map_mul, hx0.1, zero_mul, hu0.1, sub_zero]
  · intro w'
    by_cases hw' : w' = v
    · subst hw'; rw [RingHom.map_sub, RingHom.map_mul, compAt_cA, hxc, hnorm, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, hx0.2 w' hw', zero_mul, hu0.2 w' hw', sub_zero]

end GlobalTheory.FixedUnitNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagStabilizer_eq_unipotent_torus_levi_atPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S g * d.jX = d.jX * a) → ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), g = n * d.levi t * d.emb0 γ := by
  intro D S S₀ ρ d v g hg ⟨a, hup, hgX⟩
  have hG' : ∀ i j, (mt S g - 1) i j ∈ idAt D (· = v) := fun i j => by
    rw [Matrix.sub_apply]; exact (mem_congGrp_iff S (idAt D (· = v)) g).1 hg i j

  have hba : (adj (mt S g * d.jY) * (gA S * d.jX)) * a = 1 := by
    have h1 : adj (mt S g * d.jY) * (gA S * (mt S g * d.jX)) = 1 := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
      exact d.gram_YX
    rw [hgX] at h1
    simpa only [Matrix.mul_assoc] using h1
  have hab : a * (adj (mt S g * d.jY) * (gA S * d.jX)) = 1 := mul_eq_one_comm.1 hba
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin ρ) (AE D), A.1 = a := ⟨⟨a, _, hab, hba⟩, rfl⟩

  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hba
  rw [Matrix.det_of_isUpperTriangular (M := a) (fun ⦃i j⦄ h => hup i j h)] at hdet
  have hu : ∀ i, IsUnit (a i i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k => a k k) (Finset.mem_univ i)) hdet
  obtain ⟨t, ht1, htinv⟩ : ∃ t : GL (Fin ρ) (AE D), t.1 = diagonal (fun i => a i i) ∧
      (t⁻¹).1 = diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) :=
    ⟨⟨diagonal (fun i => a i i), diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)),
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.mul_val_inv, diagonal_one],
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.val_inv_mul, diagonal_one]⟩, rfl, rfl⟩
  have ht_diag : ∀ i j, i ≠ j → t.1 i j = 0 := fun i j h => by rw [ht1]; exact diagonal_apply_ne _ h

  have hAt : (A * t⁻¹).1 =
      a * diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) := by
    rw [Units.val_mul A t⁻¹, htinv, hA]
  have hUX : A * t⁻¹ ∈ UX D ρ := fun i j =>
    ⟨fun h => by rw [hAt, mul_diagonal, hup i j h, zero_mul],
      by rw [hAt, mul_diagonal]; exact IsUnit.mul_val_inv (hu i)⟩
  have hR' : mt S (g * (d.levi t)⁻¹) * d.jX = d.jX * (A * t⁻¹).1 := by
    rw [Units.val_mul A t⁻¹, hA, ← map_inv d.levi t, mt_mul, Matrix.mul_assoc, d.levi_jX]
    simpa only [Matrix.mul_assoc] using congrArg (fun M : Mx D S.rank ρ => M * (t⁻¹).1) hgX
  let u := A * t⁻¹
  let r := g * (d.levi t)⁻¹
  let s := d.levi u⁻¹ * r
  have hsX : mt S s * d.jX = d.jX := by
    change mt S (d.levi u⁻¹ * r) * d.jX = d.jX
    rw [mt_mul, Matrix.mul_assoc, show mt S r * d.jX = d.jX * u.1 from hR',
      ← Matrix.mul_assoc, d.levi_jX, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one]
  have hgram {k l : ℕ} (X : Mx D S.rank k) (Y : Mx D S.rank l) :
      adj (mt S s * X) * (gA S * (mt S s * Y)) = adj X * (gA S * Y) := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) _ Y,
      ← Matrix.mul_assoc (adj (mt S s)), mt_unitary]
  have hsY : d.pY * (mt S s * d.j0) = 0 := by
    rw [d.pY_eq, Matrix.mul_assoc, ← hsX, hgram, d.wittDecomp_gram_X_anisotropic]
  let B := d.pX * (mt S s * d.j0)
  let Q := d.p0 * (mt S s * d.j0)
  have hs0 : mt S s * d.j0 = d.jX * B + d.j0 * Q := by
    conv_lhs => rw [← Matrix.one_mul (mt S s * d.j0), ← d.sum_eq_one]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      hsY, Matrix.mul_zero, add_zero]
  have hQ : adj Q * (gA S₀ * Q) = gA S₀ := by
    have h := hgram d.j0 d.j0
    rw [hs0, d.gram_00] at h
    simpa only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      cancel₃ d.gram_XX, cancel₃ d.wittDecomp_gram_X_anisotropic, cancel₃ d.gram_0X,
      cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] using h
  let γ := GlobalTheory.MixModel.ofMat S₀ Q hQ
  have hγQ : mt S₀ γ = Q := by
    change mt S₀ (GlobalTheory.MixModel.ofMat S₀ Q hQ) = Q
    rw [mt_ofMat]
  have hs0' : mt S s * d.j0 = d.jX * B + d.j0 * mt S₀ γ := by rw [hγQ, hs0]
  let n₀ := s * (d.emb0 γ)⁻¹
  have hn₀X : mt S n₀ * d.jX = d.jX := by
    change mt S (s * (d.emb0 γ)⁻¹) * d.jX = d.jX
    rw [← map_inv, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, hsX]
  have hn₀0 : mt S n₀ * d.j0 = d.j0 + d.jX * (B * mt S₀ γ⁻¹) := by
    change mt S (s * (d.emb0 γ)⁻¹) * d.j0 = _
    rw [← map_inv, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic,
      ← Matrix.mul_assoc, hs0', Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc d.j0,
      GlobalTheory.MixModel.mt_mul_inv, Matrix.mul_one, add_comm]
  have hn₀ : n₀ ∈ flagN d := by
    refine d.mem_NFlag HypDec.one_mem_upperUni ?_ hn₀0
    rw [hn₀X, Units.val_one, Matrix.mul_one]
  let n := d.levi u * n₀
  have hn : n ∈ flagN d := mul_mem (d.levi_mem_NFlag hUX) hn₀
  have hnγ : g * (d.levi t)⁻¹ = n * d.emb0 γ := by
    change r = (d.levi u * (s * (d.emb0 γ)⁻¹)) * d.emb0 γ
    rw [mul_assoc, inv_mul_cancel_right]
    change r = d.levi u * (d.levi u⁻¹ * r)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

  have hgfac : g = n * d.levi t * d.emb0 γ := by
    rw [mul_assoc, ← d.wittHyperbolic_anisotropic_commute_levi, ← mul_assoc, ← hnγ,
      inv_mul_cancel_right]

  have hmtγ : mt S₀ γ = d.p0 * (mt S g * d.j0) := by
    rw [hγQ]
    change d.p0 * (mt S (d.levi u⁻¹ * (g * (d.levi t)⁻¹)) * d.j0) = _
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← map_inv d.levi t,
      d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc d.p0,
      d.wittDecomp_projAnisotropic_levi]
  have hγ : γ ∈ grpAt S₀ (· = v) := (mem_congGrp_iff S₀ _ γ).2 fun i j => by
    have e : mt S₀ γ - 1 = d.p0 * ((mt S g - 1) * d.j0) := by
      rw [hmtγ, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.p0_j0]
    rw [← Matrix.sub_apply, e]
    exact GlobalTheory.IwaFlag.mul_left_mem _ (GlobalTheory.IwaFlag.mul_right_mem _ hG') i j

  have haI : ∀ i j, (a - 1) i j ∈ idAt D (· = v) := by
    have e : a - 1 = d.pX * ((mt S g - 1) * d.jX) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.pX_jX, hgX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    intro i j
    rw [e]
    exact GlobalTheory.IwaFlag.mul_left_mem _ (GlobalTheory.IwaFlag.mul_right_mem _ hG') i j
  have ht1I : ∀ i j, (t.1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [ht1, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply] at this
      rwa [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have htiI : ∀ i j, ((t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [htinv, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
      rw [diagonal_apply_eq, Matrix.one_apply_eq]
      have e : (((hu i).unit⁻¹ : (AE D)ˣ) : AE D) - 1 = -((((hu i).unit⁻¹ : (AE D)ˣ) : AE D) * (a i i - 1)) := by
        rw [mul_sub, IsUnit.val_inv_mul (hu i)]; ring
      rw [e]
      exact (idAt D (· = v)).neg_mem (Ideal.mul_mem_left _ _ this)
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have hadjI : ∀ i j, (adj (t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [← adj_one, ← adj_sub]
    exact GlobalTheory.IwaFlag.cA_mem_idAt' (htiI j i)
  have hlevI : d.levi t ∈ grpAt S (· = v) := by
    have e : mt S (d.levi t) - 1 = d.jX * (t.1 - 1) * d.pX + d.jY * (adj (t⁻¹).1 - 1) * d.pY := by
      rw [d.mt_levi, ← d.sum_eq_one]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      abel
    refine (mem_congGrp_iff S _ _).2 fun i j => ?_
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact add_mem (GlobalTheory.IwaFlag.mul_right_mem _ (GlobalTheory.IwaFlag.mul_left_mem _ ht1I) i j) (GlobalTheory.IwaFlag.mul_right_mem _ (GlobalTheory.IwaFlag.mul_left_mem _ hadjI) i j)
  have hnI : n ∈ grpAt S (· = v) := by
    have hγI : d.emb0 γ ∈ grpAt S (· = v) := by
      have hγ' : ∀ i j, (mt S₀ γ - 1) i j ∈ idAt D (· = v) := fun i j => by
        rw [Matrix.sub_apply]
        exact (mem_congGrp_iff S₀ _ γ).1 hγ i j
      have e : mt S (d.emb0 γ) - 1 = d.j0 * (mt S₀ γ - 1) * d.p0 := by
        rw [d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one]
        abel
      refine (mem_congGrp_iff S _ _).2 fun i j => ?_
      rw [← Matrix.sub_apply, e]
      exact GlobalTheory.IwaFlag.mul_right_mem _ (GlobalTheory.IwaFlag.mul_left_mem _ hγ') i j
    have e : n = g * (d.levi t * d.emb0 γ)⁻¹ := eq_mul_inv_of_mul_eq ((mul_assoc _ _ _).symm.trans hgfac.symm)
    rw [e]
    exact mul_mem hg (inv_mem (mul_mem hlevI hγI))
  exact ⟨n, hn, hnI, t, ht_diag, hlevI, γ, hγ, hgfac⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicatorStatement
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k) (ε : 𝓀[k]ˣ), ((e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q Q'' : Pair k n), Q''.lat = Q.lat → (Q'' = ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = fpair χ e μ (vecInd Q.lat) (dualInd Q.lat)) ∧ (Q'' ≠ ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = 0) := by
  first | exact @GlobalTheory.FinPl.CosetPairing.fpair_charInd_cosetInd | exact GlobalTheory.FinPl.CosetPairing.fpair_charInd_cosetInd | (intros; apply GlobalTheory.FinPl.CosetPairing.fpair_charInd_cosetInd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesCoverOfFactorsThroughCove
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverDS

theorem hasTypes_of_factors : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar →
    ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T)
      (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)),
      BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → HasTypes R (blockPar P e) := by
  intro h1 h2 h3 p q n e P T R σ hb hf hd
  have hc : ∀ a, ((blockPar P e a : ℚ) : ℝ) = P.lam (e a) := fun a => ratEntry_cast P (e a)
  have hlow : (fun i => ((blattner (blockPar P e) (e.symm i) : ℚ) : ℝ)) = Formalism.QuantumDeterminants.lowK P.sgn P.lam := by
    funext i
    rw [blattner_eq P hb hc, e.apply_symm_apply]
    rfl
  have hn : p + q = n := by simpa using Fintype.card_congr e
  refine ⟨?_, fun v => ?_, GlobalTheory.CoverCone.inCone_of_kTypesAbove h2 p q n e P T R σ hb hf hd⟩
  · refine _root_.GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one p q n e P.sgn T R σ hb hf _ ?_ ?_
    · rw [hlow]
      exact hd.2.2.2.2.2.1
    · rw [hlow]
      exact h1 n P.sgn P.lam _ σ P.hc hd
  · rw [_root_.GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar p q n e P.sgn T R σ hb hf _ (h3 n P.sgn P.lam _ σ P.hc hd) v, _root_.GlobalTheory.GelfandTwo.gelfVal_two, hn]
    congr 1
    have hc' : ∀ a, ((blockPar P e a : ℚ) : ℂ) = ((P.lam (e a) : ℝ) : ℂ) := fun a => by
      rw [← hc a]; simp
    rw [normSq]
    push_cast
    simp only [hc']
    rw [Equiv.sum_comp e (fun a => ((P.lam a : ℝ) : ℂ) ^ 2)]

end GlobalTheory.CoverDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumDoublingInert
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.DoublingSumU


set_option maxHeartbeats 1000000 in
theorem hasSum_doubling_inert : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : Lˣ) (σ : L →+* L) (q n : ℕ), IsUnramInv (ϖ : L) σ q → ∀ χ : Lˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr χ → ∀ m : ℕ, ((χ ϖ : ℂˣ) : ℂ) = (-1) ^ m → ∀ (s : ℂ) (Φ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD σ n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec σ q n χ s Φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (x : V) (α : Fin (n / 2) → ℂˣ), IsSatVecU (ϖ : L) q ρ x α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ KU σ n, ∀ g, ℓ (ρ (k * g) x) = ℓ (ρ g x)) → (ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q (χ ϖ) s) α) → (∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g)) ∧ HasSum (fun a : GU σ n ⧸ KU σ n => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n a.out) * ℓ (ρ a.out x)) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL q n α (χ ϖ) (s + 1 / 2) / GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac q n m s * ℓ x) := by
  intro hD L _ _ _ ϖ σ q n hU χ hχ m hm s Φ hΦ V _ _ ρ x α hx ℓ hℓ hdom
  have hright : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) := by
    intro g k hk
    obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := GlobalTheory.ZetaSumU.cartan_complete L (ϖ : L) σ q n hU g
    rw [mul_assoc (a * t) b k, _root_.GlobalTheory.UGraph.sphSec_io_diag L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha _ (mul_mem hb hk),
      _root_.GlobalTheory.UGraph.sphSec_io_diag L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha b hb]
  refine ⟨hright, ?_⟩
  obtain ⟨h0, h1⟩ := _root_.GlobalTheory.ZonalCoeff.coeff_zero_or_zonal L ϖ σ q n hU V ρ x α hx ℓ hℓ
  by_cases hx0 : ℓ x = 0
  · simp only [h0 hx0, hx0, mul_zero]
    exact hasSum_zero
  · have hw := h1 hx0
    letI : MeasurableSpace (GU σ n) := borel _
    haveI : BorelSpace (GU σ n) := ⟨rfl⟩
    obtain ⟨μ, hμH, hμK⟩ := GlobalTheory.ZetaSumU.exists_haar (ϖ : L) hU n
    have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1
    obtain ⟨hint, -, hval⟩ := (hD L ϖ σ q n hU μ hμK χ hχ s Φ hΦ α _ hw).1 (hdom hx0)
    have hval' := hval m hm
    have hF : ∀ g, ∀ k ∈ KU σ n, Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n (g * k)) * (ℓ (ρ (g * k) x) / ℓ x) =
        Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x) := fun g k hk => by
      have h2 := hw.1 1 ⟨k, hk⟩ g
      simp only [OneMemClass.coe_one, one_mul] at h2
      rw [hright g k hk, h2]
    have hs := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ n) hKo hμK _ hF hint).of_norm
    have hci := (_root_.GlobalTheory.InertZeta.cosetIntegral_holds _ μ (KU σ n) hKo hμK
      (fun g => Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 σ n g) * (ℓ (ρ g x) / ℓ x)) _ hF hs.hasSum).2
    have hS := hs.hasSum
    rw [← hci, hval'] at hS
    have h3 := hS.mul_right (ℓ x)
    simpa only [mul_assoc, div_mul_cancel₀ _ hx0] using h3

end GlobalTheory.DoublingSumU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableSchwartzMajorantPullbackUnitriangular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
namespace GlobalTheory.Unf

theorem pull_integrable : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m ρ : ℕ) (vU : VolU D ρ) (x : Matrix (Fin m) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∃ N : ℕ, ∀ K : Set (Mx D m ρ), IsCompact K → Integrable (fun u : UX D ρ => maj θ K N ((rat x : Mx D m ρ) ⬝ u.1.1)) vU.ν := by
  intro D θ hθ m ρ vU x hx
  have hH : vU.ν.IsHaarMeasure := vU.unit.1
  obtain ⟨hf, hfin, hinv⟩ := _root_.GlobalTheory.UnitTransl.haar_val_add_invariant D ρ vU.ν hH
  have hae : ∀ᵐ y ∂(Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) vU.ν), ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j := by
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : T2Space (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.1
    have hS : MeasurableSet {y : Mx D ρ ρ | ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j} := by
      have hc : IsClosed {y : Mx D ρ ρ | ∀ i j, ¬ (fun i j : Fin ρ => i < j) i j → y i j = (1 : Mx D ρ ρ) i j} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
          isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
      exact hc.measurableSet
    rw [ae_map_iff hf.aemeasurable hS]
    refine ae_of_all _ fun u i j hij => ?_
    have hU := (GlobalTheory.UniIndexPrime.mem_uniSub u.1).1 u.2
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [Matrix.one_apply_ne h.ne']
      exact hU.1 i j h
    · subst h
      rw [Matrix.one_apply_eq]
      exact hU.2 _
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Unf.MajInt.maj_integrable D θ hθ ρ ρ (fun i j => i < j) 1 _ hfin hae hinv
  obtain ⟨hmaj, hmove⟩ := _root_.GlobalTheory.Unf.maj_measurable_rat D θ hθ
  refine ⟨N, fun K hK => ?_⟩
  obtain ⟨K', hK', hb⟩ := hmove m ρ ρ x hx K hK
  obtain ⟨C, hC⟩ := hb N
  have h1 : Integrable (maj θ K' N) (Measure.map (fun u : UX D ρ => (u.1.1 : Mx D ρ ρ)) vU.ν) := hN K' hK'
  have h2 : Integrable (fun u : UX D ρ => maj θ K' N (u.1.1 : Mx D ρ ρ)) vU.ν :=
    (integrable_map_measure ((hmaj ρ ρ K' hK').2.2.1 N).aestronglyMeasurable hf.aemeasurable).1 h1
  have hmul : Measurable (fun y : Mx D ρ ρ => (rat x : Mx D m ρ) ⬝ y) := by
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : BorelSpace (Mx D m ρ) := ⟨rfl⟩
    exact (continuous_const.matrix_mul continuous_id).measurable
  refine (h2.const_mul C).mono' (((hmaj m ρ K hK).2.2.1 N).comp (hmul.comp hf)).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (maj_nonneg θ K N _)]
  exact hC _

end GlobalTheory.Unf
end

