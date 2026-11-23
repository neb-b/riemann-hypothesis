module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDualWeylProductSpanOfFactorwiseDualWeyl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1819
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCoefficientPolySimpleSubquotient

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarDilationElementSupportDetPullback
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DilScalar

variable {D : D7}

theorem int_mul {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem incA_int (x : 𝓞 D.host.E) : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, x, rfl⟩

theorem idemAt_mul_int {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e P)
    {y : D.host.E} (hv : P.valuation D.host.E y ≤ 1) : finPart D (e * incA D y) ∈ intAE D := by
  obtain ⟨a, b, hab⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  have hb : (b : 𝓞 D.host.E) ∉ P.asIdeal := b.2
  have hb0 : (b : 𝓞 D.host.E) ≠ 0 := fun h => hb (h ▸ zero_mem _)
  have hb1 : ((b : 𝓞 D.host.E) : D.host.E) ≠ 0 := by exact_mod_cast hb0
  have hi : finPart D (e * incA D (((b : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra hc
    exact hb ((he.2 _ hb0).2 hc)
  have hq : y = (a : D.host.E) * ((b : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hb1]
    exact hab
  have h := int_mul (incA_int (D := D) a) hi
  rw [← RingHom.map_mul, mul_left_comm, ← map_mul (incA D), ← hq] at h
  exact h

theorem val_uniformiser (P : HeightOneSpectrum (𝓞 D.host.E)) {ϖ : 𝓞 D.host.E}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) :
    P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) := by
  rw [P.valuation_of_algebraMap]
  have a1 : P.intValuation ϖ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) :=
    (P.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
  have a2 : ¬ P.intValuation ϖ ≤ WithZero.exp (-((2 : ℕ) : ℤ)) :=
    fun h => h2 ((P.intValuation_le_pow_iff_mem ϖ 2).1 h)
  have a0 : P.intValuation ϖ ≠ 0 := fun h => a2 (h ▸ zero_le')
  rw [← WithZero.exp_log a0] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  omega

theorem idemSum_dil_int {e : AE D} {Q : Finset (Pl D.host.E)} (he : IsIdemSum e Q) {N : ℕ}
    (hN : ∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) {ϖ : 𝓞 D.host.E}
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) :
    finPart D (e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) ∈ intAE D := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => idemAt_mul_int (hes PP hPP) ?_
  have v1 := val_uniformiser (D := D) PP (hϖ PP hPP).1 (hϖ PP hPP).2
  have v2 : PP.valuation D.host.E (N : D.host.E) ≤ WithZero.exp (-1 : ℤ) := by
    rw [← map_natCast (algebraMap (𝓞 D.host.E) D.host.E) N, PP.valuation_of_algebraMap]
    have := (PP.intValuation_le_pow_iff_mem (N : 𝓞 D.host.E) 1).2 (by rw [pow_one]; exact hN PP hPP)
    simpa using this
  rw [map_mul, map_inv₀, v1]
  calc PP.valuation D.host.E (N : D.host.E) * (WithZero.exp (-1 : ℤ))⁻¹
      ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.DilScalar


set_option maxHeartbeats 1000000 in
open GlobalTheory.DilScalar in
theorem GlobalTheory.DilScalar.scalar_dil_facts : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D S, mt S z = Matrix.diagonal (fun _ => e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) → SuppAt e S z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D e) S z x) ∧ (∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) → actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w)) ∧ (∀ Φ, IsSBHalf e (latAll S T ΛS ΛT) Φ → IsSBHalf e (latAll S T ΛS ΛT) (actPull (z, (1 : GA D T)) Φ)) ∧ ∀ t : WO S T, IsHalf e t → actO S T z⁻¹ 1 t ∈ latAll S T ΛS ΛT → t ∈ latAll S T ΛS ΛT := by
  intro D S T ΛS ΛT Q e he N hN0 hN ϖ hϖ0 hϖ z hz
  have hee : e * e = e := idemSum_sq he
  have hec : e * cA D e = 0 := he.2
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hXP : incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hϖ0, map_one]
  have hYZ : cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hϖ0, map_one, map_one]
  have hea : e * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) =
      e * incA D ((ϖ : D.host.E)⁻¹) := by
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hec
  have hab : (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) *
      (e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) = 1 := by
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) * incA D (ϖ : D.host.E) - incA D ((ϖ : D.host.E)⁻¹)
        - incA D (ϖ : D.host.E) + 1) * hee
      + (cA D (incA D (ϖ : D.host.E)) * cA D (incA D ((ϖ : D.host.E)⁻¹)) - cA D (incA D (ϖ : D.host.E))
        - cA D (incA D ((ϖ : D.host.E)⁻¹)) + 1) * hcc
      + (incA D ((ϖ : D.host.E)⁻¹) * cA D (incA D ((ϖ : D.host.E)⁻¹)) + cA D (incA D (ϖ : D.host.E)) * incA D (ϖ : D.host.E)
        - incA D ((ϖ : D.host.E)⁻¹) - incA D (ϖ : D.host.E) - cA D (incA D (ϖ : D.host.E))
        - cA D (incA D ((ϖ : D.host.E)⁻¹)) + 2) * hec
      + e * hXP + cA D e * hYZ

  have hPint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D := incA_int ϖ
  have hPmem : ∀ u ∈ latAll S T ΛS ΛT, incA D (ϖ : D.host.E) • u ∈ latAll S T ΛS ΛT :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hPint

  have hact : ∀ t : WO S T, actO S T z⁻¹ 1 t =
      t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e)) := by
    intro t
    have h0 : actO S T z⁻¹ 1 t = HMul.hMul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z) := by
      rw [actO_eq, inv_inv, mt_one']; exact congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) => HMul.hMul M (mt S z))
        (Matrix.one_mul (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)))
    rw [h0, hz]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.map_apply]
  have hmapA : ∀ t : WO S T, IsHalf e t →
      (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) =
        t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w := by
    intro t ht
    ext i j
    simp only [Matrix.map_apply]
    linear_combination (incA D ((ϖ : D.host.E)⁻¹) -
      (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) * ht i j + t i j * hea
  have halfA : ∀ t : WO S T, IsHalf e (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) +
      cA D e * cA D (incA D (ϖ : D.host.E)) + (1 - e - cA D e))) → IsHalf e t := by
    intro t h i j
    have h1 := h i j
    simp only [Matrix.map_apply] at h1
    linear_combination (e * incA D (ϖ : D.host.E) + cA D e * cA D (incA D ((ϖ : D.host.E)⁻¹)) + (1 - e - cA D e)) * h1
      - (e * t i j - t i j) * hab
  have halfX : ∀ t : WO S T, IsHalf e (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) → IsHalf e t := by
    intro t h i j
    have h1 := h i j
    simp only [Matrix.map_apply] at h1
    linear_combination incA D (ϖ : D.host.E) * h1 - (e * t i j - t i j) * hXP
  have hpull : ∀ Ψ : WO S T → ℂ, (∀ t, Ψ t ≠ 0 → IsHalf e t) →
      actPull (z, (1 : GA D T)) Ψ = fun x => Ψ (x.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) := by
    intro Ψ hΨ
    funext t
    show Ψ (actO S T z⁻¹ (1 : GA D T)⁻¹ t) = _
    rw [inv_one, hact]
    by_cases hh : IsHalf e t
    · rw [hmapA t hh]
    · have h1 : Ψ (t.map fun w => w * (e * incA D ((ϖ : D.host.E)⁻¹) + cA D e * cA D (incA D (ϖ : D.host.E)) +
          (1 - e - cA D e))) = 0 := by
        by_contra h0
        exact hh (halfA t (hΨ _ h0))
      have h2 : Ψ (t.map fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = 0 := by
        by_contra h0
        exact hh (halfX t (hΨ _ h0))
      rw [h1, h2]
  refine ⟨?_, ?_, hpull, ?_, ?_⟩
  ·
    intro i j
    rw [hz]
    by_cases h : i = j
    · subst h
      rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      linear_combination (incA D ((ϖ : D.host.E)⁻¹) - 1) * hee + (cA D (incA D (ϖ : D.host.E)) - 1) * hcc +
        (incA D ((ϖ : D.host.E)⁻¹) + cA D (incA D (ϖ : D.host.E)) - 2) * hec
    · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]
  ·
    have hdet : (mt S z).det * (mt S z⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← mt_mul', mul_inv_cancel, mt_one', Matrix.det_one]
    refine ⟨⟨cA D e * (mt S z).det + (1 - cA D e), cA D e * (mt S z⁻¹).det + (1 - cA D e), ?_, ?_⟩, rfl⟩
    · linear_combination (cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc
    · linear_combination (cA D e * cA D e) * hdet + (2 - (mt S z).det - (mt S z⁻¹).det) * hcc
  ·
    intro Φ hΦ
    have hsupp := hΦ.1
    obtain ⟨_, k, hk, hinv, hcpt⟩ := hΦ
    rw [hpull Φ hsupp]
    have hint := idemSum_dil_int he hN hϖ
    refine ⟨fun t ht => halfX t (hsupp _ ht), N * k, Nat.mul_pos (Nat.pos_of_ne_zero hN0) hk,
      fun u hu hue t => ?_, fun t ht => ?_⟩
    · have key : (t + (N * k) • u).map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) =
          t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) +
            k • ((e * incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹)) • u) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul,
          map_natCast, Nat.cast_mul]
        linear_combination (-((k : AE D) * (N : AE D) * incA D ((ϖ : D.host.E)⁻¹))) * hue i j
      dsimp only
      rw [key]
      refine hinv _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hint u hu) (fun i j => ?_) _
      simp only [Matrix.smul_apply, smul_eq_mul]
      linear_combination (incA D ((N : D.host.E) * (ϖ : D.host.E)⁻¹) * u i j) * hee
    · have h1 := hPmem _ (hcpt _ ht)
      have h2 : incA D (ϖ : D.host.E) • k • t.map (fun w => incA D ((ϖ : D.host.E)⁻¹) * w) = k • t := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul]
        linear_combination ((k : AE D) * t i j) * hXP
      rw [h2] at h1
      rw [mul_smul]
      exact nsmul_mem h1 N
  ·
    intro t ht hmem
    rw [hact, hmapA t ht] at hmem
    have h1 := hPmem _ hmem
    convert h1 using 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (-t i j) * hXP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftedWeightsDominantOfGaps
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CompHS.WtPar

theorem antitone_of_step {N : ℕ} (f : Fin N → ℤ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) :
    Antitone f := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only [Fin.mk_le_mk] at hij
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (h ⟨k, by omega⟩ ⟨k + 1, hj⟩ rfl).trans (ih (by omega))

theorem shifted_dominant : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (P : WtPar Dw),
    0 ≤ P.c₀ → 2 * (Dw.p + Dw.q) + CompHt.dimFlag Dw ≤ P.T →
    (∀ (τ : Psi H) (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      ((b : ℕ) ≠ Dw.p → ((P.T : ℤ) + CompHt.dimFlag Dw + 2) * ((P.T : ℤ) + CompHt.dimFlag Dw + 2 + 2 * ((Dw.p + Dw.q : ℕ) : ℤ)) ≤
        P.u τ a - P.u τ b + 2) ∧
      ((b : ℕ) = Dw.p → ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag Dw + 1) + P.c₀ + 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 ≤
        P.u τ a - P.u τ b)) →
    ∀ s : ℕ, s ≤ 3 → ∀ τ : Psi H, Antitone (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ) ∧
      Antitone (((P.T + CompHt.dimFlag Dw + (if s = 0 then 3 else 4) : ℕ) : ℤ) • P.u₁ τ - (P.uMinus τ + (s * P.c₀) • hodgeWt Dw τ)) := by
  intro E _ _ _ H Dw P hc hT hgap s hs τ
  have hD : (CompHt.dimFlag Dw : ℤ) = (FlagTan.dimFlag Dw : ℤ) := by exact_mod_cast dimFlag_eq Dw
  have hw : ∀ i : Fin (Dw.p + Dw.q), hodgeWt Dw τ i = if (i : ℕ) < Dw.p then 0 else -1 := fun i => rfl
  have hX : ∀ i, (P.uMinus τ + ((s : ℤ) * P.c₀) • hodgeWt Dw τ) i =
      P.u τ i + ((s : ℤ) * P.c₀ - P.c₀) * hodgeWt Dw τ i := by
    intro i
    simp only [uMinus, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsc : (s : ℤ) * P.c₀ ≤ 3 * P.c₀ := mul_le_mul_of_nonneg_right (by exact_mod_cast hs) hc
  have hsc0 : 0 ≤ (s : ℤ) * P.c₀ := mul_nonneg (by positivity) hc
  have hT0 : (0 : ℤ) ≤ P.T := by positivity
  have hD0 : (0 : ℤ) ≤ CompHt.dimFlag Dw := by positivity
  constructor
  · refine antitone_of_step _ fun a b hab => ?_
    rw [hX, hX, hw, hw]
    obtain ⟨h1, h2⟩ := hgap τ a b hab
    by_cases hb : (b : ℕ) = Dw.p
    · have h := h2 hb
      have hb' : ¬ (b : ℕ) < Dw.p := by omega
      have ha' : (a : ℕ) < Dw.p := by omega
      simp only [hb', ha', if_true, if_false]
      have : 0 ≤ ((P.T : ℤ) + P.c₀) * ((P.T : ℤ) + CompHt.dimFlag Dw + 1) := by positivity
      have : (2 : ℤ) ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by have := b.2; push_cast; omega
      linarith
    · have h := h1 hb
      have : 2 ≤ ((P.T : ℤ) + CompHt.dimFlag Dw + 2) * ((P.T : ℤ) + CompHt.dimFlag Dw + 2 + 2 * ((Dw.p + Dw.q : ℕ) : ℤ)) := by
        have h2 : (0 : ℤ) ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by positivity
        nlinarith
      by_cases ha : (a : ℕ) < Dw.p
      · have hb' : (b : ℕ) < Dw.p := by omega
        simp only [hb', ha, if_true]; linarith
      · have hb' : ¬ (b : ℕ) < Dw.p := by omega
        simp only [hb', ha, if_false]; linarith
  · refine antitone_of_step _ fun a b hab => ?_
    obtain ⟨h1, h2⟩ := hgap τ a b hab
    have hk : (a : ℕ) + 1 < Dw.p + Dw.q := hab ▸ b.2
    have hg1 := P.gap_u₁ τ hk
    rw [P.gap_uMinus_sub_kap τ hk, gap_eq _ hab, gap_eq _ hab] at hg1
    set G := P.u τ a - P.u τ b + (if (a : ℕ) + 1 = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) with hG
    have hT₁ : P.T₁ = (P.T : ℤ) + CompHt.dimFlag Dw + 1 := by rw [WtPar.T₁, hD]
    have hT₁0 : 0 < P.T₁ := by rw [hT₁]; positivity
    set g := G / P.T₁ with hgdef
    have hdiv : P.T₁ * g + G % P.T₁ = G := by rw [Int.emod_def]; ring
    have hr0 : 0 ≤ G % P.T₁ := Int.emod_nonneg _ hT₁0.ne'
    have hr1 : G % P.T₁ < P.T₁ := Int.emod_lt_of_pos _ hT₁0
    have hu : P.u₁ τ a = P.u₁ τ b + g := by rw [← hg1]; ring
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hX, hw, hu]
    rw [hT₁] at hdiv hr1
    have hTz : 2 * ((Dw.p + Dw.q : ℕ) : ℤ) + CompHt.dimFlag Dw ≤ P.T := by exact_mod_cast hT
    have hN : (2 : ℤ) ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by
      have := b.2; push_cast; omega
    have hK : ∀ c : ℕ, ((P.T + CompHt.dimFlag Dw + c : ℕ) : ℤ) = (P.T : ℤ) + CompHt.dimFlag Dw + c := by
      intro c; push_cast; ring
    by_cases hb : (b : ℕ) = Dw.p
    · have h := h2 hb
      have hb' : ¬ (b : ℕ) < Dw.p := by omega
      have ha' : (a : ℕ) < Dw.p := by omega
      have hG' : G = P.u τ a - P.u τ b - P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) := by
        rw [hG, if_pos (by omega)]; ring
      have hgl : (P.T : ℤ) + P.c₀ ≤ g := by
        rw [hgdef, Int.le_ediv_iff_mul_le hT₁0, hT₁]; linarith
      simp only [hb', ha', if_true, if_false]
      by_cases hs0 : s = 0
      · subst hs0
        simp only [if_true, hK, Nat.cast_zero, zero_mul]
        push_cast
        linarith
      · simp only [hs0, if_false, hK]
        push_cast
        linarith
    · have h := h1 hb
      have hG' : G = P.u τ a - P.u τ b + 2 := by
        rw [hG, if_neg (by omega)]
      have hgl : (P.T : ℤ) + CompHt.dimFlag Dw + 2 + 2 * ((Dw.p + Dw.q : ℕ) : ℤ) ≤ g := by
        rw [hgdef, Int.le_ediv_iff_mul_le hT₁0, hT₁]; linarith
      have hsame : hodgeWt Dw τ a = hodgeWt Dw τ b := by
        rw [hw, hw]
        by_cases ha : (a : ℕ) < Dw.p
        · rw [if_pos ha, if_pos (by omega)]
        · rw [if_neg ha, if_neg (by omega)]
      simp only [← hw, hsame]
      split_ifs <;> simp only [hK] <;> push_cast <;> linarith

end GlobalTheory.CompHS.WtPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientEmbedsDualWeylReductionMaxWeigh
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb


set_option maxHeartbeats 1000000 in
theorem embeds_of_maxWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.BaseChange → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ τ, Antitone (w τ)) → GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → Embeds O N lam (GlobalTheory.HighWt.extW N w) ϖ Gm := by
  intro O _ _ _ _ N ι _ _ lam ϖ hϖ hlam hBC hC Gm _ _ hS hSQ w hw hJ hmax
  obtain ⟨z₀, hz₀, hfix⟩ := hJ
  obtain ⟨φ, hφ0, hφc, hφp⟩ := _root_.GlobalTheory.HighWtEmb.exists_weightForm O N ι lam ϖ hϖ Gm hSQ w z₀ hz₀ hfix
  obtain ⟨Pz, hPc, hPg, hPp, hPn, hPz0⟩ :=
    _root_.GlobalTheory.HighWtEmb.exists_coefPoly O N ι lam ϖ hϖ hlam hC Gm hSQ w hmax φ z₀ hφ0 hfix hφc hφp
  have hmuA : ∀ τ, Antitone (res N (GlobalTheory.HighWt.extW N w τ)) := fun τ => by
    rw [GlobalTheory.HighWt.res_extW]; exact hw τ
  have hle : (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) ≤
      LinearMap.ker (redT O N (GlobalTheory.HighWt.extW N w) ϖ) := by
    refine Submodule.smul_le.2 fun r hr n _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ), mul_zero, map_zero, zero_mul]
  set L := (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))).liftQ
    (redT O N (GlobalTheory.HighWt.extW N w) ϖ) hle with hL
  have hLmk : ∀ y, L (Submodule.Quotient.mk y) = redT O N (GlobalTheory.HighWt.extW N w) ϖ y := fun y => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, hL, Submodule.ker_liftQ_eq_bot]
    intro y hy
    exact _root_.GlobalTheory.HighWtEmb.mem_smul_top_of_redT_eq_zero O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC y hy
  have hsurj : ∀ z, ∃ q, L q = Pz z := by
    intro z
    have h1 : Pz z ∈ nabK (O ⧸ Ideal.span {ϖ}) N (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) := by
      have e : (fun τ => res N (GlobalTheory.HighWt.extW N w τ)) = w := funext fun τ => GlobalTheory.HighWt.res_extW N w τ
      rw [e]
      haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
      letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
      exact _root_.GlobalTheory.HighWtEmb.mem_nabK_of_toBlock (O ⧸ Ideal.span {ϖ}) N ι w (Pz z) (hPn z)
    obtain ⟨y, hy⟩ := _root_.GlobalTheory.HighWtEmb.nabK_lift O N ι (GlobalTheory.HighWt.extW N w) ϖ hϖ hmuA hBC _ h1
    exact ⟨Submodule.Quotient.mk y, hy⟩
  choose q hq using hsurj
  have hsm : ∀ (a : alg O N lam) (z : Gm), Pz z = 0 → Pz (a • z) = 0 := by
    rintro ⟨a, ha⟩
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      intro z hz
      rcases hx with ⟨g, rfl⟩ | ⟨τ, v, hp⟩
      · have e : (⟨grp O N lam g, Algebra.subset_adjoin (Or.inl ⟨g, rfl⟩)⟩ : alg O N lam) = grpA O N lam g := rfl
        rw [e, hPg, hz, map_zero]
      · rw [hPp τ v _ hp, hz, map_zero]
    | algebraMap c =>
      intro z hz
      have e : (⟨algebraMap O _ c, Subalgebra.algebraMap_mem _ c⟩ : alg O N lam) = algebraMap O (alg O N lam) c := rfl
      rw [e, hPc, hz, mul_zero]
    | add x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e, add_smul, map_add (f := _), ihx z hz, ihy z hz, add_zero]
    | mul x y hx hy ihx ihy =>
      intro z hz
      have e : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : alg O N lam) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, mul_smul]
      exact ihx _ (ihy z hz)
  let K : Submodule (alg O N lam) Gm :=
    { carrier := {z | Pz z = 0}
      add_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq, map_add (f := _)] at *; rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun a z hz => hsm a z hz }
  have hK : K = ⊥ := by
    haveI : IsSimpleOrder (Submodule (alg O N lam) Gm) := (isSimpleModule_iff _ _).1 hS
    rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
    · exact h
    · exfalso
      have : z₀ ∈ K := h ▸ Submodule.mem_top
      exact hPz0 this
  let ψ : Gm →+ NablaT O N (GlobalTheory.HighWt.extW N w) ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N (GlobalTheory.HighWt.extW N w))) :=
    { toFun := q
      map_zero' := hLinj (by rw [hq, map_zero, map_zero])
      map_add' := fun a b => hLinj (by rw [hq, map_add (f := _), map_add (f := _), hq, hq]) }
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 : Pz (a - b) = 0 := by
      rw [map_sub, ← hq a, ← hq b]
      exact sub_eq_zero.2 (congrArg L hab)
    have h2 : a - b ∈ K := h1
    rw [hK, Submodule.mem_bot] at h2
    exact sub_eq_zero.1 h2
  · intro c z
    apply hLinj
    change L (q _) = L (c • q z)
    rw [hq, hPc, LinearMap.map_smul, hq, Algebra.smul_def, MvPolynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  · intro g z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, _root_.GlobalTheory.HighWtEmb.redT_grp, hPg, ← hq z, hzy', hLmk]
  · intro τ v a a' ha ha' z y hzy
    apply hLinj
    change L (q _) = _
    have hzy' : q z = Submodule.Quotient.mk y := hzy
    rw [hq, hLmk, _root_.GlobalTheory.HighWtEmb.redT_isProj O N ι _ ϖ τ v a' ha', hPp τ v a ha, ← hq z, hzy', hLmk]

end GlobalTheory.HighWtEmb

end
end

