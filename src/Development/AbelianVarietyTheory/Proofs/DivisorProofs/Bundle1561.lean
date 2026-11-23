module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SplitFullyUnr

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ramificationIdx_eq_one_of_splitsFully (v : HeightOneSpectrum (𝓞 F))
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v) (q : Ideal (𝓞 E)) (hq : q ∈ (v.asIdeal.under ℤ).primesOver (𝓞 E)) :
    q.ramificationIdx ℤ = 1 := by
  classical
  set P : Ideal ℤ := v.asIdeal.under ℤ with hP
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hfin : (P.primesOver (𝓞 E)).Finite := Set.finite_of_ncard_pos (by rw [h]; exact hn)
  letI : Fintype (P.primesOver (𝓞 E)) := hfin.fintype
  have hcard : Fintype.card (P.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq]; exact h
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [RingOfIntegers.rank] at hsum
  have hpos : ∀ r ∈ (Finset.univ : Finset (P.primesOver (𝓞 E))),
      (fun _ => 1) r ≤ r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := fun r _ =>
    Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) r.1) (Ideal.inertiaDeg_pos r.1 ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).1 (by rw [← Fintype.card_eq_sum_ones, hcard, hsum])
  have hm := (hall ⟨q, hq⟩ (Finset.mem_univ _)).symm
  exact Nat.eq_one_of_mul_eq_one_right hm

theorem under_eq_span_of_mem (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (hw : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  have : NeZero w.asIdeal := ⟨w.ne_bot⟩
  have hq := Nat.absNorm_under_prime w.asIdeal
  have hd : (Ideal.absNorm (w.asIdeal.under ℤ) : ℤ) ∣ (p : ℤ) := by
    rw [← Int.cast_mem_ideal_iff]; simpa using hw
  have he : Ideal.absNorm (w.asIdeal.under ℤ) = p :=
    (Nat.prime_dvd_prime_iff_eq hq hp).1 (Int.natCast_dvd_natCast.1 hd)
  rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), he]

theorem not_mem_sq_of_ramificationIdx {p : ℕ} (hl : p.Prime) (w : HeightOneSpectrum (𝓞 E))
    (hv : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (he : w.asIdeal.ramificationIdx ℤ = 1) :
    ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {((p : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have := w.isPrime
  have : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hl.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  intro hsq
  have hne : Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) w.asIdeal ≠ 1 := by
    rw [Ideal.ramificationIdx'_ne_one_iff hle, hmap, Ideal.span_le]; simpa using hsq
  exact hne he

theorem not_le_differentIdeal (v : HeightOneSpectrum (𝓞 F)) (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully E v) :
    ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  set p := Ideal.absNorm (v.asIdeal.under ℤ) with hpdef
  have hp : p.Prime := Nat.absNorm_under_prime v.asIdeal
  have hpv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := Int.absNorm_under_mem v.asIdeal
  have hP : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := (Int.ideal_span_absNorm_eq_self _).symm
  have hE : ∀ w : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ w.asIdeal → ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
    intro w hw
    have hmem : w.asIdeal ∈ (v.asIdeal.under ℤ).primesOver (𝓞 E) :=
      ⟨w.isPrime, ⟨by rw [hP, under_eq_span_of_mem w hp hw]⟩⟩
    exact not_mem_sq_of_ramificationIdx hp w hw (ramificationIdx_eq_one_of_splitsFully v h _ hmem)
  have hnd := GlobalTheory.SplitUnram.not_dvd_different hp v hpv (GlobalTheory.SplitUnram.not_mem_sq_of_ext hE v)
  exact fun hle => hnd (Ideal.dvd_iff_le.2 hle)

end GlobalTheory.SplitFullyUnr

theorem GlobalTheory.SplitFullyUnr.psiUnr_of_splitsFully : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SplitsFully D.host.E v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr W.ψ v := by
  intro D T L sc G W v hv
  exact GlobalTheory.BaseGoodPlace.psiUnr_of_not_le W.ψ_std v (GlobalTheory.SplitFullyUnr.not_le_differentIdeal v hv)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeylElementDoubled
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblDiag

open Matrix

theorem swap_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  intro F E _ _ _ _ _ σ n J v f hQf hff hfc
  set Q : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with hQdef
  have hQQ : Q * Q = Q := by
    have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (1 - Q)
      (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [← hQdef, smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
    exact h.symm
  set q : AE F E := algebraMap (AF F) (AE F E) Q with hqdef
  set p : AE F E := algebraMap (AF F) (AE F E) (1 - Q) with hpdef
  have hp : p = 1 - q := by rw [hpdef, map_sub, map_one]
  have hqq : q * q = q := by rw [hqdef, ← map_mul, hQQ]
  have hqf : q * f = f := by rw [hqdef, ← Algebra.smul_def]; exact hQf
  have hcp : cA σ p = p := AlgHom.commutes _ _
  have hpp : p * p = p := by rw [hp]; linear_combination hqq
  have hpf : p * f = 0 := by rw [hp]; linear_combination -hqf
  have hpcf : p * cA σ f = 0 := by rw [← hcp, ← map_mul, hpf, map_zero]
  have hsm : ∀ (m : Type) [Fintype m] [DecidableEq m] (N : Matrix m m (AE F E)), (1 - Q) • N = p • N :=
    fun m _ _ N => (algebraMap_smul (AE F E) (1 - Q) N).symm
  have hmap : ∀ a : AE F E, (a • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = cA σ a • 1 := by
    intro a; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
    split_ifs <;> simp
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
    Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
      ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) with hMdef
  have hM : M = Matrix.fromBlocks (p • 1) (f • 1) (f • 1) (p • 1) := by
    rw [hMdef, ← hQdef, hsm]

  have hMM : M * M = 1 := by
    rw [hM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1 <;> ext i j <;> simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
  have hU : Mᵀ * dbl (incM F J) * M.map (cA σ) = dbl (incM F J) := by
    rw [hM, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, hmap, hcp, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, smul_smul, smul_neg]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.neg_apply]
    all_goals
      first
        | linear_combination incM F J i j * (hpp - hfc + hp)
        | linear_combination incM F J i j * (hfc - hpp - hp)
        | linear_combination incM F J i j * (hpcf - hpf)
        | linear_combination incM F J i j * (hpf - hpcf)
        | linear_combination incM F J i j * (hpcf + hpf)
        | linear_combination incM F J i j * (-hpcf - hpf)

  refine ⟨⟨⟨M, M, hMM, hMM⟩, hU⟩, rfl, ?_, Subtype.ext (Units.ext hMM), ?_⟩
  · intro u hu
    show u • (M - 1) = 0
    have hQu : u * Q = 0 := by
      have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu
      rwa [← hQdef, smul_eq_mul] at h
    set ua : AE F E := algebraMap (AF F) (AE F E) u with huadef
    have huq : ua * q = 0 := by rw [huadef, hqdef, ← map_mul, hQu, map_zero]
    have huf : ua * f = 0 := by rw [← hqf]; linear_combination f * huq
    rw [← algebraMap_smul (AE F E) u, ← huadef, hM, ← Matrix.fromBlocks_one]
    ext (i | i) (j | j) <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, smul_eq_mul] <;>
      first
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf)
          | linear_combination 1 * (-((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf))
          | linear_combination 1 * (- (ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * (-(ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
  · intro k hk gd gd' hgd hgd'
    apply Subtype.ext
    apply Units.ext
    show M * ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * M =
      ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    have hK : p • (mat k - 1) = 0 := by
      rw [← hsm]
      exact hk (1 - Q) (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    have hKe : ∀ i j, p * mat k i j = p * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j := by
      intro i j
      have h := congrFun (congrFun hK i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_eq_mul] at h
      linear_combination h
    rw [hgd, hgd', hM, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, smul_smul, smul_zero]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    all_goals
      first
        | linear_combination 1 * (mat k i j * hpp + hKe i j + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hp)
        | linear_combination 1 * (mat k i j * hpf + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpf)
        | linear_combination 1 * (mat k i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpp + mat k i j * hp - hKe i j)

end GlobalTheory.DblDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateShellLeDivModulus
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

theorem modulus_mul_measure_shell_le : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ C : Set G, IsCompact C → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (b : G) (κ : ℝ≥0∞), (∀ m ∈ M, b * m = m * b) → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → ∀ S : Set G, MeasurableSet S → (∀ x ∈ S, ∃ u ∈ N, ∃ m ∈ M, ∃ y ∈ C, b * x = u * m * y) → κ * μ (S ∩ D) ≤ B := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM hL μ D hμ hD C hC
  obtain ⟨U, c, hU, hμU, hc, hlow⟩ := _root_.GlobalTheory.ResLine.LowerAverage.average_lower G N M Λ ν π DN DM hL μ hμ C hC
  have hX : ν DN * π DM * μ U ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hL.finN hL.finM) hμU
  refine ⟨ν DN * π DM * μ U / c, ENNReal.div_ne_top hX hc, ?_⟩
  intro b κ hb hκ S hS hSx
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inr hX)]
  have hφ : Measurable (U.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hU.measurableSet
  have hw := _root_.GlobalTheory.ResLine.lintegral_two_step_unfolding G N M Λ ν π DN DM hL μ D hμ hD
    (fun x => U.indicator (1 : G → ℝ≥0∞) (b * x)) (hφ.comp (measurable_const_mul b))
  rw [lintegral_mul_left_eq_self (U.indicator (1 : G → ℝ≥0∞)) b,
    lintegral_indicator_one hU.measurableSet] at hw
  rw [← hw]
  have h1 : κ * μ (S ∩ D) * c = ∫⁻ x in D, S.indicator (fun _ => κ * c) x ∂μ := by
    rw [lintegral_indicator_const hS, Measure.restrict_apply hS]; ring
  rw [h1]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    obtain ⟨u₀, hu₀, m₀, hm₀, y, hy, hxy⟩ := hSx x hx
    have h2 := hlow u₀ hu₀ m₀ hm₀ y hy
    rw [← hxy] at h2
    refine le_trans (mul_le_mul_right h2 κ) (le_trans (lintegral_const_mul_le _ _) (le_of_eq ?_))
    refine lintegral_congr fun m => ?_
    have h3 := hκ (fun g => U.indicator (1 : G → ℝ≥0∞) (g * m * (b * x)))
      (hφ.comp ((measurable_id.mul_const _).mul_const _))
    rw [← h3]
    refine lintegral_congr fun u => ?_
    congr 1
    have h4 := hb m m.2
    calc b * (u : G) * b⁻¹ * m * (b * x) = b * u * b⁻¹ * (m * b) * x := by group
      _ = b * u * b⁻¹ * (b * m) * x := by rw [h4]
      _ = b * (u * m * x) := by group
  · rw [Set.indicator_of_notMem hx]; exact zero_le

end GlobalTheory.ResLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRationalPointsOfUnipotentCoordsRational
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem mem_ratPts_of_crd_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (u : GAd σ J) (b₀ : Matrix (Fin j) (Fin m) E) (c₀ : Matrix (Fin j) (Fin j) E), Crd σ J C D Z J₀ u (adMat F b₀) (adMat F c₀) → u ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u b₀ c₀ h
  have hmul : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    unfold adMat
    exact Matrix.map_mul (L := X) (M := Y) (f := (inclR (F := F) (AF F) : E →+* _))
  have hadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X + Y) = adMat F X + adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  have hsub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) E),
      adMat F (X - Y) = adMat F X - adMat F Y := fun X Y => by
    ext i k; simp [adMat]
  refine _root_.GlobalTheory.SphEis.mem_ratPts_of_cols_rat F E σ n J j m C D Z J₀ hF u C
    (D - Z * (J₀⁻¹ * cT (σ : E →+* E) b₀) + C * c₀) (Z + C * b₀) h.onC ?_ ?_
  · rw [h.onZ, hadd, hmul]
  · rw [h.onD, hadd, hsub, hmul, hmul, hmul]
    rfl

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModTSupConj
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem modT_sup_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (t : T),
    modT G t ⊔ D.host.conj • modT G t = ⊤ := by
  intro D T L sc μ₀ hL G t
  classical
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hund : ∀ PP PP' : HeightOneSpectrum (𝓞 D.host.E), PP.asIdeal = D.host.conj • PP'.asIdeal →
      (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') := by
    intro PP PP' h
    have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv PP' PP := by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      intro x y hxy
      have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
      rw [hy, h]
      exact Ideal.smul_mem_pointwise_smul_iff.symm
    exact (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) PP' PP).2
      (Or.inr hc)
  have hmax' : ∀ PP : HeightOneSpectrum (𝓞 D.host.E), (D.host.conj • PP.asIdeal).IsMaximal := by
    intro PP
    have := PP.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => PP.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have hmem : ∀ w ∈ twPl G t, w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
    intro w hw
    rw [twPl, Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union] at hw
    exact ⟨hw.1.resolve_left hw.2, hw.2⟩
  have hoff : ∀ w ∈ twPl G t, w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro w hw hS
    obtain ⟨hQ, hW⟩ := hmem w hw
    rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
    · exact G.pl.levelPlace_ne_basePlace t w hQ h0
    · apply hW
      rw [G.pl.w_Q t w hQ h1]
      exact Finset.mem_image_of_mem _ hS
  have hAB : ∀ v ∈ G.pl.S0, ∀ w ∈ twPl G t, (G.pl.w v).asIdeal ≠ D.host.conj • w.asIdeal := by
    intro v hv w hw h
    exact hoff w hw (by rw [← hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBA : ∀ w ∈ twPl G t, ∀ v ∈ G.pl.S0, w.asIdeal ≠ D.host.conj • (G.pl.w v).asIdeal := by
    intro w hw v hv h
    exact hoff w hw (by rw [hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBB : ∀ w ∈ twPl G t, ∀ w' ∈ twPl G t, w.asIdeal ≠ D.host.conj • w'.asIdeal := by
    intro w hw w' hw' h
    refine (hL.Q_pl t w' (hmem w' hw').1).2 w (hmem w hw).1 fun c hc => ⟨D.host.conj • c, ?_, ?_⟩
    · rw [h]; exact Ideal.smul_mem_pointwise_smul _ _ _ hc
    · exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [modT, smul_mul', ← Ideal.isCoprime_iff_sup_eq]
  refine IsCoprime.mul_left (IsCoprime.mul_right ?_ ?_) (IsCoprime.mul_right ?_ ?_) <;> rw [Ideal.isCoprime_iff_sup_eq]
  · exact condE_sup_conj G.pl
  · rw [Finset.smul_prod']
    refine Ideal.prod_sup_eq_top fun v hv => Ideal.sup_prod_eq_top fun w hw => ?_
    exact Ideal.pow_sup_eq_top (Ideal.IsMaximal.coprime_of_ne (G.pl.w v).isMaximal (hmax' w) (hAB v hv w hw))
  · rw [GlobalTheory.FunObj.SqNum.condE, Finset.smul_prod']
    simp only [smul_pow']
    refine Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun v hv => ?_
    exact Ideal.sup_pow_eq_top (Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' _) (hBA w hw v hv))
  · rw [Finset.smul_prod']
    exact Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun w' hw' =>
      Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' w') (hBB w hw w' hw')

end GlobalTheory.SqTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTower

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc}

def IsStageC (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) {A A' WW : HSp D} (X : Tri T A A' WW) : Prop :=
  p ≤ pp D j ∧ q ≤ qq D j ∧ A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p ∧
    A'.rank + 2 * qq D j = rankV D i j + 2 * q ∧ NegIdx A p ∧ NegIdx A' q ∧ NegIdx WW (p + q) ∧
    X.Is W.ψ W.θ (fun t => Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (fun _ => G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (fun t => nuH G t i j) (locPl G)

theorem negIdx_of_isStd {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) : NegIdx V 0 := fun τ => by
  have : gramAt D V τ = 1 := by rw [gramAt, h.1]; simp
  rw [this]
  refine ⟨(Equiv.sumEmpty _ _).symm, 1, ?_⟩
  ext (a | a) (b | b)
  · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
  all_goals first | exact a.elim0 | exact b.elim0

theorem IsBottomTri.isStageC {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (h : IsBottomTri W i j X) : IsStageC W i j 0 0 X := by
  have r := ranks_exact D i j
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, negIdx_of_isStd h.std, negIdx_of_isStd h.std',
    negIdx_of_isStd h.stdW, h.is⟩
  · rw [h.rank]; simpa [pp] using r.1
  · rw [h.rank']; simpa [qq] using r.2.1

end GlobalTheory.SqTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceFixedVectorsNeBotTransportStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_fixedVectors_ne_bot_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL (k := k)) (x' : IrrGL (k := k')), RepRel i x x' → GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne k (Fin x.1)) ≠ ⊥ → GlobalTheory.PRep.fixed x'.rep (GlobalTheory.SplitWeil.KOne k' (Fin x'.1)) ≠ ⊥ := by
  first | (exact @GlobalTheory.KOneTransport.fixed_ne_bot_transport) | (exact GlobalTheory.KOneTransport.fixed_ne_bot_transport) | (intros; apply GlobalTheory.KOneTransport.fixed_ne_bot_transport  <;> assumption)
end

