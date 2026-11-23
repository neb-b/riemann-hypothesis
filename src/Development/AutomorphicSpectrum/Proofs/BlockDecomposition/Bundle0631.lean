module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0608
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0613
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdQuotGenericOfStdSubGeneric
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.StdQuot

section Theta

variable {k : Type} [Field k] {N : ℕ}

theorem thetaW_apply (g : GL (Fin N) k) (i j : Fin N) :
    (thetaW k N g).val i j = (g⁻¹).val (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply]

theorem thetaW_mem_unipB {u : GL (Fin N) k} (hu : u ∈ unipB k (Fin N)) : thetaW k N u ∈ unipB k (Fin N) := by
  have hi := (mem_unipB k).1 (inv_mem hu)
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [thetaW_apply]
    exact hi.1 _ _ (Fin.rev_lt_rev.2 hij)
  · rw [thetaW_apply]
    exact hi.2 _

theorem whitChar_thetaW (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ N ⟨thetaW k N u, thetaW_mem_unipB u.2⟩ = whitChar ψ N u⁻¹ := by
  show Circle.toUnits (ψ _) = Circle.toUnits (ψ _)
  refine congrArg (fun s => Circle.toUnits (ψ s)) ?_
  refine Finset.sum_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1)) (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp only [thetaW_apply]
    rfl

theorem whitChar_inv (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ⁻¹ N u = whitChar ψ N u⁻¹ := by
  rw [map_inv]
  show Circle.toUnits (ψ⁻¹ _) = (Circle.toUnits (ψ _))⁻¹
  rw [AddChar.inv_apply', map_inv]

end Theta

section Main

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {k}

variable (k)

end Main

end GlobalTheory.CompanionTheory.StdQuot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableDenominatorPowerOfLt
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

theorem zetaR_nonneg (K : Type) [Field K] [NumberField K] (r : ℝ) : 0 ≤ zetaR K r :=
  tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem step {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (m : ℕ) (s : ℝ) (hs : (m : ℝ) + 1 < s)
    (ih : Summable (fun x : hermE σ m ⧸ hermO σ m => (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)))) :
    Summable (fun x : hermE σ (m + 1) ⧸ hermO σ (m + 1) =>
      (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  obtain ⟨C, hC, hD⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD.sum_delta_le F E σ hσ
  obtain ⟨ι, hinj, hι⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.Decomp.hermClass_blocks F E σ hσ m
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs1 : 1 < s := by linarith
  set G : (hermE σ m ⧸ hermO σ m) × ((Fin m → E) ⧸ intVec E m) × FQ F → ℝ := fun p =>
    (delta (blk σ (Quotient.out p.1).1 (Quotient.out p.2.1)
      (algebraMap F E ((Quotient.out p.2.2 : Fin 1 → F) 0))) : ℝ) ^ (-s) with hG
  have hG0 : 0 ≤ G := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set r : ℝ := 2 * s - 1 - m with hr
  have hr1 : 1 < r := by rw [hr]; linarith
  have hexp : 1 - 2 * s = -((m : ℝ) + r) := by rw [hr]; ring

  have hin : ∀ (x : hermE σ m ⧸ hermO σ m) (U : (Fin m → E) ⧸ intVec E m),
      Summable (fun D : FQ F => G (x, U, D)) ∧
      ∑' D : FQ F, G (x, U, D) ≤ C * zetaR F (2 * s - 1) * (delta (Quotient.out x).1 : ℝ) ^ (-s) *
        (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) := by
    intro x U
    have := hD m (Quotient.out x).1 (Quotient.out x).2 (Quotient.out U) s hs1
    rw [hexp] at this
    exact this
  set A : ℝ := C * zetaR F (2 * s - 1) with hA
  have hA0 : 0 ≤ A := mul_nonneg hC.le (zetaR_nonneg _ _)
  have hmid : ∀ x : hermE σ m ⧸ hermO σ m,
      Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) ∧
      ∑' q : ((Fin m → E) ⧸ intVec E m) × FQ F, G (x, q) ≤
        A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
    intro x
    obtain ⟨hU, hUle⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.SumU.sum_tor E m (Quotient.out x).1 r hr1
    have hδ : (0 : ℝ) < delta (Quotient.out x).1 :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex.delta_index E m _).1)
    set B : ℝ := A * (delta (Quotient.out x).1 : ℝ) ^ (-s) with hB
    have hB0 : 0 ≤ B := mul_nonneg hA0 (Real.rpow_nonneg hδ.le _)
    have hsum : Summable (fun U : (Fin m → E) ⧸ intVec E m => ∑' D : FQ F, G (x, U, D)) :=
      Summable.of_nonneg_of_le (fun U => tsum_nonneg fun D => hG0 _) (fun U => (hin x U).2)
        (hU.mul_left B)
    have hS : Summable (fun q : ((Fin m → E) ⧸ intVec E m) × FQ F => G (x, q)) :=
      (summable_prod_of_nonneg (fun q => hG0 (x, q))).mpr ⟨fun U => (hin x U).1, hsum⟩
    refine ⟨hS, ?_⟩
    rw [hS.tsum_prod' (fun U => (hin x U).1)]
    calc ∑' U : (Fin m → E) ⧸ intVec E m, ∑' D : FQ F, G (x, U, D)
        ≤ ∑' U : (Fin m → E) ⧸ intVec E m, B *
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          hsum.tsum_le_tsum (fun U => (hin x U).2) (hU.mul_left B)
      _ = B * ∑' U : (Fin m → E) ⧸ intVec E m,
            (Ideal.absNorm (tor (Quotient.out x).1 (Quotient.out U)) : ℝ) ^ (-((m : ℝ) + r)) :=
          tsum_mul_left
      _ ≤ B * (delta (Quotient.out x).1 * zetaR E r) := mul_le_mul_of_nonneg_left hUle hB0
      _ = A * zetaR E r * (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) := by
          have : (delta (Quotient.out x).1 : ℝ) ^ (-(s - 1)) =
              (delta (Quotient.out x).1 : ℝ) ^ (-s) * delta (Quotient.out x).1 := by
            rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
          rw [this, hB]
          ring
  have hGs : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun x => (hmid x).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun x => tsum_nonneg fun q => hG0 _) (fun x => (hmid x).2)
      (ih.mul_left _)
  refine (hGs.comp_injective hinj).congr fun x => ?_
  simp only [Function.comp, hG, hι x]

theorem summable_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  intro F E _ _ _ _ _ σ hσ n
  induction n with
  | zero =>
    intro s _
    haveI : Subsingleton (hermE σ 0) := ⟨fun a b => Subtype.ext (Matrix.ext fun i => i.elim0)⟩
    haveI : Subsingleton (hermE σ 0 ⧸ hermO σ 0) := QuotientAddGroup.mk_surjective.subsingleton
    exact Summable.of_finite
  | succ n ih =>
    intro s hs
    push_cast at hs
    exact step σ hσ n s hs (ih (s - 1) (by linarith))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterBlockValue
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.NuVal

theorem ord_eq_ordL_unit {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : (w.adicCompletion E)ˣ) : GlobalTheory.SmGL.ord (w.adicCompletion E) x = ordL (x : w.adicCompletion E) := by
  have h : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion]
  unfold ordL
  rw [dite_eq_right h]
  congr 1
  conv_lhs => rw [← WithZero.coe_unzero h]
  first | rfl | simp [WithZero.log]

theorem unrChar_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (c : ℂˣ) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) = (c : ℂ) ^ (i * b + j * a) := by
  intro E _ _ _ a b w c i j m h1 h2
  have hneg : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (-1) = 1 := by
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.ord_eq_zero (by simp), zpow_zero]
  have hd1 : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (GeneralLinearGroup.det m.1) = c ^ i := by
    rw [GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL_unit]
    erw [h1]
    simp
  have hd2 : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (GeneralLinearGroup.det m.2) = c ^ j := by
    rw [GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL_unit]
    erw [h2]
    simp
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, hneg, hd1, hd2, one_pow, one_mul, ← pow_mul, ← pow_mul,
    ← pow_add]
  simp

end GlobalTheory.CompanionTheory.CtS.NuVal
end
end

