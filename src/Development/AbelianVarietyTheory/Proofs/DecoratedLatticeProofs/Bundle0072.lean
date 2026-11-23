module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0070
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0054
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardMatrixStepIndicesLeExp
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.IndexCountS

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE GlobalTheory.RowTypeInv GlobalTheory.SymLevelDatum GlobalTheory.IndexCount

theorem card_index_le_sharp : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ j, j + 2 ≤ N.R.m → (Fintype.card (I.β j) : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H j hj
  obtain ⟨hvG, -, -, hprod, -⟩ := BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, -, hsh, hI, -⟩ := H
  have hq : ∀ P : HeightOneSpectrum (𝓞 X.E), Formalism.L2.Col.qOf P ≠ 0 := fun P h =>
    P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hgg : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos
  have h1 : Fintype.card (I.β j) ≤ (Pr.g 0 * Pr.g 1) ^ (N.R.f * N.Nm ^ 2) := by
    rcases j with _ | i
    · obtain ⟨b, hb⟩ := hI.zero_uniq
      exact (Fintype.card_le_one_iff.2 fun a a' => (hb a).trans (hb a').symm).trans (Nat.one_le_pow _ _ hgg)
    · set n := N.R.N (i + 1) + cOf N.R (i + 1) with hn
      haveI : ∀ P : rowSG Pr sel mu, Finite (𝓞 X.E ⧸ P.1.asIdeal) := fun P => finite_res P.1
      let φ : I.β (i + 1) → ∀ P : rowSG Pr sel mu, Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal := fun b P =>
        resMat P.1 (Formalism.L2.Col.qOf P.1) (scE (N.R.N (i + 1)) fun i => i + 1) (I.h (i + 1) b P)
      have hφ : Function.Injective φ := by
        intro b b' hbb
        refine hI.inj i (by omega) b b' fun P => ?_
        have hP := hvG P.1 P.2
        have s1 := hI.stabG _ b P hP
        have s2 := hI.stabG _ b' P hP
        unfold lamYat at s1 s2
        rw [if_pos hP] at s1 s2
        refine ⟨1, Subgroup.one_mem _, (I.h (i + 1) b P)⁻¹ * I.h (i + 1) b' P, ?_, by group⟩
        unfold Jat
        rw [if_pos hP, hsh, if_pos rfl]
        exact mem_JGsym_of_cong _ _ (hq _) _ _ _ _ _ _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ s1) s2)
          (cong_of_resMat_eq _ _ (hq _) (GlobalTheory.TypePrimeUnif.intAt_div_qOf X Pr hX.ok hPr P.1 hP) s1 s2 (congrFun hbb P))
      have h2 := Nat.card_le_card_of_injective φ hφ
      have h3 : ∀ P : rowSG Pr sel mu, Nat.card (Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal) = Formalism.L2.Col.qOf P.1 ^ (n * n) := fun P => by
        rw [Nat.card_fun, Nat.card_prod, Nat.card_fin, Formalism.L2.Col.qOf,
          Ideal.absNorm_eq_natCard]
      rw [Nat.card_eq_fintype_card, Nat.card_pi, Finset.prod_congr rfl fun P _ => h3 P, Finset.prod_pow, hprod, ← pow_mul] at h2
      refine h2.trans (Nat.pow_le_pow_right hgg (Nat.mul_le_mul_left _ ?_))
      have h4 : n ≤ N.Nm := by
        rw [hn]
        unfold NumDatum.Nm Ranks.N cOf
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ N.R.m by omega)
        rw [hd]
        have : i + 1 + d - 1 - (i + 1) ≤ d := by omega
        nlinarith [Nat.zero_le (d * N.R.t)]
      rw [sq]
      exact Nat.mul_le_mul h4 h4
  rw [hg 0, hg 1] at h1
  have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
  have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
  have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
  have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
  have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
  have he : N.R.f * N.Nm ^ 2 ≤ N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  calc (Fintype.card (I.β j) : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (N.R.f * N.Nm ^ 2) := by exact_mod_cast h1
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * N.Nm ^ 2) := pow_le_pow_left₀ (by linarith) ggT _
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
    _ = Real.exp (1 * errUnit N (Pr.T u)) := by
      rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
      unfold errUnit
      push_cast
      ring

end GlobalTheory.Core.Ht2.IndexCountS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmGoodModelOfGlobalArtinReciprocity
section
namespace GlobalTheory.Corev.CmTwoClosing

theorem cmGoodModel_of_globalArtinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) : Formalism.L2.Th1.CM.CM2 :=
  GlobalTheory.T.cmLattice_good_model_unramified (_root_.GlobalTheory.IdealArtinSymbol.exists_artinSymbol hA) _root_.GlobalTheory.chebOmSt_holds

end GlobalTheory.Corev.CmTwoClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateIdealLatticeDiscrOneHomotheticIdeal
section
noncomputable section

namespace GlobalTheory.ConjLatticeCore

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem conj_lattice_core :
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have hC := GlobalTheory.ConjLattice.containsData hM
  have hm : ∀ a : D.host.K, D.host.φ₀ (a : D.host.E) ∈ M := hC.1
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => GlobalTheory.ConjLattice.lamConj_spec GlobalTheory.ConjLattice.uniformization_holds M ρ'
    (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  have hfix : ∀ ρ' : M →ₐ[ℚ] ℂ, EquidistributedConjugates.FixesK D M ρ' → ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ,
      x ≠ 0 ∧ lamConj M ρ' (lamOf D cc δ) = lamOf D c x := by
    intro ρ' hρ'
    obtain ⟨cc', δ', hc', -, he⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ ⟨hcc, hδ⟩ M ρ'
      (GlobalTheory.ConjEquidistrib.fixK_of_fixesK D M ρ' hm hρ') h2 h3 1 one_pos
    exact ⟨cc', hc'.1.1, δ', Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc' hc'.1 δ' hc'.2, he⟩
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · exact hfix ρ hρ
  · have hρ' : EquidistributedConjugates.FixesK D M (EquidistributedConjugates.conjEmb M ρ) :=
      (GlobalTheory.ConjEquidistrib.fixesK_conjEmb_iff D M ρ hm).2 hρ
    obtain ⟨c, hc, x, hx, hxe⟩ := hfix _ hρ'
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds
        GlobalTheory.ConjLattice.uniformization_holds
    have hmap : (lamConj M ρ (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj =
        lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [GlobalTheory.ConjLattice.discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [GlobalTheory.ConjLattice.eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [GlobalTheory.ConjLattice.eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) =
        (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map GlobalTheory.ConjLattice.cj := by
      rw [← hmap, GlobalTheory.ConjLattice.map_cj_map_cj]
    refine ⟨c.map (GlobalTheory.ConjLattice.conjO D), ?_, starRingEnd ℂ x, (map_ne_zero _).2 hx,
      by rw [hback, hxe, GlobalTheory.ConjLattice.lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (GlobalTheory.ConjLattice.conjO D).injective] at hbot
    exact hc hbot

end GlobalTheory.ConjLatticeCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAtTypeAndOrd
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section
namespace GlobalTheory.AtTypeExists
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

section Compl
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem intAt_iff (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, e⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff).2 hs
    have h2 := congrArg (P.valuation E) e
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one P r
  · intro h
    obtain ⟨r, s, e⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer P a h
    exact ⟨r, s.1, s.2, by rw [mul_comm]; exact e⟩

theorem valuation_norm (h : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    P.valuation E ((qOf P : ℕ) : E) = WithZero.exp (-1 : ℤ) := by
  have hm : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have e : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E) := by simp
  rw [e, HeightOneSpectrum.valuation_of_algebraMap]
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 1).2 (by simpa using hm)
  have h2 := mt (HeightOneSpectrum.intValuation_le_pow_iff_mem P ((qOf P : ℕ) : 𝓞 E) 2).1 h
  have h0 : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0 := fun h0 => h2 (by rw [h0]; exact zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  push_cast at h1 h2
  omega

end Compl

theorem exists_ord : (∀ κ τ j : ℕ, ∃ e : XIx (Fin κ) (Fin τ) j ≃ Fin (κ + j * (τ + 1)), IsOrd xPos e) ∧ (∀ κ τ l j : ℕ, ∃ e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ), IsOrd zPos e) ∧ (∀ (A : Type) (n c : ℕ) (pos : A → ℕ) (d : A ≃ Fin n), IsOrd pos d → ∃ e : A ⊕ Fin c ≃ Fin (n + c), IsOrd (yPos pos n) e) ∧ (∀ (A : Type) (n N : ℕ) (pos : A → ℕ) (d : A ≃ Fin n), IsOrd pos d → N = n + 1 → ∃ e : A ⊕ Unit ≃ Fin N, IsOrd (Sum.elim pos fun _ => N - 1) e) := by
  refine ⟨fun κ τ j => ?_, fun κ τ l j => ?_, fun A n c pos d hd => ?_, fun A n N pos d hd hN => ?_⟩
  · refine ⟨((Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv).trans (finCongr (by ring)), ?_⟩
    rintro ((i | i) | ⟨i, i'⟩) <;> simp [xPos, finProdFinEquiv]
    ring
  · refine ⟨(Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv, ?_⟩
    rintro ((i | i) | ⟨i, i'⟩) <;> simp [zPos, finProdFinEquiv]
    ring
  · refine ⟨(Equiv.sumCongr d (Equiv.refl _)).trans finSumFinEquiv, ?_⟩
    rintro (i | i)
    · simpa [yPos] using hd i
    · simp [yPos]
  · subst hN
    refine ⟨(Equiv.sumCongr d (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv, ?_⟩
    rintro (i | i)
    · simpa using hd i
    · simp

end GlobalTheory.AtTypeExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormNearNegOneAtRealPlace
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Filter Topology

namespace GlobalTheory.NormSign

open scoped Classical

theorem ext_algebraMap {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (x : K) :
    InfinitePlace.Completion.extensionEmbedding v (algebraMap K v.Completion x) = v.embedding x :=
  by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply, InfinitePlace.Completion.extensionEmbedding_coe]
    simp

theorem tendsto_completion_iff {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) {α : Type}
    {l : Filter α} (f : α → K) (c : v.Completion) :
    Tendsto (fun x => algebraMap K v.Completion (f x)) l (𝓝 c) ↔
      Tendsto (fun x => v.embedding (f x)) l (𝓝 (InfinitePlace.Completion.extensionEmbedding v c)) := by
  rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.isInducing.tendsto_nhds_iff]
  exact iff_of_eq (congrArg (fun g => Tendsto g l _) (funext fun x => ext_algebraMap v (f x)))

theorem mk_eq_mk_iff_of_isReal {K : Type} [Field K] [NumberField K] {j σ : K →+* ℂ}
    (hj : ComplexEmbedding.IsReal j) : InfinitePlace.mk σ = InfinitePlace.mk j ↔ σ = j := by
  rw [InfinitePlace.mk_eq_iff]
  refine ⟨fun h => h.elim id fun h => ?_, Or.inl⟩
  have e : ComplexEmbedding.conjugate j = j := ComplexEmbedding.isReal_iff.mp hj
  ext x
  have h1 := RingHom.congr_fun h x
  have h2 := RingHom.congr_fun e x
  rw [ComplexEmbedding.conjugate_coe_eq] at h1 h2
  calc σ x = starRingEnd ℂ (j x) := by rw [← h1, Complex.conj_conj]
    _ = j x := h2

theorem tendsto_embedding {K : Type} [Field K] [NumberField K] {j : K →+* ℂ} (hj : ComplexEmbedding.IsReal j)
    {l : Filter K}
    (hl : ∀ u : InfinitePlace K, Tendsto (fun x => algebraMap K u.Completion x) l
      (𝓝 (if u = InfinitePlace.mk j then -1 else 1))) (σ : K →+* ℂ) :
    Tendsto (fun x => σ x) l (𝓝 (if σ = j then -1 else 1)) := by
  have h := (tendsto_completion_iff (InfinitePlace.mk σ) id _).1 (hl (InfinitePlace.mk σ))
  have hc : InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk σ)
      (if InfinitePlace.mk σ = InfinitePlace.mk j then -1 else 1) = if σ = j then -1 else 1 := by
    by_cases hσ : σ = j
    · subst hσ; simp
    · rw [if_neg (fun e => hσ ((mk_eq_mk_iff_of_isReal hj).1 e)), if_neg hσ, map_one]
  rw [hc] at h
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e] at h; exact h
  · rw [e] at h
    have h' := (Complex.continuous_conj.tendsto _).comp h
    have hs : starRingEnd ℂ (if σ = j then -1 else 1) = if σ = j then -1 else 1 := by
      split_ifs <;> simp
    rw [hs] at h'
    refine h'.congr fun x => ?_
    simp [ComplexEmbedding.conjugate_coe_eq]

theorem tendsto_norm {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    {j : K →+* ℂ} (hj : ComplexEmbedding.IsReal j) {l : Filter K}
    (hσ : ∀ σ : K →+* ℂ, Tendsto (fun x => σ x) l (𝓝 (if σ = j then -1 else 1))) (u : InfinitePlace E) :
    Tendsto (fun x => u.embedding (Algebra.norm E x)) l
      (𝓝 (if u = InfinitePlace.mk (j.comp (algebraMap E K)) then -1 else 1)) := by
  letI : Algebra E ℂ := u.embedding.toAlgebra
  have hn : ∀ x : K, u.embedding (Algebra.norm E x) = ∏ σ : K →ₐ[E] ℂ, σ x :=
    fun x => Algebra.norm_eq_prod_embeddings E ℂ x
  simp_rw [hn]
  have hlim : Tendsto (fun x => ∏ σ : K →ₐ[E] ℂ, σ x) l
      (𝓝 (∏ σ : K →ₐ[E] ℂ, if (σ : K →+* ℂ) = j then (-1 : ℂ) else 1)) :=
    tendsto_finsetProd _ fun σ _ => hσ (σ : K →+* ℂ)
  convert hlim using 2
  by_cases hu : u = InfinitePlace.mk (j.comp (algebraMap E K))
  · have he : u.embedding = j.comp (algebraMap E K) := by
      rw [hu]; exact InfinitePlace.embedding_mk_eq_of_isReal (hj.comp _)
    let σ₀ : K →ₐ[E] ℂ := { toRingHom := j, commutes' := fun e => (RingHom.congr_fun he e).symm }
    have hiff : ∀ σ : K →ₐ[E] ℂ, (σ : K →+* ℂ) = j ↔ σ = σ₀ := fun σ =>
      ⟨fun h => AlgHom.coe_ringHom_injective h, fun h => by rw [h]; rfl⟩
    rw [if_pos hu, Finset.prod_congr rfl fun σ _ => if_congr (hiff σ) rfl rfl]
    simp
  · rw [if_neg hu]
    refine (Finset.prod_eq_one fun σ _ => if_neg fun h => hu ?_).symm
    have he : u.embedding = j.comp (algebraMap E K) := by
      ext e
      have := σ.commutes e
      rw [← h]
      exact this.symm
    rw [← he, InfinitePlace.mk_embedding]

end GlobalTheory.NormSign

namespace GlobalTheory.NormSign

open scoped Classical

theorem exists_norm_sign : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (j : K →+* ℂ), NumberField.ComplexEmbedding.IsReal j → ∀ (T : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ) (W : Set (Ideles E)), W ∈ nhds (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E (InfinitePlace.mk (j.comp (algebraMap E K))) (-1)) → ∃ a : Kˣ, (∀ w ∈ T, w.valuation K ((a : K) - 1) ≤ WithZero.exp (-(M : ℤ))) ∧ Units.map (ReciprocityTheory.Neutral.Bridge.HCFR.infPart E) (diagUnits E (Units.map (Algebra.norm E (S := K)) a)) ∈ W := by
  intro E K _ _ _ _ _ j hj T M W hW
  set w₀ := InfinitePlace.mk (j.comp (algebraMap E K)) with hw₀

  let y : GlobalTheory.FrobDense.Loc T := (fun u => if u = InfinitePlace.mk j then -1 else 1, fun _ => 1)
  let f : K → GlobalTheory.FrobDense.Loc T := fun x => GlobalTheory.FrobDense.proj T (algebraMap K (AdeleRing (𝓞 K) K) x)
  let l : Filter K := comap f (𝓝 y)
  haveI : l.NeBot := comap_neBot_iff.2 fun t ht => by
    obtain ⟨_, hz, a, rfl⟩ := mem_closure_iff_nhds.1 (GlobalTheory.FrobDense.denseRange_proj T y) t ht
    exact ⟨a, hz⟩
  have hf : Tendsto f l (𝓝 y) := tendsto_comap
  have hinf : ∀ u : InfinitePlace K, Tendsto (fun x => algebraMap K u.Completion x) l
      (𝓝 (if u = InfinitePlace.mk j then -1 else 1)) := fun u =>
    (((continuous_apply u).comp continuous_fst).tendsto y).comp hf
  have hfin : ∀ v : T, Tendsto (fun x => algebraMap K (v.1.adicCompletion K) x) l (𝓝 1) := fun v =>
    (((continuous_apply v).comp continuous_snd).tendsto y).comp hf
  have hσ := tendsto_embedding hj hinf

  have h0 : ∀ᶠ x in l, x ≠ 0 := by
    have hj' := hσ j
    rw [if_pos rfl] at hj'
    filter_upwards [hj'.eventually_ne (by norm_num : (-1 : ℂ) ≠ 0)] with x hx e
    exact hx (by rw [e, map_zero])

  have h1 : ∀ᶠ x in l, ∀ v : T, v.1.valuation K (x - 1) ≤ WithZero.exp (-(M : ℤ)) := by
    rw [eventually_all]
    intro v
    have ho : IsOpen {z : v.1.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(M : ℤ))} :=
      (GlobalTheory.Mem.UnitOpen.isOpen_val_le v.1 (-(M : ℤ))).preimage (continuous_sub_right 1)
    have hm : (1 : v.1.adicCompletion K) ∈ {z : v.1.adicCompletion K | Valued.v (z - 1) ≤ WithZero.exp (-(M : ℤ))} := by
      show Valued.v ((1 : v.1.adicCompletion K) - 1) ≤ _
      rw [sub_self, map_zero]
      exact zero_le'
    filter_upwards [hfin v (ho.mem_nhds hm)] with x hx
    have e : Valued.v (algebraMap K (v.1.adicCompletion K) x - 1) = v.1.valuation K (x - 1) := by
      rw [← map_one (algebraMap K (v.1.adicCompletion K)), ← map_sub]
      exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 (x - 1)
    rw [← e]
    exact hx

  let Φ : (InfiniteAdeleRing E)ˣ →* Ideles E :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  have hΦ : Continuous Φ := Continuous.units_map _ (continuous_id.prodMk continuous_const)
  let P := ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w₀ (-1)
  let p : (InfiniteAdeleRing E)ˣ := Units.map (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)) P
  have hP : Φ p = P := Units.ext rfl
  have hpW : Φ ⁻¹' W ∈ 𝓝 p := hΦ.continuousAt.preimage_mem_nhds (by rw [hP]; exact hW)
  rw [(GlobalTheory.HeckeGal.isOpenEmbedding_val_inf E).isInducing.nhds_eq_comap, mem_comap] at hpW
  obtain ⟨U, hU, hUW⟩ := hpW
  have hpu : ∀ u : InfinitePlace E, InfinitePlace.Completion.extensionEmbedding u ((p : InfiniteAdeleRing E) u) =
      if u = w₀ then -1 else 1 := by
    intro u
    by_cases hu : u = w₀
    · subst hu
      rw [if_pos rfl]
      show InfinitePlace.Completion.extensionEmbedding _ ((P : AdeleRing (𝓞 E) E).1 _) = _
      rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self]
      simp
    · rw [if_neg hu]
      show InfinitePlace.Completion.extensionEmbedding _ ((P : AdeleRing (𝓞 E) E).1 _) = _
      rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne E w₀ u hu, map_one]
  have hg : Tendsto (fun x => algebraMap E (InfiniteAdeleRing E) (Algebra.norm E x)) l
      (𝓝 (p : InfiniteAdeleRing E)) := by
    refine tendsto_pi_nhds.2 fun u => ?_
    have := (tendsto_completion_iff u (fun x => Algebra.norm E x) ((p : InfiniteAdeleRing E) u)).2
      (by rw [hpu u]; exact tendsto_norm hj hσ u)
    exact this
  have h2 : ∀ᶠ x in l, algebraMap E (InfiniteAdeleRing E) (Algebra.norm E x) ∈ U := hg hU
  obtain ⟨x, ⟨hx0, hx1⟩, hx2⟩ := ((h0.and h1).and h2).exists
  refine ⟨Units.mk0 x hx0, fun w hw => hx1 ⟨w, hw⟩, ?_⟩
  let q : (InfiniteAdeleRing E)ˣ := Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom
    (Units.map (Algebra.norm E (S := K)) (Units.mk0 x hx0))
  have hq : Units.map (ReciprocityTheory.Neutral.Bridge.HCFR.infPart E)
      (diagUnits E (Units.map (Algebra.norm E (S := K)) (Units.mk0 x hx0))) = Φ q := Units.ext rfl
  rw [hq]
  exact hUW (show (q : InfiniteAdeleRing E) ∈ U from hx2)

end GlobalTheory.NormSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NcardYbSetLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.CouplingCosetsS

theorem ncard_ybSet_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ n ≤ N.Nm, (((ybSet sel mu cst (Formalism.L2.Col.stdLat X.E n)).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsLattice X.E L → ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H n hn
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, hmu, -⟩ := H
  have hf : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm, ← Module.finrank_mul_finrank ℚ X.F X.E, hX.ok.rankE, ← hX.ok.card_Tau, mul_comm]
    rfl
  have key : ∀ L : Submodule (𝓞 X.E) (Sp X.E n), ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (2 * errUnit N (Pr.T u)) := by
    intro L
    have h1 := (GlobalTheory.CouplingCosets.finite_ncard_ybSet hPr sel mu hmu cst L).2
    rw [hf, hg 0, hg 1] at h1
    have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
    have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
    have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
    have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
    have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
    have he : 2 * N.R.f * n ≤ 2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) := by
      refine Nat.mul_le_mul_left _ (hn.trans ?_)
      have hm : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by have := N.R.two_le_m; omega)
      calc N.Nm ≤ N.Nm ^ 2 := Nat.le_self_pow two_ne_zero _
        _ ≤ N.R.m ^ 2 * N.Nm ^ 2 := Nat.le_mul_of_pos_left _ hm
    calc ((ybSet sel mu cst L).ncard : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (2 * N.R.f * n) := by exact_mod_cast h1
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * n) := pow_le_pow_left₀ (by linarith) ggT _
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
      _ = Real.exp (2 * errUnit N (Pr.T u)) := by
        rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
        unfold errUnit
        push_cast
        ring
  exact ⟨key _, fun L _ => key L⟩

end GlobalTheory.CouplingCosetsS
end

