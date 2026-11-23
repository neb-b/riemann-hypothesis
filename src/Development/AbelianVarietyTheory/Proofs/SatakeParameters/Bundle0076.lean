module

public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.GaussJetBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockRowsOfFills
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory

theorem fock_rows_of_fills : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (hT : GatTies D) (Y : LatInst D), FillsAll hT Y → (Y.Fl u w hg).t = D.R.t → ∀ (v : Fin (D.gat u w hg).P.nV) (s : Fin ((D.gat u w hg).P.n' v)) (i : ℕ), i < D.R.m → ∀ r : ℕ, ((FormalGroupSystem.nu (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) (i + 1) s (r + 1) : ℤ) : ℝ) = if r < D.R.N i then DV.nuRow D u (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) r else 0 := by
  intro D u w hg hT Y hF ht v s i hi r
  have hk : (D.gat u w hg).P.m + 1 = D.R.k := hT.gat_k u w hg
  have hw : ∀ b (hb : b < D.R.m), (((Y.Fl u w hg).w v (b + 1) s : ℤ) : ℝ) =
      ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨b, hb⟩ : ℝ) - kaJ D (b + 1) := by
    intro b hb
    rw [hF u w hg v s (b + 1) (by simp [SizeData₂.lifts]; omega)]
    simp [wj, hb, D.hcW_e]
  have hwS : DV.wSz D (i + 1) (hT.gat_pos u w hg ⟨v, s⟩) = ((D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).e ⟨i, hi⟩ : ℝ) := by
    simp [DV.wSz, show 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m by omega, D.hcW_e]
  unfold FormalGroupSystem.nu FormalGroupSystem.NN
  rw [ht]
  by_cases h1 : r < D.R.k
  · rw [if_pos (by omega), if_pos (show r < D.R.N i by simp [Ranks.N]; omega)]
    unfold FormalGroupSystem.lamI
    rw [dite_eq_left (by omega)]
    unfold DV.nuRow DV.srcPar
    rw [dite_eq_left h1, hwS]
    have hl : (((D.gat u w hg).P.lam0 v s ⟨r + 1 - 1, by omega⟩ : ℤ) : ℚ) =
        (D.hcW u (hT.gat_pos u w hg ⟨v, s⟩)).u ⟨r, h1⟩ - ((D.R.k : ℚ) - 1) / 2 + r := by
      rw [hT.gat_lam, (D.fm u).lam_eq 0 (Nat.zero_le _)]
      simp [hcToWeightQ, rhoVec, Ranks.N, h1]
      ring
    have hlR := congrArg (Rat.cast : ℚ → ℝ) hl
    push_cast at hlR ⊢
    rw [hlR, hw i hi]
    simp only [kaJ, Ranks.N, Nat.add_sub_cancel]
    push_cast
    ring
  · rw [if_neg (by omega)]
    obtain ⟨q, rfl⟩ : ∃ q, r = D.R.k + q := ⟨r - D.R.k, by omega⟩
    have hrk : D.R.k + q + 1 - ((D.gat u w hg).P.m + 2) = q := by omega
    rw [hrk]
    have ht1 : 0 < D.R.t + 1 := Nat.succ_pos _
    have hM : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + (D.R.t + 1) := by ring
    have hNi : D.R.N i = D.R.k + i * (D.R.t + 1) := rfl
    by_cases h2 : q < i * (D.R.t + 1)
    · have hb : q / (D.R.t + 1) < i := by
        rw [Nat.div_lt_iff_lt_mul ht1]; exact h2
      rw [if_pos (by omega), if_pos (by omega)]
      unfold DV.nuRow DV.srcPar
      rw [dite_eq_right h1]
      simp only [Nat.add_sub_cancel_left]
      rw [dite_eq_left (by omega), hwS]
      have hr : q = q / (D.R.t + 1) * (D.R.t + 1) + q % (D.R.t + 1) := by
        have := Nat.div_add_mod q (D.R.t + 1); rw [mul_comm] at this; omega
      have hrR : (q : ℝ) = ((q / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1) + ((q % (D.R.t + 1) : ℕ) : ℝ) := by
        exact_mod_cast hr
      push_cast
      rw [hw _ (by omega), hw i hi]
      simp only [kaJ, Ranks.N]
      push_cast
      rw [hrR]
      ring
    · rw [if_neg (show ¬ D.R.k + q < D.R.N i by omega)]
      by_cases h3 : q < i * (D.R.t + 1) + (D.R.t + 1)
      · have hb : q / (D.R.t + 1) = i := by
          apply le_antisymm
          · rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul ht1, Nat.succ_mul]; omega
          · rw [Nat.le_div_iff_mul_le ht1]; omega
        rw [if_pos (by omega), hb]
        simp
      · rw [if_neg (by omega)]
        simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSign
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobSign

theorem frobG_isArithFrob_and_sign : ∀ (D : D7) (l : ℕ) [Fact l.Prime], l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d →
    (∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q) ∧
    ((((DV.frobG D l).1.2 : ℤˣ) : ℤ) = jacobiSym (-(D.host.d : ℤ)) l) := by
  intro D l hl h2 hq hd
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  have hall : ∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q :=
    fun Q _ _ => GlobalTheory.FrobEmb.isArithFrobAt_frobG D l hl.out Q
  refine ⟨hall, ?_⟩
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have hlI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hlZ.ne_zero).2 hlZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  have hg : D.host.gal (D.host.sigmaOf (DV.frobG D l)) = DV.frobG D l := MulEquiv.apply_symm_apply _ _
  have h := ((D.host.der.frob l hlN P).2.2.1 _ (hall P)).2.1
  rw [hg] at h
  exact h

end GlobalTheory.FrobSign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralEigenCombination
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.IntegralEigenCombination

theorem eigGen_integral_comb : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ τ : D.what₂.Tau, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (a : Fin n → D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, a j ∈ D.host.AA0) ∧ ∀ τ', ∑ j, r j * tauEmb D lm τ' (a j) = if τ' = τ then lamC lm (cD τ) else 0 := by
  intro D cD hD p _ lm τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hmem : s ∈ TaylorLogMetric.ellT D M τ := by rw [hsp]; exact Submodule.mem_span_singleton_self s
  have hv : (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s ∈ TaylorLogMetric.mmM D M :=
    Submodule.mem_comap.1 hmem
  obtain ⟨n, f, v, hfv⟩ := Submodule.mem_span_set'.1 hv
  have hva : ∀ j, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      (v j : D.what₂.Tau → M) = fun τ => TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ a) := fun j => (v j).2
  choose a ha hav using hva
  obtain ⟨g, hg⟩ := GlobalTheory.Proof.DirectionalDerivative.exists_lamHom lm (algebraMap M ℂ)
  have hg' : ∀ x : M, lamC lm (x : ℂ) = g x := hg
  refine ⟨n, fun j => g ((f j : 𝓞 M) : M), a, fun j => ?_, ha, fun τ' => ?_⟩
  · exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int g (f j).isIntegral_coe)
  · have e : ∀ j, tauEmb D lm τ' (a j) = g (TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) := by
      intro j
      rw [← hg', TaylorLogMetric.liftM, dite_eq_left (hM _ _)]
      rfl
    have hc := congrFun hfv τ'
    simp only [Finset.sum_apply, Pi.smul_apply, hav] at hc
    simp only [e, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    have hc' : (∑ j, ((f j : 𝓞 M) : M) * TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) =
        (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s τ' := by
      rw [← hc]; rfl
    rw [hc']
    by_cases h : τ' = τ
    · subst h; simp [hsc.symm, hg']
    · simp [h]
end GlobalTheory.Proof.IntegralEigenCombination
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrrTransferAbsIrr
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section
namespace GlobalTheory.IrrTransfer

open Matrix

theorem span_top_of_irred_algClosed {Γ : Type} [Group Γ] {k K : Type} [Field k] [Field K] [IsAlgClosed K]
    {r : ℕ} (hr : 1 ≤ r) (rb : Γ →* GL (Fin r) k) (ι : k →+* K)
    (h : ∀ W : Submodule K (Fin r → K), IsInv (mapRep ι rb) W → W = ⊥ ∨ W = ⊤) :
    Submodule.span k (Set.range fun g => (rb g : Matrix (Fin r) (Fin r) k)) = ⊤ := by
  letI : Algebra k K := ι.toAlgebra
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hirr : IsIrrSub (mapRep ι rb) ⊤ :=
    ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => h W hW⟩
  have hs := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  apply GlobalTheory.BurnsideField.span_eq_top_of_span_map (K := K)
  convert hs using 3
  ext g a b
  simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep, RingHom.algebraMap_toAlgebra]

theorem span_image_top (k' : Type) [Field k'] (n : ℕ) :
    Submodule.span (AlgebraicClosure k')
      ((fun v : Fin n → k' => (algebraMap k' (AlgebraicClosure k')) ∘ v) ''
        ((⊤ : Submodule k' (Fin n → k')) : Set (Fin n → k'))) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [pi_eq_sum_univ' u]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Pi.single a 1, trivial, ?_⟩)
  ext c
  by_cases hc : c = a
  · subst hc; simp
  · simp [Pi.single_eq_of_ne hc]

theorem absIrr_of_algClosed {Γ : Type} [Group Γ] {k K k' : Type} [Field k] [Field K] [IsAlgClosed K]
    [Field k'] {r : ℕ} (hr : 1 ≤ r) (rb : Γ →* GL (Fin r) k) (ι : k →+* K)
    (h : ∀ W : Submodule K (Fin r → K), IsInv (mapRep ι rb) W → W = ⊥ ∨ W = ⊤) (φ : k →+* k') :
    AbsIrrSub (mapRep φ rb) ⊤ := by
  have hsp := span_top_of_irred_algClosed hr rb ι h
  letI : Algebra k (AlgebraicClosure k') := ((algebraMap k' (AlgebraicClosure k')).comp φ).toAlgebra
  have hirr := GlobalTheory.BurnsideIff.eq_bot_or_top_of_span_eq_top (K := AlgebraicClosure k') _ hsp
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [AbsIrrSub, span_image_top]
  refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => hirr W fun g v hv => ?_⟩
  have := hW g v hv
  simpa [mapRep, Matrix.map_map, RingHom.algebraMap_toAlgebra] using this

end GlobalTheory.IrrTransfer

namespace GlobalTheory.StringRepresentationDecomposition

theorem irr_transfer_absIrr : ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {k k' : Type} [Field k] [Field k']
    {r : ℕ}, 1 ≤ r → ∀ (rb : Γ →* GL (Fin r) k) (ι : k →+* Formalism.CyclotomicNorms.Fbar l),
    Formalism.CyclotomicNorms.IrredOn (mapRep ι rb) ⊤ → ∀ φ : k →+* k', AbsIrrSub (mapRep φ rb) ⊤ := by
  intro l _ Γ _ k k' _ _ r hr rb ι h φ
  exact GlobalTheory.IrrTransfer.absIrr_of_algClosed hr rb ι (fun W hW => h W fun g _ v hv => hW g v hv) φ

end GlobalTheory.StringRepresentationDecomposition
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
section
noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType

namespace GlobalTheory.CuspRep.AlgExpo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem dchi_atEmb (χ : HChar E) (τ : E →+* ℂ) (z : ℂ) :
    dchi χ (atEmb τ z) = expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [atEmb_eq, map_add (f := _), map_smul, map_smul]
  simp only [expo, atEmb_conj, map_one, Complex.conj_I, e, map_neg, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (z.im * dchi χ (atEmb τ Complex.I)) * Complex.I_mul_I

theorem dchi_eq_sum (χ : HChar E) (x : Cinf E) : dchi χ x = ∑ φ : E →+* ℂ, expo χ φ * coord φ x := by
  classical
  have hx : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dchi_atEmb]
  simp only [coord_atEmb', mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem chiInf_eq_prod (χ : HChar E) (n : (E →+* ℂ) → ℤ) (hn : ∀ τ, expo χ τ = n τ) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, coord φ (u : Cinf E) ^ n φ := by
  rw [← expU_log u, chiInf_expU, dchi_eq_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [coord_expU, hn, ← Complex.exp_int_mul]

theorem isAlgPos_of_expo : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E)
    (n : (E →+* ℂ) → ℤ), (∀ τ, expo χ τ = n τ) → IsAlgPos χ n := by
  intro E _ _ _ χ n hn k _
  have e := chiInf_eq_prod χ n hn (Units.map (diagInf E).toMonoidHom k)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eq]
  refine e.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (coord_algebraMap φ (k : E))

end GlobalTheory.CuspRep.AlgExpo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsOfCrystallineTwistBlockDecomposition
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem jumpIn_of_reads : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → (∀ (A A' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)) (Pr : A.V →ₗ[↥C.LL.1] A'.V →ₗ[↥C.LL.1] ↥C.LL.1), IsDual1 (Br.PD D.loc D.nbr i w hw) A.ρ A'.ρ Pr → IsCrys (Br.PD D.loc D.nbr i w hw) A.ρ → IsCrys (Br.PD D.loc D.nbr i w hw) A'.ρ) → (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → (∀ x, Continuous (C.loc (rTwO D.nd i r x))) → Continuous (C.loc (WpO D.nd i ρ π)) → (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rTwO D.nd i r x)))) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → (∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∃ g, Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g ∧ (∀ x a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rDuO D.nd i r x))) τ a → a ∈ jT1 (hcAt D g) (liftIdx D i) (pos ε g)) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (T2O D.nd i ρ π))) τ a = if a ∈ jT2 (hcAt D g) (liftIdx D i) (pos ε g) then 1 else 0) → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) := by
  intro D L C₀ i w hw C r ρ π ε κ hR hA hT hinc hc hcW hcr hS hτ
  have hε := _root_.GlobalTheory.HTW.Rec.enl_locChi_epsU i w hw C hinc
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HTW.Rec.twistedDuals_eq_tateDuals i w hw C r ρ π hε
  have hO := goodO_finExt_integers (D.nd.l i) C.LL
  haveI : IsTopologicalRing ↥C.LL.1 := hO.2.2.2.1
  have hsub := _root_.GlobalTheory.subWp_sub i w hw C r ρ π hS
  have hF : Formalism.MainNotions.LocalSituation.fontCore (Br.PD D.loc D.nbr i w hw) := hA (D.nd.l i) (D.nbr i w hw).Kw
  let A : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := Fin D.R.r → ↥C.LL.1
      ρ := matRep (C.loc (WpO D.nd i ρ π))
      cont := fun x => by
        change Continuous fun g => (C.loc (WpO D.nd i ρ π) g).mulVec x
        exact hcW.matrix_mulVec continuous_const }
  have hcrW : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (WpO D.nd i ρ π))) :=
    GlobalTheory.CrysSub.isCrys_of_isSubOfSums (Br.PD D.loc D.nbr i w hw) hF hO A
      (fun _ : Unit => C.loc (rTwO D.nd i r π)) (fun _ => hc π) hsub (fun _ => hcr π)
  have dual := fun x => _root_.GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (C.loc (rTwO D.nd i r x)) hT (hc x) (hcr x)
  have dualW := _root_.GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (C.loc (WpO D.nd i ρ π)) hT hcW hcrW
  have uniq : ∀ τ g g', Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g →
      Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g' → g = g' := fun τ g g' hg hg' =>
    (_root_.GlobalTheory.HTW.Rec.existsUnique_reads D.host (D.nbr i w hw).Kw C.LL (Br.cEw D.nbr i w hw) κ τ).unique hg hg'
  refine ⟨fun x => ?_, fun x => ?_, fun x τ g hg => ?_, ?_, fun τ g hg u => ?_⟩
  · rw [h1 x]; exact (dual x).1
  · rw [h1 x]; exact (dual x).2
  · obtain ⟨g', hg', hj, -⟩ := hτ τ
    obtain rfl := uniq τ g g' hg hg'
    exact fun a ha => hj x a ha
  · rw [h2]; exact dualW.2
  · obtain ⟨g', hg', -, hm⟩ := hτ τ
    obtain rfl := uniq τ g g' hg hg'
    refine (hm u).trans ?_
    have hnd := _root_.GlobalTheory.HTW.Rec.twistedDualJumpsWithoutBlock_nodup_of_roomy L C₀ (liftIdx D i) g (pos ε g) hR
    split_ifs with hu
    · rw [Multiset.count_eq_one_of_mem hnd hu]; rfl
    · rw [Multiset.count_eq_zero_of_notMem hu]; rfl

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeJetsIntegralIffIntegralFrames
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames

open MvPowerSeries GlobalTheory.Proof.DirectionalDerivative

section Formal

variable {p : ℕ} [Fact p.Prime] {σ κ : Type}

theorem jetsIntegral_iff (G : MvPowerSeries κ ℂ_[p]) :
    JetsIntegral G ↔ GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral G := by
  unfold JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt Formalism.DworkPowerSeriesWeights.mfact
  simp [Finsupp.prod, Nat.cast_prod]

theorem jetAt_linAt_list [Fintype σ] [Fintype κ] (c : σ → κ → ℂ_[p]) (l : List κ) (G : MvPowerSeries σ ℂ_[p]) :
    GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt (linAt c G) (l.map fun x => Finsupp.single x 1).sum =
      constantCoeff (l.foldl (fun H x => dirDer (fun k => c k x) H) G) := by
  induction l generalizing G with
  | nil => simp [jetAt_zero, constantCoeff_linAt]
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, add_comm, jetAt_add_single, pderiv_linAt, ih, List.foldl_cons]

end Formal

theorem jetsInt_frames : ∀ (D : D7) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (Yl : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (JetsInt D lm Yl F ↔ ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, y j ∈ Yl) → JetsIntegral (atLin (fun k j => tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j) F)) ∧ (JetsInt D lm Yl F → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), (∀ x, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, y j ∈ Yl) ∧ ∀ k, M k x = ∑ j, r j * tauEmb D lm k.1 (y j k.2.1 k.2.2)) → JetsIntegral (atLin M (fun j => MvPowerSeries.X j) F)) := by
  intro D N N' p _ lm Yl F
  refine ⟨⟨fun hF n y hy => ?_, fun h n y hy => ?_⟩, fun hF ν _ M hM => ?_⟩
  · change JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F)
    rw [jetsIntegral_iff]
    exact jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG)
      (fun x G hG => keeps_vecY D lm Yl (hy x) G hG) F hF
  · have hJ := (jetsIntegral_iff _).1 (h n y hy)
    change GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F) at hJ
    have := hJ (((List.finRange n).reverse.map fun x => Finsupp.single x 1).sum)
    rw [jetAt_linAt_list, List.foldl_reverse] at this
    show ‖constantCoeff ((List.ofFn y).foldr (fun y' G => der D lm y' G) F)‖ ≤ 1
    rw [List.ofFn_eq_map, List.foldr_map]
    have hfun : (fun x G => der D lm (y x) G) = fun x G => dirDer (fun k => vecY D lm (y x) k) G := by
      funext x G
      exact der_eq D lm (y x) G
    rw [hfun]
    exact this
  · change JetsIntegral (linAt M F)
    rw [jetsIntegral_iff]
    refine jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG) (fun x => ?_) F hF
    obtain ⟨n, r, y, hr, hy, hMx⟩ := hM x
    have e : (fun k => M k x) = ∑ j, r j • vecY D lm (y j) := by
      funext k
      rw [hMx k, Finset.sum_apply]
      rfl
    rw [e]
    exact Finset.sum_induction _ (Keeps D lm Yl) (fun _ _ ha hb => keeps_add D lm Yl ha hb) (keeps_zero D lm Yl)
      fun j _ => keeps_smul D lm Yl (hr j) (keeps_vecY D lm Yl (hy j))

end GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDgenEqOne
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Classical

namespace GlobalTheory.EigenGenerator

theorem norm_dgen_eq_one : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : Qbar →+* ℂ_[p]), p = D.host.d → ∀ τ, ‖lamC lm (cD τ)‖ = 1 := by
  intro D cD hD p _ lm hp τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hh := D.host.hyp
  unfold Formalism.FrobeniusOrbits.HostHyp at hh
  have h2 : p ∉ D.host.small := hp ▸ UpperTheory.Small.d_not_mem D.host
  have hq : p ≠ D.host.q := by omega
  rw [← hsc]
  exact norm_generator_eq_one D p lm h2 hq M hM τ s hsp

end GlobalTheory.EigenGenerator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdAtServed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

theorem std_at_served : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → 2 * rG L.sc ≤ D.R.k → ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (D.gat u w hg).P.m (Y.Fl u w hg).t (Y.Fl u w hg).mm (Y.Fl u w hg).c (D.gat u w hg).P.r ((Y.Fl u w hg).TT v) ((Y.Fl u w hg).a v) ((Y.Fl u w hg).b v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) := by
  intro D u w hg L hT X Y hLT hk v
  obtain ⟨hmm, -, -, hr, -⟩ := hLT u w hg
  have hS := (D.gat u w hg).P.setting v
  have hgk := hT.gat_k u w hg
  have hrG : 1 ≤ rG L.sc := Nat.succ_le_succ (Nat.zero_le _)
  have hm2 := D.R.two_le_m
  refine ⟨hg.1, hg.2.1, hS.two_le, hS.even, ?_, ?_, ?_, (Y.Fl u w hg).base v, (D.gat u w hg).P.dom v, ?_, ?_⟩
  · rw [hr]; split_ifs <;> omega
  · rw [hr, hgk]; split_ifs <;> omega
  · rw [hmm]; omega
  · exact fun s => ⟨le_trans (le_max_left _ _) ((Y.Fl u w hg).w_ge v s),
      le_trans (le_max_right _ _) ((Y.Fl u w hg).w_ge v s)⟩
  · exact fun s l hl _ => (Y.Fl u w hg).w_mono v s l hl

end GlobalTheory.TwU
end

