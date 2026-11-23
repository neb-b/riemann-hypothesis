module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TypePrimesOfLevel
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordHypothesesEveryLatticeSurjection
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem exists_primitiveRoot_of_good {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (hG : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.2 hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) l
  have hmem : ζ ∈ Ks K 1 := by
    refine (le_sup_right : _ ≤ Ks K 1) (IntermediateField.subset_adjoin _ _ ?_)
    simpa using hζ.pow_eq_one
  have hLL : ζ ∈ LL.1 := hG.2.2.2 (Ks K 1).val ⟨ζ, hmem⟩
  refine ⟨⟨ζ, hLL⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ LL.1.val.toRingHom.injective

theorem setCS_of_wordsAT {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l}
    (hG : Good K 1 LL) (Wc : Wach P K LL) (hs : Wc.s = 1) (hK : K.1 ≤ MaximalUnramifiedExtension l) (h11 : 11 ≤ l)
    [NeZero (Module.finrank ℚ_[l] ↥(K0 K))] (Wd : NWord (Module.finrank ℚ_[l] ↥(K0 K))) (d : ℕ)
    (hA : WordsAT l Wd d) (T₁ T₂ : Lat K LL) (F : LatHom T₁.L T₂.L) (hF : F.Onto)
    (c₁ : IsCrys (P.PD K) T₁.ρ) (c₂ : IsCrys (P.PD K) T₂.ρ)
    (hj : ∀ a, TruncatedSeriesCountingBounds.JumpsAt Wc T₁ a (Wd.win a))
    (hlow : ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), TruncatedSeriesCountingBounds.lowCount Wc T₂ a Wd.η ≤ (Wd.m : ℤ)) :
    RamifiedCoefficientChains.SetCS Wc d T₁ T₂ F Wd.sz Wd.S Wd.η Wd.m := by
  classical
  obtain ⟨hev, hup, -, -, hbig⟩ := hA
  have hp : (P.PD K).p = l := P.PD_p K
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  obtain ⟨a₀, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (ZMod (Module.finrank ℚ_[l] ↥(K0 K))))
    Finset.univ_nonempty Wd.sz
  have hgr : IsGreatest (Set.range Wd.sz) (Finset.univ.sup Wd.sz) := by
    refine ⟨⟨a₀, hsup.symm⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Finset.le_sup (Finset.mem_univ a)
  have hbig' := hbig _ hgr
  refine ⟨⟨?_, hs, by omega⟩, by omega, hev, ?_, by rw [hp]; exact exists_primitiveRoot_of_good hG, ⟨c₁, c₂, hF⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩⟩
  · exact (goodO_finExt_integers l LL).1
  · intro a τ hτ u hu
    have hw := hj a τ hτ u hu
    have hua := hup a
    unfold NWord.win at hw
    unfold RamifiedCoefficientChains.JumpWinS
    by_cases hpar : (a.val + d) % 2 = 1
    · have h0 : ¬ (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = true := by simpa [hpar] using hua
      simp only [hu1, if_true, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_false, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
    · have h0 : (a.val + d) % 2 = 0 := by omega
      have hu1 : Wd.up a = false := by simpa [hpar] using hua
      simp only [hu1, Bool.false_eq_true, if_false, Set.mem_setOf_eq, abs_le] at hw
      simp only [h0, if_true, Set.mem_union, Set.mem_Icc]
      push_cast
      omega
  · intro a τ hτ
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    letI ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Fintype.ofFinite _
    have h := hlow ft a
    unfold TruncatedSeriesCountingBounds.lowCount at h
    have hfil : (Finset.univ.filter (fun τ' => Formalism.MainNotions.LiftingTheory.Over Wc τ' a)) = {τ} := by
      ext τ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' => (existsUnique_over P K LL Wc hK a).unique h' hτ, fun h' => h' ▸ hτ⟩
    rw [hfil, Finset.sum_singleton] at h
    exact h
  · intro a
    have h := (hbig' a).2
    rw [hp]
    unfold RamifiedCoefficientChains.aR RamifiedCoefficientChains.lam RamifiedCoefficientChains.hpar
    push_cast
    exact h
  · intro a
    have h := (hbig' a).1
    unfold RamifiedCoefficientChains.hpar
    push_cast
    exact h

theorem settingC_of_wordsAT : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)) (d : ℕ), 11 ≤ D.nd.l i → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → WordsAT (D.nd.l i) Wd d → RecS.AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d := by
  intro D L HW i r ρ π w hw Cx hG Wd d h11 hB hA nz T₁ T₂ F h₁ h₂ hF
  have hT1 := hB.t1 T₁ h₁
  have hT2 := hB.t2 T₂ h₂
  exact setCS_of_wordsAT hG (WW HW i w hw Cx hG) ((HW (D.nd.l i)).W_s _ 1 _ hG) hB.unram h11 Wd d hA
    T₁ T₂ F hF hT1.1 hT2.1 hT1.2.1 hT2.2

end GlobalTheory.HTW.RecS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainDataGuarded
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

noncomputable section

namespace GlobalTheory.LastSteps

def ChainDataGuarded : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ), Pr.Ok → cst.Ok → R.m = m2 + 2 →
    ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs →
      (∀ hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1), SplitAt Ch sel mu cst m2 P hal) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → DualFn P.1 (fhat sel mu cst P f)) ∧
      (∀ f : Sp X.E (R.N (m2 + 1)) → X.K, ColFn P.1 f → FnMod P.1 (topDatum Ch sel mu cst m2 P f)) ∧
      (∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (al : L.β m2),
        L.h m2 al P ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) m2 P.1) →
        ∀ (u : Pr.Word) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p₀.deco.1.N p.deco.1.N (facPen Ch sel mu cst L m2 al p₀ p Y P)) ∧
      (∀ (u : Pr.Word), (∀ w : rowSG Pr sel mu, Pr.piT u ∉ w.1.asIdeal) →
        ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (d : RowPt Pr R sel mu),
        ∀ Y ∈ ybSet sel mu cst p.deco.1.N,
          FnModAt P.1 p.deco.1.N (tilQ sel mu u d).1.N (facTop Ch sel mu cst m2 p Y d P))

end GlobalTheory.LastSteps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationDualWeightInvolutiveStatement
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ ε : ℤˣ, ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∀ g : MP R (m + 1), CofRel R m ν f g → CofRel R m (nuDual ν) g ((ε : ℤ) • f) := by
  first | exact @GlobalTheory.ValCmp.Invol.cofRel_invol | exact GlobalTheory.ValCmp.Invol.cofRel_invol | (intros; apply GlobalTheory.ValCmp.Invol.cofRel_invol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CofactorTwistRelationRowDivSwapStatement
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofactorTwistRelation_rowDiv_swap : ∀ (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ) (f g : MP R (m + 1)), a ≠ b → CofRel R m ν f g → CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  first | exact @GlobalTheory.ValCmp.cofRel_rowDiv | exact GlobalTheory.ValCmp.cofRel_rowDiv | (intros; apply GlobalTheory.ValCmp.cofRel_rowDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnStabilizerTrivialLocal
section
noncomputable section

namespace GlobalTheory.Proof.ColumnStabilizerTrivialLocal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n n' : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem typePrimesLarge_iff (D : D7) :
    UnipotentLevelStabilisers.TypePrimesLarge D ↔ ∀ i, 2 * D.R.f * D.R.k < D.host.g i - 1 :=
  forall_congr' fun i => by omega

theorem gBig_of_large (h : UnipotentLevelStabilisers.TypePrimesLarge D) : Formalism.MainNotions.StandardLattice.GBig D :=
  ⟨0, (typePrimesLarge_iff D).mp h 0⟩

variable {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)

end GlobalTheory.Proof.ColumnStabilizerTrivialLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
section
noncomputable section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
open Filter Topology

namespace GlobalTheory.HeckeSplit

variable {L : Type} [Field L] [NumberField L]

theorem eventually_unrAt (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) :
    ∀ᶠ v in Filter.cofinite, UnrAt χ v := by
  have h : ∀ v : HeightOneSpectrum (𝓞 L), ∃ x : (v.adicCompletion L)ˣ,
      Valued.v (x : v.adicCompletion L) = 1 ∧
      (‖((χ (localIdele L v x) : ℂˣ) : ℂ) - 1‖ < 1 / 2 → UnrAt χ v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
    refine (hc _ ?_).1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  choose x hx hx' using h
  have hc : Continuous fun a : Ideles L => ‖((χ a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp hχ).sub continuous_const).norm
  have h0 : Tendsto (fun v => localIdele L v (x v)) cofinite (𝓝 1) :=
    GlobalTheory.Mem.UnrAe.tendsto_localIdele x hx
  have h1 := (hc.tendsto 1).comp h0
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact h2.mono fun v hv => hx' v hv

theorem exists_level (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 L)) :
    ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ,
      Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1 := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (hχ.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele v))).sub
      continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat + 1, fun x hx1 => ?_⟩
  have hlt : Valued.v ((x : v.adicCompletion L) - 1) < 1 := by
    refine hx1.trans_lt ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := by
    have := Valuation.map_one_add_of_lt _ hlt
    simpa using this
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)

def truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) : Ideles L :=
  infIdele L (infPart L x) * ∏ v ∈ T, localIdele L v (finPart L v x)

theorem truncIdele_inv (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    truncIdele x⁻¹ T = (truncIdele x T)⁻¹ := by
  simp only [truncIdele, map_inv, Finset.prod_inv_distrib, ← mul_inv]

open Classical in
theorem finPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (v : HeightOneSpectrum (𝓞 L)) :
    finPart L v (truncIdele x T) = if v ∈ T then finPart L v x else 1 := by
  rw [truncIdele, map_mul, finPart_infIdele, one_mul, map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem v h fun w _ hw => finPart_localIdele_ne L hw.symm _,
      finPart_localIdele]
  · exact Finset.prod_eq_one fun w hw => finPart_localIdele_ne L (v := w) (w := v) (fun e => h (by rw [e]; exact hw)) _

theorem infPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    infPart L (truncIdele x T) = infPart L x := by
  rw [truncIdele, map_mul, infPart_infIdele, map_prod,
    Finset.prod_eq_one fun v _ => infPart_localIdele L v _, mul_one]

theorem coe_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L) =
      ((x : AdeleRing (𝓞 L) L).1, GlobalTheory.HeckeProduct.cut (x : AdeleRing (𝓞 L) L).2 T) := by
  classical
  refine Prod.ext ?_ (Subtype.ext (funext fun v => ?_))
  · exact congrArg (fun u : (InfiniteAdeleRing L)ˣ => (u : InfiniteAdeleRing L)) (infPart_truncIdele x T)
  · have h := congrArg (fun u : (v.adicCompletion L)ˣ => (u : v.adicCompletion L))
      (finPart_truncIdele x T v)
    refine h.trans ?_
    by_cases hv : v ∈ T
    · simp only [hv, if_true]; exact (if_pos hv).symm
    · simp only [hv, if_false]; exact (if_neg hv).symm

theorem tendsto_truncIdele (x : Ideles L) :
    Tendsto (truncIdele x) atTop (𝓝 x) := by
  have h : ∀ x : Ideles L, Tendsto (fun T => ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L))
      atTop (𝓝 (x : AdeleRing (𝓞 L) L)) := fun x => by
    simp only [coe_truncIdele]
    exact tendsto_const_nhds.prodMk_nhds (GlobalTheory.HeckeProduct.tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
  have h2 := h x⁻¹
  simp only [truncIdele_inv] at h2
  exact h2

theorem char_eq_prod_local (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (x : Ideles L)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) :
    χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) := by
  classical
  have h1 := (hχ.tendsto x).comp (tendsto_truncIdele x)
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop S] with T hT
  change _ = χ (truncIdele x T)
  rw [truncIdele, map_mul, map_prod]
  congr 1
  exact Finset.prod_subset hT fun v _ hv => hS v hv

theorem continuous_char_factor : ∀ (L : Type) [Field L] [NumberField L] (χ : Ideles L →* ℂˣ), Continuous χ → (∀ᶠ v in Filter.cofinite, UnrAt χ v) ∧ (∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ, Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1) ∧ ∀ (x : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) → χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) :=
  fun _ _ _ χ hχ => ⟨eventually_unrAt χ hχ, exists_level χ hχ, fun x S hS => char_eq_prod_local χ hχ x S hS⟩

end GlobalTheory.HeckeSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeight
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem sum_mul_sub_succ : ∀ (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) + m * ν (Fin.last m) + ν 0 = ∑ i, ν i := by
  intro m
  induction m with
  | zero => intro ν _; simp
  | succ m ih =>
    intro ν hν
    have h := ih (fun i => ν i.castSucc) (fun a b hab => hν (by simpa using hab))
    rw [Fin.sum_univ_castSucc (f := ν), ← h, Fin.sum_univ_castSucc]
    have hle : ν (Fin.last (m + 1)) ≤ ν (Fin.last m).castSucc := hν (Fin.le_last _)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    simp only [Fin.val_castSucc, Fin.val_last, Fin.succ_last, Fin.castSucc_zero, Fin.succ_castSucc, hd,
      Nat.add_sub_cancel_left]
    ring

noncomputable def revInitMinor (R : Type) [CommRing R] (n k : ℕ) : MP R n :=
  if h : k ≤ n then initMinor R (fun a : Fin k => Fin.rev (Fin.castLE h a)) h else 1

def antiDiagGL (R : Type) [CommRing R] (n : ℕ) : GL (Fin n) R where
  val := Matrix.of fun a b => if b = a.rev then 1 else 0
  inv := Matrix.of fun a b => if b = a.rev then 1 else 0
  val_inv := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
    simp [Matrix.one_apply, eq_comm]
  inv_val := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
    simp [Matrix.one_apply, eq_comm]

theorem dwAct_antiDiag_X (R : Type) [CommRing R] (n : ℕ) (a s : Fin n) :
    Formalism.UG.dwAct R n n (antiDiagGL R n) (X (a, s)) = X (a.rev, s) := by
  have : (((antiDiagGL R n)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      Matrix.of fun a b => if b = a.rev then 1 else 0 := rfl
  rw [Formalism.UG.dwAct, this, rowAct, aeval_X, Finset.sum_eq_single a.rev (fun j _ hj => by simp [hj]) (by simp)]
  simp

theorem dwAct_antiDiag_lpMinor (R : Type) [CommRing R] (n k : ℕ) (h h' : k ≤ n) :
    Formalism.UG.dwAct R n n (antiDiagGL R n) (lpMinor R k h h') = revInitMinor R n k := by
  rw [revInitMinor, dite_eq_left h, lpMinor, initMinor, AlgHom.map_det]
  congr 1
  ext a b : 2
  simp [dwAct_antiDiag_X]

theorem cofAct_lpMinor (R : Type) [CommRing R] [IsDomain R] (n k : ℕ) (h h' : k + 1 ≤ n) : ∃ ε : ℤˣ,
    cofAct R n (lpMinor R (k + 1) h h') = (ε : ℤ) • ((genM R n).det ^ k * revInitMinor R n (n - (k + 1))) := by
  obtain ⟨ε, hε⟩ := cofAct_initMinor R n (k + 1) h (by omega) 1
  refine ⟨ε, ?_⟩
  rw [revInitMinor, dite_eq_left (Nat.sub_le _ _)]
  exact hε

theorem exists_cofRel_hw : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (hw R le_rfl ν) g := by
  intro R _ _ m ν hν h0
  have hmem : hw R le_rfl (nuDual ν) ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν) :=
    Submodule.subset_span ⟨[], rfl⟩
  have hJ := Formalism.UG.Final.WeylGLStable R (m + 1) (m + 1) le_rfl (nuDual ν) (antiDiagGL R (m + 1)) _ hmem
  have hnext : ∀ (μ : Fin (m + 1) → ℕ) (s : Fin m), nuNext μ s.castSucc = μ s.succ := by
    intro μ s
    have : s.castSucc.val + 1 < m + 1 := by simp
    rw [nuNext, dite_eq_left this]
    rfl
  have e1 : Formalism.UG.dwAct R (m + 1) (m + 1) (antiDiagGL R (m + 1)) (hw R le_rfl (nuDual ν)) =
      ∏ s : Fin m, revInitMinor R (m + 1) (m + 1 - (s.val + 1)) ^ (ν s.castSucc - ν s.succ) := by
    rw [hw, map_prod, Fin.prod_univ_castSucc]
    simp only [map_pow, dwAct_antiDiag_lpMinor, hnext]
    have : nuDual ν (Fin.last m) = 0 := by simp [nuDual]
    rw [this, Nat.zero_sub, pow_zero, mul_one, ← Equiv.prod_comp Fin.revPerm]
    refine Finset.prod_congr rfl fun s _ => ?_
    have h1 : ν s.castSucc ≤ ν 0 := hν (Fin.zero_le _)
    have h2 : ν s.succ ≤ ν s.castSucc := hν (Fin.castSucc_lt_succ).le
    have hs := s.isLt
    congr 1
    · congr 1
      simp [Fin.val_rev]
      omega
    · simp only [nuDual, Fin.revPerm_apply, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]
      omega
  choose ε hε using fun s : Fin m =>
    cofAct_lpMinor R (m + 1) s.val (by have := s.isLt; omega) (by have := s.isLt; omega)
  refine ⟨(∏ s : Fin m, (ε s : ℤ) ^ (ν s.castSucc - ν s.succ)) • _, Submodule.smul_of_tower_mem _ _ hJ, ?_⟩
  have hsum : ∑ i, ν i - ν 0 = ∑ s : Fin m, s.val * (ν s.castSucc - ν s.succ) := by
    have := sum_mul_sub_succ m ν hν
    rw [h0] at this
    omega
  rw [CofRel, e1, hsum, hw, map_prod, Fin.prod_univ_castSucc, h0, Nat.zero_sub, pow_zero, map_one, mul_one]
  simp only [map_pow, hnext, Fin.val_castSucc, hε, zsmul_eq_mul, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

end GlobalTheory.ValCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) := by
  first | exact @GlobalTheory.HTW.Rec.goodO_finExt_integers | exact GlobalTheory.HTW.Rec.goodO_finExt_integers | (intros; apply GlobalTheory.HTW.Rec.goodO_finExt_integers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimesStatement
section
open NumberField
open GlobalTheory.UPel.HT.Gen
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  first | (exact @GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (exact GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (intros; apply GlobalTheory.UPel.HT.Gen.SplitAE.splitAE  <;> assumption)
end

