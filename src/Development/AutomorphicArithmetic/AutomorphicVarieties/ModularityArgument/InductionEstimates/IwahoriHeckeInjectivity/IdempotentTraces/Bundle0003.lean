module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.HeckeEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ZSimple
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.IrreducibleCuspidalWeightComponent
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.irreducible_cuspidal_weight_component {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K (2 + 2)))
    [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (hP : Pair μ₂ τ₁ τ₂)
    {κ e κ₂ p₁ p₂ k₀} (hA : ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀) {r : ℕ} (w : Fin r → Pl K) (hw : Function.Injective w)
    (U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v)) (hU : Lev U) (D : TypeDat K (2 + 2)) (hD : IsTy D κ e (levOn (im w) U))
    (d : ℕ) (A : Line μ τ₁ τ₂ D d) (P : Submodule ℂ (Eu d))
    (hst : ∀ v ∈ im w, ∀ (g : Gw (2 + 2) v) M, HeckeAt A (levOn (im w) U) (AdelicGLn.localEmbedding v g) M → ∀ x ∈ P, M x ∈ P) :
    P = ⊥ ∨ P = ⊤ := by
  obtain ⟨⟨ι, hι⟩, hemb⟩ := embEx (2 + 2) w hw
  obtain ⟨-, hc1, hc2, -, -, hlev⟩ := hemb ι hι
  have hcf1 : ∀ v : Pl K, GM.cf v (1 : FA K (2 + 2)) = 1 := by
    intro v
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      have h := hc1 1 i
      rwa [map_one] at h
    · have h := hc2 1 v hv
      rwa [map_one] at h
  have hinU : ∀ u ∈ Subgroup.pi Set.univ (fun i => U (w i)), ι u ∈ levOn (im w) U := fun u hu =>
    (hlev U _).2 ⟨u, 1, (mul_one _).symm, fun i => hu i trivial, fun i => hcf1 _, fun v => by rw [hcf1]; exact one_mem _⟩
  obtain ⟨-, hfl, hinj, -⟩ := secTr μ₂ τ₁ τ₂ κ e hA.idem
  obtain ⟨hZ, hZ'⟩ := zMem μ₂ τ₁ τ₂ κ e hA.idem
  have hle := (levLaws (2 + 2) (im w)).1
  have hsimple := zSimple μ₂ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hP hA w ι hw hι
  have hex := (heckeEx K μ μ₂ τ₁ τ₂ hP κ e hA.idem (im w) U hU D hD d A).1
  let Φ : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ) :=
    { toFun := fun v => flat 0 (A.sec v)
      map_add' := fun a b => by funext x; simp [flat, mul_add]
      map_smul' := fun c a => by funext x; simp [flat, mul_left_comm] }
  have hΦ : ∀ v, Φ v = flat 0 (A.sec v) := fun _ => rfl
  have hΦinj : Function.Injective Φ := fun a b h => A.inj (hinj _ _ h)
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ FixA κ e (A.sec v) ∧ FixF (levOn (im w) U) (A.sec v) := fun v => by
    obtain ⟨h1, h2⟩ := (A.onto _).1 (LinearMap.mem_range_self A.sec v)
    exact ⟨h1, (hD.fix _ h1.cont).1 h2⟩
  have hfixΦ : ∀ v, FixF (levOn (im w) U) (Φ v) := fun v =>
    ((hfl _ (hsec v).1.cont).2 _ (hle U hU).2).2 (hsec v).2.2
  have hmem : ∀ v, Φ v ∈ Zs τ₁ τ₂ κ e (im w) := fun v =>
    (hZ _ _).2 ⟨_, (hsec v).1, (hsec v).2.1, ⟨U, hU, (hsec v).2.2⟩, rfl⟩
  have hCO : ∀ i, CO (U (w i)) := fun i => (hU (w i)).1
  have hCOpi : CO (Subgroup.pi Set.univ fun i => U (w i)) := by
    refine ⟨?_, ?_⟩
    · rw [Subgroup.coe_pi]; exact isCompact_univ_pi fun i => (hCO i).1
    · rw [Subgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => (hCO i).2
  have hrS : ∀ g (φ : G1 K (2 + 2) → ℂ) x, rS ι g φ x = φ (x * fin1 (ι g)) := fun _ _ _ => rfl
  have hQfix : ∀ φ ∈ P.map Φ, ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u φ = φ := by
    rintro _ ⟨v, -, rfl⟩ u hu
    funext x
    rw [hrS]
    exact hfixΦ v _ (hinU u hu) x
  have hQhop : ∀ g, ∀ φ ∈ P.map Φ, hopR (rS ι) (Subgroup.pi Set.univ fun i => U (w i)) g φ ∈ P.map Φ := by
    refine hopProd (rS ι) (fun i => U (w i)) (P.map Φ) hCO hQfix ?_
    rintro i g _ ⟨v, hv, rfl⟩
    obtain ⟨M, hM, -⟩ := hex (AdelicGLn.localEmbedding (w i) g)
    refine ⟨M v, hst (w i) (Finset.mem_image_of_mem _ (Finset.mem_univ i)) g M hM v hv, ?_⟩
    rw [← hopEmb (2 + 2) w ι hw hι U hU _ (hfixΦ v), hι i g]
    exact hM v
  rcases heckeSimple (rS ι) (Zs τ₁ τ₂ κ e (im w)) _ hCOpi hsimple (fun φ hφ => (hZ' w ι hw hι φ hφ).1) (P.map Φ)
    (by rintro _ ⟨v, -, rfl⟩; exact hmem v) hQfix hQhop with h | h
  · left
    refine (Submodule.eq_bot_iff _).2 fun v hv => hΦinj ?_
    rw [map_zero]
    exact (Submodule.eq_bot_iff _).1 h _ ⟨v, hv, rfl⟩
  · right
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : ∀ u ∈ Subgroup.pi Set.univ fun i => U (w i), rS ι u (Φ v) = Φ v := by
      intro u hu
      funext x
      rw [hrS]
      exact hfixΦ v _ (hinU u hu) x
    obtain ⟨v', hv', he⟩ := h _ (hmem v) hv
    rwa [← hΦinj he]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.irrW :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.IrrW := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP κ e κ₂ p₁ p₂ k₀ hA S U hU D hD d A P hst
  obtain ⟨r, w, hw, rfl⟩ : ∃ (r : ℕ) (w : Fin r → Pl K), Function.Injective w ∧ S = im w := by
    refine ⟨S.card, fun i => (S.equivFin.symm i : Pl K), fun a b h => S.equivFin.symm.injective (Subtype.ext h), ?_⟩
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun hv => ⟨S.equivFin ⟨v, hv⟩, by simp⟩, fun ⟨i, hi⟩ => hi ▸ (S.equivFin.symm i).2⟩
  exact irreducible_cuspidal_weight_component μ μ₂ τ₁ τ₂ hP hA w hw U hU D hD d A P hst
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.NormOfSplit
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

private theorem norm_of_split {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) (h : GM.Split M (w.under (𝓞 K))) :
    Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
  haveI hl : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  have hs : Function.Surjective (completionMap (w.under (𝓞 K)) w) := h ⟨w, hl⟩
  have h1 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    rw [← finrank_eq_ramificationIdx_mul_inertiaDeg M (w.under (𝓞 K)) w]
    have hb : Function.Bijective (Algebra.linearMap ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion M)) :=
      ⟨(completionMap (w.under (𝓞 K)) w).injective, hs⟩
    rw [← (LinearEquiv.ofBijective _ hb).finrank_eq, Module.finrank_self]
  have nv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
      Formalism.ConjugateSelfDual.normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [nv, nv]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, Nat.eq_one_of_mul_eq_one_left h1, pow_one]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.sysOf :
    SysOf := by
  intro K M _ _ _ _ _ _ _ _ h2 π π' P hsw hW
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  obtain ⟨χ, hχ, hP⟩ := R.twoParts_holds K M hp (2 * 2) P (Fin 2) (fun _ => 2) ![π, π'] (by norm_num)
    (fun _ => by norm_num) (by simp) hW
  obtain ⟨η, hη⟩ := R.classChar2 K M hp
  obtain ⟨j, hj0, hj, rfl⟩ := (R.normCharPow_holds K M hp η hη).1 χ hχ
  obtain rfl : j = 1 := by omega
  rw [pow_one] at hP
  filter_upwards [hW, hη.2, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (R.decomp K M hp)] with w hw hg hd
  have hq : 1 < Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
    have nv : Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) =
        Ideal.absNorm (w.under (𝓞 K)).asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    rw [nv]
    exact NumberField.HeightOneSpectrum.one_lt_absNorm _
  refine ⟨fun w' hne hu => ?_, fun hn => ?_⟩
  · have hn : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := by
      rcases hd with hd | hd
      · exact hd.2 w rfl
      · exact absurd (congrArg Subtype.val ((Nat.card_eq_one_iff_unique.1 hd.1).1.elim ⟨w', hu⟩ ⟨w, rfl⟩)) hne
    obtain ⟨A, hA, B, hB, e⟩ := hw 1 (by rw [pow_one]; exact hn)
    have e' : A = B 0 + B 1 := by simpa [Fin.sum_univ_two] using e
    exact ⟨B 0, B 1, hB 0, (hsw w w' hu.symm (Or.inl hne.symm) _).1 (hB 1), e' ▸ hA⟩
  · have hne : Formalism.ConjugateSelfDual.normV w ≠ Formalism.ConjugateSelfDual.normV (w.under (𝓞 K)) := fun e => by
      have : (2 : ℕ) = 1 := Nat.pow_right_injective hq ((hn.symm.trans e).trans (pow_one _).symm)
      omega
    have hv : η.val (w.under (𝓞 K)) = -1 := by
      have h := hg.2.resolve_left hne
      rw [h2] at h
      exact Units.ext (IsPrimitiveRoot.coe_units_iff.2 h).eq_neg_one_of_two_right
    obtain ⟨A, hA, B, hB, e⟩ := hw 2 hn
    have hB0 : π.HasSat w (B 0) := hB 0
    have hB1 : π.HasSat w (B 1) := (hsw w w rfl (Or.inr fun h => hne (norm_of_split w h)) _).1 (hB 1)
    have e1 : B 1 = B 0 := hB1.unique hB0
    have hT := hA.twist hg.1
    rw [hP, hv] at hT
    have hs : A.map (fun x => -x) = A := by simpa using hT.unique hA
    obtain ⟨B', h3, h4⟩ := signMs A (B 0) hA.card hB0.card hs (by rw [e, Fin.sum_univ_two, e1])
    exact ⟨A, B', h3 ▸ hB0, h4, hA⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.IdempotentTraces.NotConjIso
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open GlobalTheory.CuspRep UpperTheory.V.Published
open scoped ComplexConjugate Classical

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

section Pow

open Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.ConvolutionTheory.T

private theorem pow_loc {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]
  exact h _

private theorem pow_val {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = (normV v : ℂ) ^ (-s) := by
  refine ⟨fun x hx => Units.ext ?_, ?_⟩
  · have hx' : Valued.v (x : v.adicCompletion K) = 1 := hx
    rw [pow_loc h, FinitePlace.norm_def, hx']
    simp
  · have hx' : Valued.v ((atFin v (unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
      unif_spec v
    refine (pow_loc h v (atFin v (unif v))).trans ?_
    rw [FinitePlace.norm_def, hx', WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    have e' : normV v = Ideal.absNorm v.asIdeal := by
      rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [WithZero.log_exp, e', zpow_neg_one, NNReal.coe_inv, Complex.ofReal_inv, NNReal.coe_natCast, Complex.ofReal_natCast,
      Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

private theorem exists_place (E : Type) [Field E] [NumberField E] : Nonempty (HeightOneSpectrum (𝓞 E)) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩⟩

private theorem absC_pow (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (s : ℂ) : IsPow (GlobalTheory.CuspRep.Model.absC E s) s := by
  obtain ⟨b, hb⟩ := GlobalTheory.AbsTwist.exists_eq_mul_log_module (F := E) (GlobalTheory.Mem.Chr.CharModel.logNorm E)
    (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E) (GlobalTheory.Mem.Chr.CharModel.logNorm_mul E)
    (GlobalTheory.Mem.Chr.CharModel.logNorm_principal E)
  have hgen : ∀ z : ℂ, IsPow (GlobalTheory.CuspRep.Model.absC E z) (z * b) := fun z y => by
    change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E y) = _
    have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E y).2
    rw [hb y, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]
    congr 1
    push_cast
    ring
  have hb1 : b = 1 := by
    obtain ⟨w⟩ := exists_place E
    have h1 := (pow_val (hgen 1) w).2
    have e' : normV w = Ideal.absNorm w.asIdeal := by
      rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [PositivityTheory.Rg.Rs.StrStepB.absC_val, e'] at h1
    have h0 : 1 < (Ideal.absNorm w.asIdeal : ℕ) := NumberField.HeightOneSpectrum.one_lt_absNorm w
    have h2 := congrArg norm h1
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_natCast_cpow_of_pos (by omega),
      show (-(1 : ℂ)).re = -1 by simp, show (-(1 * (b : ℂ))).re = -b by simp] at h2
    have h3 := congrArg Real.log h2
    rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < (Ideal.absNorm w.asIdeal : ℕ))),
      Real.log_rpow (by exact_mod_cast (by omega : 0 < (Ideal.absNorm w.asIdeal : ℕ)))] at h3
    have h4 : Real.log (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast h0)).ne'
    linarith [mul_right_cancel₀ h4 h3]
  simpa [hb1] using hgen s

private theorem pow_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {χ : HChar E} {s : ℂ} (h : IsPow χ s) :
    χ = GlobalTheory.CuspRep.Model.absC E s :=
  Subtype.ext (MonoidHom.ext fun x => Units.ext ((h x).trans (absC_pow E s x).symm))

private theorem pow_expo {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {χ : HChar E} {s : ℂ} (h : IsPow χ s)
    (τ : E →+* ℂ) : expo χ τ = s := by
  rw [pow_eq h, GlobalTheory.CuspRep.Model.expo_absC]

end Pow

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Formalism.L2.Host Formalism.ConjugateSelfDual

private theorem norm_deg (w : HeightOneSpectrum (𝓞 E)) :
    normV w = normV (w.under (𝓞 F)) ^ w.asIdeal.inertiaDeg (𝓞 F) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 F)).isMaximal
  simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    (Ideal.absNorm_pow_inertiaDeg (w.under (𝓞 F)).asIdeal w.asIdeal).symm

private theorem deg_sum (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F))
    (T : Finset (v.asIdeal.primesOver (𝓞 E))) : ∑ q ∈ T, q.1.inertiaDeg (𝓞 F) ≤ 2 := by
  have := v.isMaximal
  have : Fintype (v.asIdeal.primesOver (𝓞 E)) := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).fintype
  rw [← h2, IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E,
    ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine (Finset.sum_le_sum_of_subset T.subset_univ).trans (Finset.sum_le_sum fun q _ => ?_)
  have := q.2.1
  exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos _ _)

private theorem norm_split (h2 : Module.finrank F E = 2) {w w' : HeightOneSpectrum (𝓞 E)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 F) = w.under (𝓞 F)) : normV w = normV (w.under (𝓞 F)) := by
  classical
  have := w.isPrime
  have := w'.isPrime
  have hu' : (w.under (𝓞 F)).asIdeal = w'.asIdeal.under (𝓞 F) := (congrArg HeightOneSpectrum.asIdeal hu).symm
  have hs := deg_sum h2 (w.under (𝓞 F)) {⟨w'.asIdeal, w'.isPrime, ⟨hu'⟩⟩, ⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩}
  rw [Finset.sum_pair fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h))] at hs
  have h3 := w.asIdeal.inertiaDeg_pos (𝓞 F)
  have h4 := w'.asIdeal.inertiaDeg_pos (𝓞 F)
  rw [norm_deg (F := F) w, show w.asIdeal.inertiaDeg (𝓞 F) = 1 by dsimp only at hs; omega, pow_one]

private theorem gal_two (h2 : Module.finrank F E = 2) : ∃ σ : E ≃ₐ[F] E, σ ≠ 1 ∧ ∀ τ : E ≃ₐ[F] E, τ = 1 ∨ τ = σ := by
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, hy, hy'⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  exact ⟨y, hy, fun τ => (em (τ = 1)).imp_right (hy' τ)⟩

end Places

section Conj

open Formalism.L2.Host UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Bc

private theorem infOf_ne {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) : infOf m ≠ infOf m' := by
  intro e
  have h1 : (((2 : ℕ) : ℂ) - 1) / 2 + (m 0 : ℂ) ∈ infOf m := Multiset.mem_map.2 ⟨0, Finset.mem_univ_val _, rfl⟩
  rw [e] at h1
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 h1
  have h2 : m' i = m 0 := Int.cast_injective (add_left_cancel hi)
  fin_cases i
  · exact absurd (@h 2 0 h2) (by decide)
  · exact absurd (@h 3 0 h2) (by decide)

open UpperTheory.CBC UpperTheory.CBC.SConjSpaceCAux in
private theorem not_conjIso {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    (h2 : Module.finrank K M = 2) (π : CuspSub M 2) (hm : MixWtC K π) (σ : M ≃ₐ[K] M) (h1σ : σ ≠ 1) :
    ¬ (Cusp.cx π).ConjIso σ.toRingEquiv := by
  intro h
  have : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  obtain ⟨m, m', τ, τ', hne, h1, h2', k1, k2, hinj⟩ := hm φ
  obtain ⟨σ₀, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := K) τ τ' (h1.trans h2'.symm)
  obtain ⟨y, -, hy⟩ := gal_two (F := K) (E := M) h2
  have h0 : σ₀ ≠ 1 := by
    rintro rfl
    exact hne (RingHom.ext fun x => (RingHom.congr_fun hσ x))
  obtain rfl : σ₀ = σ := ((hy σ₀).resolve_left h0).trans ((hy σ).resolve_left h1σ).symm
  obtain ⟨s, hs⟩ := SGalAdEx_holds M σ₀.toRingEquiv
  obtain ⟨P', hsp, hiso⟩ := h s hs
  obtain ⟨d, hd, hd'⟩ := exists_GD _ s hs
  cases P' with
  | re π' => exact hiso.elim
  | cx π' =>
    have e : τ.comp (d.σ.symm : M →+* M) = τ' := by
      rw [hd']
      exact hσ
    have k3 : π'.HasInfChar τ (infOf m') := by
      refine ⟨k2.1, fun u x hx => ?_⟩
      have hx' : x.1 ∈ (Cusp.cx π').space := ⟨x, hx, rfl⟩
      rw [hsp] at hx'
      obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := hx'
      obtain rfl : x = pull d 2 y := Subtype.ext (by rw [← hxy, ← hd]; rfl)
      rw [cap_pull, e, k2.2 u y hy, map_smul]
    exact infOf_ne hinj (k1.unique (CuspSub.Iso.hasInfChar hiso k3))

end Conj

section Main

open Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.ConvolutionTheory.T

private theorem satTw {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {π : CuspSub E a}
    {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : (CG.mk π).HasSat w B) {χ : HChar E}
    (hu : χ.UnrAt w) : (CG.mk (π.twist χ)).HasSat w (B.map (· * χ.val w)) :=
  GlobalTheory.SphGal.hasSatGL_twist E a π χ w B hu h

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indCs :
    IndNorm → IndCs := by
  intro hN K M _ _ hK _ _ hM _ h2 π hm hS
  have hq : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  have hn : 1 ≤ (2 : ℕ) := by decide
  let μ : Measure (normOneGL (K := M) (n := 2)) := Measure.haar
  obtain ⟨χ, ⟨s, hχ⟩, V, hV⟩ :
      ∃ χ : HChar M, (∃ s : ℂ, IsPow χ s) ∧ ∃ V, Dp.Carries μ (π.twist χ) V :=
    Dp.exTwist M 2 μ π hn
  obtain ⟨hex, hpw⟩ := powTwist K M
  obtain ⟨χ₀, hχ₀⟩ := (hex s).1
  obtain ⟨hi₀, hi, htw⟩ := hpw s χ₀ χ hχ₀ hχ
  have hback := (htw 2 hn).2.1 π
  have hCj := ((hpw (-s) χ₀⁻¹ χ⁻¹ hi₀ hi).2.2 2 hn).2.2.2.1
  have hnorm : GlobalTheory.DiscSpec.IsNormalised (π.twist χ) :=
    (Dp.normIff M 2 _).2 ((Dp.exSummand M 2 μ _ V).1 hV).1
  have hnc : ∀ σ : M ≃ₐ[K] M, σ ≠ 1 → ¬ (UpperTheory.CBC.Cusp.cx (π.twist χ)).ConjIso σ.toRingEquiv := fun σ h1 hc =>
    not_conjIso h2 π hm σ h1 (by simpa only [hback] using hCj _ _ hc)
  have hsb : SplitBad K (π.twist χ) := fun v hv => ⟨(hS v hv).1, fun w hw =>
    let ⟨_, hB⟩ := (hS v hv).2 w hw
    ⟨_, satTw hB (pow_val hχ w).1⟩⟩
  obtain ⟨P, hP, hI⟩ := hN K M h2 (π.twist χ) hnorm hnc hsb
  have hun : ∀ {w : HeightOneSpectrum (𝓞 M)} {B : Multiset ℂˣ}, (CG.mk (π.twist χ)).HasSat w B →
      (CG.mk π).HasSat w (B.map (· * χ⁻¹.val w)) := fun {w B} h => by
    have h1 := satTw h (pow_val hi w).1
    rwa [hback] at h1
  have hv : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f →
      χ⁻¹.val w = χ₀⁻¹.val (w.under (𝓞 K)) ^ f := fun w f hf => by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, (pow_val hi _).2, (pow_val hi₀ _).2, hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
      Complex.natCast_cpow_natCast_mul]
  refine ⟨P.twist χ₀⁻¹, hP.mono fun w hw => ⟨fun w' hne e => ?_, fun hq2 => ?_⟩, fun τ τ' m m' hne hc k1 k2 => ?_⟩
  · obtain ⟨B, B', k1, k2, k3⟩ := hw.1 w' hne e
    have e1 : χ⁻¹.val w = χ₀⁻¹.val (w.under (𝓞 K)) :=
      (hv w 1 ((norm_split h2 hne e).trans (pow_one _).symm)).trans (pow_one _)
    have e2 : χ⁻¹.val w' = χ₀⁻¹.val (w.under (𝓞 K)) := by
      rw [← e]
      exact (hv w' 1 ((norm_split h2 hne.symm e.symm).trans (by rw [e, pow_one]))).trans (pow_one _)
    refine ⟨_, _, hun k1, hun k2, ?_⟩
    rw [e1, e2, ← Multiset.map_add (f := _)]
    exact satTw k3 (pow_val hi₀ _).1
  · obtain ⟨_, B', k1, rfl, k3⟩ := hw.2 hq2
    refine ⟨_, B'.map (· * χ₀⁻¹.val (w.under (𝓞 K))), ?_, ?_, satTw k3 (pow_val hi₀ _).1⟩
    · have k4 := hun k1
      rw [hv w 2 hq2] at k4
      simpa only [Multiset.map_map, Function.comp_def, mul_pow] using k4
    · simp only [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, neg_mul]
  · have k := (hI τ τ' _ _ hne hc (k1.twist χ) (k2.twist χ)).twist χ₀⁻¹
    rw [pow_expo hχ, pow_expo hχ, pow_expo hi₀, ← Multiset.map_add (f := _), Multiset.map_map] at k
    simpa using k

end Main
end

