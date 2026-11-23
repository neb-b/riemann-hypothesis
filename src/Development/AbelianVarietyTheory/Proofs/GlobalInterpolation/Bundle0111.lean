module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0076
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
public import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SignedLiftWEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.LiftTranslate

theorem signed_eq {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {α : V → ℂ} (hH : IsHerm H) (hα : ∀ x, α (-x) = α x)
    {A B : AddSubgroup V} (hd : IsSelfDual H A) (hs : IsSemiChar H A α) {θ : V → ℂ} (hθ : θ ∈ fixedBy H α B)
    {s u : V} (h1 : s ∈ A) (h2 : u ∈ A) (h3 : u - s ∈ B) (z : V) :
    α s * opU H (-s) θ z = α u * opU H (-u) θ z := by
  have h := GlobalTheory.ThetaInter.alpha_opU_add hH hd hs (A.neg_mem h2) (A.sub_mem h2 h1) θ z
  rw [show -u + (u - s) = -s by abel, hα, hα, ← GlobalTheory.ThetaInter.opU_mul (-u) (α (u - s)),
    show (fun w => α (u - s) * opU H (u - s) θ w) = θ from funext (hθ _ h3)] at h
  exact h

theorem alV_neg {ι : Type} [Fintype ι] {a b : ℕ} (d : ℕ) (sc : ℝ) (x : VV ι a b) : alV d sc (-x) = alV d sc x := by
  simp [alV, alphaQ, Formalism.L2.Th1.H.qOf]

private theorem sdLat_span_local {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Sp E n)) (hL : IsSdLat L) :
    Submodule.span E (L : Set (Sp E n)) = ⊤ := by
  let W := Submodule.span E (L : Set (Sp E n))
  change W = ⊤
  by_contra h
  let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
  let g : Sp E n →ₗ[E] Module.Dual E W :=
    (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
  have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt h
  obtain ⟨x, hx, hx₀⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
  have hsmul (a : E) : a • e x ∈ L := by
    rw [← hL.2, dualBasic_mem_dual]
    intro y hy
    apply hStd_mem_one_symm
    have hxy : hStd E n (e x) y = 0 :=
      congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
    simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
  let i : E →ₗ[𝓞 E] L :=
    ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
  let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.1.fg
  let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

omit [StarRing E] in
theorem nat_smul_mem {M : Submodule (𝓞 E) (HomE E a b)} (c : ℕ) {y : HomE E a b} (hy : y ∈ M) : (c : E) • y ∈ M := by
  rw [Nat.cast_smul_eq_nsmul]
  exact M.toAddSubgroup.nsmul_mem hy c

theorem off_le (S : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) (HomE E a b)) {c c' : ℕ} (hc : 0 < c) (hc' : 0 < c')
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : Q ∉ S) {y : HomE E a b} (hy : y ∈ localization₂ Q.asIdeal (halfAO S M c')) :
    y ∈ localization₂ Q.asIdeal (twist₂ M c (expS S)) := by
  have hcE : (c' : E) ≠ 0 := by exact_mod_cast hc'.ne'
  rw [halfAO, mem_localization_twist M hc' (fun Q => by have := expS_bound S Q; omega)] at hy
  rw [mem_localization_twist M hc (expS_bound S)]
  unfold expS at hy ⊢
  rw [if_neg hQ] at hy ⊢
  split_ifs at hy ⊢
  · have h1 := nat_smul_mem c' hy
    rw [neg_neg, zpow_one, smul_smul, mul_inv_cancel₀ hcE, one_smul] at h1
    rw [zpow_neg, inv_inv, zpow_one]
    exact nat_smul_mem c h1
  · simpa using hy

theorem mem_mulLat_iff (S : Finset (HeightOneSpectrum (𝓞 E))) (AA : Submodule (𝓞 E) E) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (hN : N.FG) (hAA : ∀ P ∈ S, localization₂ P.asIdeal AA = localization₂ P.asIdeal (1 : Submodule (𝓞 E) E))
    {c : ℕ} (hc : 0 < c) (y : HomE E a b) :
    y ∈ mulLat c (homAt S N N') ↔ ∀ P ∈ S, y ∈ localization₂ P.asIdeal (twist₂ (perO AA N N') c (expS S)) := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  have key : ∀ P ∈ S, (y ∈ localization₂ P.asIdeal (twist₂ (perO AA N N') c (expS S)) ↔ (c : E)⁻¹ • y ∈ homAt {P} N N') := by
    intro P hP
    rw [mem_localization_twist _ hc (expS_bound S), (GlobalTheory.ThetaMove.PeriodComp.perO_components E a b AA).2.1 P N N' hN (hAA P hP), expS,
      if_pos hP, zpow_one]
  have hsm : ∀ w : HomE E a b, (c : 𝓞 E) • w = (c : E) • w := fun w => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  constructor
  · rintro ⟨w, hw, rfl⟩ P hP
    rw [key P hP, LinearMap.smul_apply, LinearMap.id_apply, hsm, smul_smul, inv_mul_cancel₀ hcE, one_smul]
    intro P' hP'
    rw [Finset.mem_singleton.1 hP']
    exact hw P hP
  · intro h
    refine ⟨(c : E)⁻¹ • y, fun P hP => (key P hP).1 (h P hP) P (Finset.mem_singleton_self P), ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, hsm, smul_smul, mul_inv_cancel₀ hcE, one_smul]

end Loc

theorem signed_liftW_eq : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N G : Submodule (𝓞 X.E) (Sp X.E a)) (N' G' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x t : HomE X.E a b) (θ : VCx X.Tau a b → ℂ), Moves A a b → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → IsSdLat G → IsSdLat G' → 0 < c → Dom S (perO A.AA G G') (perO A.AA N (twist₂ N' c (expS S))) → t ∈ perO A.AA G G' → t - x ∈ mulLat c (homAt S N N') → θ ∈ fixedBy (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N (twist₂ N' c (expS S))) → ∀ z, (alV A.d A.sc) ((embH (X.embC A.σ₀) A.δ) (A.liftW S N N' c x)) * opU (Formalism.L2.Ker.HV A.sc) (-((embH (X.embC A.σ₀) A.δ) (A.liftW S N N' c x))) θ z = (alV A.d A.sc) ((embH (X.embC A.σ₀) A.δ) t) * opU (Formalism.L2.Ker.HV A.sc) (-((embH (X.embC A.σ₀) A.δ) t)) θ z := by
  intro X A a b S N G N' G' c x t θ hM hS hAA hN hN' hG hG' hc hD ht htx hθ z
  obtain ⟨hδ, -, -, hA0, hLa, -⟩ := hM
  have hfg : N.FG := hN.1.fg
  have per := GlobalTheory.ThetaMove.PeriodComp.perO_components X.E a b A.AA
  have eB : twist₂ (perO A.AA N N') c (expS S) = perO A.AA N (twist₂ N' c (expS S)) :=
    GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c _ hfg hc (expS_bound S)
  have eA : ∀ c' : ℕ, 0 < c' → halfAO S (perO A.AA N N') c' = perO A.AA N (twist₂ N' c' fun Q => -expS S Q) := fun c' hc' =>
    GlobalTheory.ThetaMove.PeriodTwist.twO_perO X.E a b A.AA N N' c' _ hfg hc' (fun Q => by have := expS_bound S Q; omega)
  have sdB := (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c S hS hN' hc).1
  have sdA := fun c' (hc' : 0 < c') => (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS X.E b N' c' S hS hN' hc').2
  have fullSd {n : ℕ} (L : Submodule (𝓞 X.E) (Sp X.E n)) (hL : IsSdLat L) :
      Submodule.IsFullLattice X.E L := by
    letI : Submodule.IsLattice X.E L := hL.1
    exact ⟨sdLat_span_local L hL⟩
  have fB : Full (twist₂ (perO A.AA N N') c (expS S)) := eB ▸ per.2.2 N _ hfg (fullSd _ sdB) hA0
  have fA : ∀ c' : ℕ, 0 < c' → Full (halfAO S (perO A.AA N N') c') := fun c' hc' => by
    rw [eA c' hc']; exact per.2.2 N _ hfg (fullSd _ (sdA c' hc')) hA0
  have fG : Full (perO A.AA G G') := per.2.2 G G' hG.1.fg (fullSd _ hG') hA0
  have hmul := mem_mulLat_iff S A.AA N N' hfg hAA hc
  have hex : ∃ s, A.IsLift S N N' c x s := by
    obtain ⟨c', hc', hx⟩ := per.2.2 N N' hfg (fullSd _ hN') hA0 x
    obtain ⟨s, h1, h2⟩ := ((fA c' hc').inf fB).approx S x
    simp only [localization_inf, Submodule.mem_inf] at h1 h2
    refine ⟨s, ⟨c', hc', mem_of_locP fun Q => ?_⟩, (hmul _).2 fun P hP => (h1 P hP).2⟩
    by_cases hQ : Q ∈ S
    · have h3 : x ∈ localization₂ Q.asIdeal (halfAO S (perO A.AA N N') c') := by
        rw [halfAO, mem_localization_twist _ hc' (fun Q => by have := expS_bound S Q; omega), expS, if_pos hQ, zpow_neg, inv_inv, zpow_one,
          Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 X.E)]
        exact mem_localization_of_mem Q hx
      simpa using add_mem (h1 Q hQ).1 h3
    · exact (h2 Q hQ).1
  obtain ⟨⟨c₁, hc₁, hs⟩, hsx⟩ : A.IsLift S N N' c x (A.liftW S N N' c x) := Classical.epsilon_spec hex
  generalize A.liftW S N N' c x = s at hs hsx ⊢
  rw [hmul] at hsx htx
  rw [← eB] at hD
  obtain ⟨u, h1, h2⟩ := (((fA c₁ hc₁).inf fG).inf fB).approx S s
  simp only [localization_inf, Submodule.mem_inf] at h1 h2
  have huA : u ∈ halfAO S (perO A.AA N N') c₁ := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · simpa using add_mem (h1 Q hQ).1.1 (mem_localization_of_mem Q hs)
    · exact (h2 Q hQ).1.1
  have hus : u - s ∈ twist₂ (perO A.AA N N') c (expS S) := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · exact (h1 Q hQ).2
    · exact sub_mem (h2 Q hQ).2 (off_le S _ hc hc₁ hQ (mem_localization_of_mem Q hs))
  have hut : u - t ∈ twist₂ (perO A.AA N N') c (expS S) := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · rw [show u - t = (u - s) + (s - x) - (t - x) by abel]
      exact sub_mem (add_mem (h1 Q hQ).2 (hsx Q hQ)) (htx Q hQ)
    · exact sub_mem (h2 Q hQ).2 (hD.2 Q hQ (mem_localization_of_mem Q ht))
  have huG : u ∈ perO A.AA G G' := mem_of_locP fun Q => by
    by_cases hQ : Q ∈ S
    · simpa using add_mem (hD.1 Q hQ (mem_localization_of_mem Q hut)) (mem_localization_of_mem Q ht)
    · exact (h2 Q hQ).1.2
  rw [eB] at hus hut
  rw [eA c₁ hc₁] at hs huA
  have L1 := (hLa N _ hN (sdA c₁ hc₁)).2.2
  have L2 := (hLa G G' hG hG').2.2
  have im : ∀ {M : Submodule (𝓞 X.E) (HomE X.E a b)} {y}, y ∈ M → embH (X.embC A.σ₀) A.δ y ∈ laV (X.embC A.σ₀) A.δ M :=
    fun hy => ⟨_, hy, rfl⟩
  rw [signed_eq (isHerm_HV A.sc) (alV_neg A.d A.sc) L1.1 L1.2 hθ (im hs) (im huA) (by rw [← map_sub]; exact im hus),
    signed_eq (isHerm_HV A.sc) (alV_neg A.d A.sc) L2.1 L2.2 hθ (im ht) (im huG) (by rw [← map_sub]; exact im hut)]

end GlobalTheory.ThetaMove.LiftTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumInvCardStabEq
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeightedDoubleCoset

def stabConjEquiv {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Unfold.stab Γ K ((γ₀ : G) * g * k) ≃ Unfold.stab Γ K g where
  toFun δ := ⟨γ₀⁻¹ * δ.1 * γ₀, by
    have h := K.mul_mem (K.mul_mem k.2 δ.2) (K.inv_mem k.2)
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  invFun δ := ⟨γ₀ * δ.1 * γ₀⁻¹, by
    have h := K.mul_mem (K.mul_mem (K.inv_mem k.2) δ.2) k.2
    simp only [Unfold.stab, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv] at h ⊢
    convert h using 1; group⟩
  left_inv δ := by ext; simp [mul_assoc]
  right_inv δ := by ext; simp [mul_assoc]

theorem card_stab_eq {G : Type} [Group G] (Γ K : Subgroup G) (g : G) (γ₀ : Γ) (k : K) :
    Nat.card (Unfold.stab Γ K ((γ₀ : G) * g * k)) = Nat.card (Unfold.stab Γ K g) :=
  Nat.card_congr (stabConjEquiv Γ K g γ₀ k)

theorem sum_inv_card_stab_eq : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (n m : ℕ) (g : Fin n → G) (g' : Fin m → G), (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) → (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g' i * k) → (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g' i * k = (γ' : G) * g' j * k' → i = j) → ∑ i, ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ∑ j, ((Nat.card (Unfold.stab Γ K (g' j)) : ℝ))⁻¹ := by
  intro G _ Γ K n m g g' hcov hdisj hcov' hdisj'
  choose e γe ke he using fun i => hcov' (g i)
  choose f γf kf hf using fun j => hcov (g' j)
  have hfe : ∀ i, f (e i) = i := by
    intro i
    symm
    refine hdisj i (f (e i)) 1 (γe i * γf (e i)) 1 (kf (e i) * ke i) ?_
    have h1 := he i
    rw [hf (e i)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  have hef : ∀ j, e (f j) = j := by
    intro j
    symm
    refine hdisj' j (e (f j)) 1 (γf j * γe (f j)) 1 (ke (f j) * kf j) ?_
    have h1 := hf j
    rw [he (f j)] at h1
    simp only [OneMemClass.coe_one, one_mul, mul_one, Subgroup.coe_mul]
    simpa only [mul_assoc] using h1
  let σ : Fin n ≃ Fin m := ⟨e, f, hfe, hef⟩
  refine Fintype.sum_equiv σ _ _ (fun i => ?_)
  show ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = ((Nat.card (Unfold.stab Γ K (g' (e i))) : ℝ))⁻¹
  rw [he i, card_stab_eq]

end GlobalTheory.WeightedDoubleCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_numAt :
    SzRow (fun C D L => HostArith D.host → Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) := by
  refine szRow_and_imp.2 _ _ (szRow_and_imp.1 _ _ (szRow_and_imp.1 _ _ explicitConstants_parameterConditions_large szRow_blockLengthParams)
    (szRow_and_imp.1 _ _ szRow_sizesAt szRow_band_lambda_primes)) ?_
  rintro C cD ch D L hC hV ⟨⟨h5, hT⟩, hS, hrho, hLa, hg, hp, hp', hTT, hCode⟩ hA
  obtain ⟨P, hPK, hPW⟩ := h5 hA
  obtain ⟨T, hTK, hTe⟩ := hT P hPW
  have hCt : C.Ct = 401 := hC.1.2.2.2.2.2.2.2.2.2
  obtain ⟨hn, hm, hk, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, -, hLw, hcc, -⟩ := hV.host
  refine ⟨⟨{ params := P
             params_K := hPK
             CnW_eq := hPW
             parT := T
             parT_K := hTK
             eP_eq := hTe
             sizes := hS
             rho_le := hrho
             CGam_eq := hV.CGam_eq
             Cc_eq := hV.Cc_eq
             Ct_eq := hV.Ct_eq
             secondConstant_eq := hV.secondConstant_eq
             LaG_ge := hLa
             bT_le := hV.bT_le
             ccK_top := hcc
             g_le := hg
             pde_lt := ⟨hp, hp'⟩
             logFiveDepth_eq := hV.logFiveDepth_eq
             Lw_eq := ?_
             cloud1 := fun τ τ' => ?_
             win := ⟨hn, hm, hk⟩ }⟩, hTT, hCode⟩
  · rw [hLw, hCt]; unfold Lwv; norm_num
  · funext i
    rw [hV.hc.1 τ i, hV.hc.1 τ' i]

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaCharHalfPeriodEqZeroIff
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.Glob.ThetaParity

open Complex

theorem jacobiTheta₂_add_int (z τ : ℂ) (k : ℤ) :
    jacobiTheta₂ (z + (k : ℂ)) τ = jacobiTheta₂ z τ := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have : z + ((k + 1 : ℤ) : ℂ) = (z + (k : ℂ)) + 1 := by push_cast; ring
    rw [this, jacobiTheta₂_add_left]; exact_mod_cast ih
  | pred k ih =>
    have : z + ((-(k : ℤ) : ℤ) : ℂ) = (z + ((-(k : ℤ) - 1 : ℤ) : ℂ)) + 1 := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((-(k : ℤ) : ℤ) : ℂ)) τ = jacobiTheta₂ z τ := by exact_mod_cast ih
    rw [← ih', this, jacobiTheta₂_add_left]

theorem jacobiTheta₂_add_int_mul_eq_zero_iff (z τ : ℂ) (l : ℤ) :
    jacobiTheta₂ (z + (l : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  induction l using Int.induction_on with
  | zero => simp
  | succ l ih =>
    have : z + ((l + 1 : ℤ) : ℂ) * τ = (z + (l : ℂ) * τ) + τ := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((l : ℤ) : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by exact_mod_cast ih
    rw [this, jacobiTheta₂_add_left', mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
    exact_mod_cast ih'
  | pred l ih =>
    have : z + ((-(l : ℤ) : ℤ) : ℂ) * τ = (z + ((-(l : ℤ) - 1 : ℤ) : ℂ) * τ) + τ := by push_cast; ring
    have ih' : jacobiTheta₂ (z + ((-(l : ℤ) : ℤ) : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by exact_mod_cast ih
    rw [← ih', this, jacobiTheta₂_add_left', mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]

theorem jacobiTheta₂_shift_eq_zero_iff (z τ : ℂ) (k l : ℤ) :
    jacobiTheta₂ (z + (k : ℂ) + (l : ℂ) * τ) τ = 0 ↔ jacobiTheta₂ z τ = 0 := by
  rw [jacobiTheta₂_add_int_mul_eq_zero_iff, jacobiTheta₂_add_int]

theorem thetaChar_half_period_eq_zero_iff :
    ∀ τ : UpperHalfPlane, ThetaConstantWeber.JacobiProduct τ → ∀ (m n : ℤ) (a b : Fin 2),
    JacobiThetaHalfCharacteristic.IsEvenChar a b →
    (JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2) (τ : ℂ) = 0 ↔
      Odd (m + ((b : ℕ) : ℤ)) ∧ Odd (n + ((a : ℕ) : ℤ))) := by
  intro τ hJ m n a b _
  set t : ℂ := (τ : ℂ)

  have hprod : ThetaConstantWeber.thetaConst 0 0 τ * ThetaConstantWeber.thetaConst 0 1 τ * ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := by
    rw [hJ]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ (ModularForm.eta_ne_zero τ.2))
  have h00 : jacobiTheta₂ 0 t ≠ 0 := by
    have := left_ne_zero_of_mul (left_ne_zero_of_mul hprod)
    simpa [ThetaConstantWeber.thetaConst, t] using this
  have h01 : jacobiTheta₂ (1 / 2) t ≠ 0 := by
    have := right_ne_zero_of_mul (left_ne_zero_of_mul hprod)
    simpa [ThetaConstantWeber.thetaConst, t] using this
  have h10 : jacobiTheta₂ (t / 2) t ≠ 0 := by
    have := right_ne_zero_of_mul hprod
    simp only [ThetaConstantWeber.thetaConst, mul_eq_zero, Complex.exp_ne_zero, false_or, ne_eq] at this
    simpa [t] using this
  have h11 : jacobiTheta₂ ((1 + t) / 2) t = 0 := by
    rw [add_comm]; exact GlobalTheory.JacobiDeriv.jacobiTheta₂_half_period t

  set p : ℤ := m + ((b : ℕ) : ℤ)
  set q : ℤ := n + ((a : ℕ) : ℤ)
  have hred : JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * t) / 2) t = 0 ↔
      jacobiTheta₂ ((((p % 2 : ℤ) : ℂ) + ((q % 2 : ℤ) : ℂ) * t) / 2 + ((p / 2 : ℤ) : ℂ) +
        ((q / 2 : ℤ) : ℂ) * t) t = 0 := by
    unfold JacobiThetaHalfCharacteristic.thetaChar
    rw [mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
    have hp := Int.emod_add_mul_ediv p 2
    have hq := Int.emod_add_mul_ediv q 2
    have hp' : ((p % 2 : ℤ) : ℂ) + 2 * ((p / 2 : ℤ) : ℂ) = (m : ℂ) + ((b : ℕ) : ℂ) := by
      exact_mod_cast hp
    have hq' : ((q % 2 : ℤ) : ℂ) + 2 * ((q / 2 : ℤ) : ℂ) = (n : ℂ) + ((a : ℕ) : ℂ) := by
      exact_mod_cast hq
    have : ((m : ℂ) + (n : ℂ) * t) / 2 + (((a : ℕ) : ℂ) * t + ((b : ℕ) : ℂ)) / 2 =
        ((((p % 2 : ℤ) : ℂ) + ((q % 2 : ℤ) : ℂ) * t) / 2 + ((p / 2 : ℤ) : ℂ) +
        ((q / 2 : ℤ) : ℂ) * t) := by
      linear_combination (-(1:ℂ)/2) * hp' + (-(t:ℂ)/2) * hq'
    rw [this]
  rw [hred, jacobiTheta₂_shift_eq_zero_iff, Int.odd_iff, Int.odd_iff]
  rcases Int.emod_two_eq_zero_or_one p with hp | hp <;>
    rcases Int.emod_two_eq_zero_or_one q with hq | hq <;>
    rw [hp, hq] <;> push_cast
  · simpa using h00
  · simpa using h10
  · simpa using h01
  · simpa [add_comm] using h11

end GlobalTheory.Glob.ThetaParity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryGroupNegFormCompatible
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem uj_neg_eq {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J : Matrix n n A) : Formalism.UG.UJ s (-J) = Formalism.UG.UJ s J := by
  ext g
  show Formalism.UG.cT s (g : Matrix n n A) * (-J) * (g : Matrix n n A) = -J ↔
    Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem hR_neg_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : HR R σ (-J) = HR R σ J := by
  unfold HR JR
  rw [Matrix.map_neg _ (map_neg _), uj_neg_eq]

theorem hFin_neg_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : HFin R σ (-J) = HFin R σ J := by
  unfold HFin
  rw [uj_neg_eq]

theorem unitary_neg_same : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E), J' = -J → ∃ φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ J', (∀ h, HA.mat (AF F) σ J' (φ h) = HA.mat (AF F) σ J h) ∧ (∀ h, h ∈ HFinIn (AF F) σ J ↔ φ h ∈ HFinIn (AF F) σ J') ∧ ∀ (L : Set (Fin M → E)) h, h ∈ StabFin.SFin σ J L ↔ φ h ∈ StabFin.SFin σ J' L := by
  intro F E _ _ _ _ _ σ M J J' hJ
  subst hJ
  have e := (hR_neg_eq (AF F) σ J).symm
  let ψ : HA (AF F) σ J ≃* HA (AF F) σ (-J) := MulEquiv.subgroupCongr e
  have hψ : ∀ h : HA (AF F) σ J, HA.mat (AF F) σ (-J) (ψ h) = HA.mat (AF F) σ J h := fun h => rfl
  let φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ (-J) :=
    { ψ with
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val _ }
  have hφ : ∀ h : HA (AF F) σ J, HA.mat (AF F) σ (-J) (φ h) = HA.mat (AF F) σ J h := fun h => rfl
  refine ⟨φ, hφ, ?_, ?_⟩
  · intro h
    show (HA.mat (AF F) σ J h) ∈ HFin (AF F) σ J ↔ (HA.mat (AF F) σ (-J) (φ h)) ∈ HFin (AF F) σ (-J)
    rw [hFin_neg_eq]
    exact Iff.rfl
  · intro L h
    exact Iff.rfl

end GlobalTheory
end

