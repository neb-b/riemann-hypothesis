module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLift
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.KatzPull

open GlobalTheory.Katz

theorem lift_X (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} (s : σ) :
    Katz.lift p (X s : MvPowerSeries σ k) = X s := by
  classical
  ext α
  rw [coeff_lift, coeff_X, coeff_X]
  split_ifs
  · rw [map_one, map_one]
  · rw [WittVector.teichmuller_zero, map_zero]

theorem lin_subst {R : Type} [CommRing R] {d e : ℕ} (a : Fin e → MvPowerSeries (Fin d) R)
    (ha : ∀ j, constantCoeff (a j) = 0) (f : MvPowerSeries (Fin e) R) :
    lin (subst a f) = pullLin a (lin f) := by
  classical
  have ha' := hasSubst_of_constantCoeff_zero ha
  have hcard : ∀ α : Fin e →₀ ℕ, Multiset.card (Finsupp.toMultiset α) = α.degree := fun α => by
    rw [Finsupp.card_toMultiset, Finsupp.degree]; rfl
  have inj : Function.Injective (Finsupp.toMultiset : (Fin e →₀ ℕ) → Multiset (Fin e)) :=
    fun x y hxy => by simpa using congrArg Multiset.toFinsupp hxy
  set f1 : MvPowerSeries (Fin e) R := C (constantCoeff f) + ∑ j, C (lin f j) * X j with hf1
  have hf2 : ∀ α : Fin e →₀ ℕ, α.degree < 2 → coeff α (f - f1) = 0 := by
    intro α hα
    rcases (show α.degree = 0 ∨ α.degree = 1 by omega) with h | h
    · have h0 : α = 0 := by
        apply inj
        rw [map_zero, ← Multiset.card_eq_zero, hcard, h]
      subst h0
      simp [hf1, coeff_X]
    · obtain ⟨j, hj⟩ := Multiset.card_eq_one.1 ((hcard α).trans h)
      have h1 : α = Finsupp.single j 1 := by
        apply inj
        rw [hj, Finsupp.toMultiset_single, one_smul]
      subst h1
      simp [hf1, coeff_X, coeff_C, lin, Finsupp.single_eq_single_iff]
  funext i
  have key := (_root_.GlobalTheory.coeff_subst_leading R (Fin e) (Fin d) a a 2 (f - f1) ha ha (fun _ _ _ => rfl) hf2
    (Finsupp.single i 1)).1 (by rw [Finsupp.degree_single]; norm_num)
  rw [subst_sub ha', map_sub, sub_eq_zero] at key
  unfold lin pullLin
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, hf1, subst_add ha', subst_C, map_add (f := _), coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero),
    zero_add, ← coe_substAlgHom ha', map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom ha', subst_C, subst_X ha', coeff_C_mul]
  rfl

theorem quasiLog_pull : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (φ j)) f ∈ quasiLog p hμ ∧ (∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c → Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (subst (fun j => Katz.lift p (φ j)) f)) (pullLin φ w) := by
  intro p _ k _ _ _ d e μ ν hμ hν φ hφ f hf
  obtain ⟨hf1, hf2⟩ := hf
  have hΦ0 : ∀ j, constantCoeff (Katz.lift p (φ j)) = 0 := fun j => constantCoeff_lift p (hφ.const j)
  have hΦs : HasSubst (fun j => Katz.lift p (φ j)) := hasSubst_of_constantCoeff_zero hΦ0
  have hLμ0 : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hLμs : HasSubst (fun i => Katz.lift p (μ i)) := hasSubst_of_constantCoeff_zero hLμ0
  have hLν0 : ∀ i, constantCoeff (Katz.lift p (ν i)) = 0 := fun i => constantCoeff_lift p (hν.const i)
  have hXl0 : ∀ i : Fin d, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXr0 : ∀ i : Fin d, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXls := hasSubst_of_constantCoeff_zero hXl0
  have hXrs := hasSubst_of_constantCoeff_zero hXr0
  have RR := fun σ => _root_.GlobalTheory.Katz.red_rules p k σ
  have hRedΦ : ∀ j, Red p (Katz.lift p (φ j)) (φ j) := fun j => (RR _).2.2.1 (φ j)
  have redX : ∀ {σ : Type} (s : σ), Red p (X s : MvPowerSeries σ (Fr p k)) (X s) := fun s => by
    simpa [lift_X] using (RR _).2.2.1 (X s : MvPowerSeries _ k)
  have hIL := _root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inl i)) (fun i => X (Sum.inl i))
    hXl0 (fun i => redX _)
  have hIR := _root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inr i)) (fun i => X (Sum.inr i))
    hXr0 (fun i => redX _)

  set U : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    Sum.elim (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) with hU
  set U' : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k :=
    Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) with hU'
  have hinL0 : ∀ j, constantCoeff (inL (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXls hXl0 (hΦ0 j)
  have hinR0 : ∀ j, constantCoeff (inR (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXrs hXr0 (hΦ0 j)
  have hU0 : ∀ s, constantCoeff (U s) = 0 := by
    rintro (j | j)
    · exact hinL0 j
    · exact hinR0 j
  have hRedU : ∀ s, Red p (U s) (U' s) := by
    rintro (j | j)
    · exact hIL.1 _ _ (hRedΦ j)
    · exact hIR.1 _ _ (hRedΦ j)
  have hIU := _root_.GlobalTheory.Katz.red_subst p k (Fin e ⊕ Fin e) (Fin d ⊕ Fin d) U U' hU0 hRedU
  have C6 := _root_.GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt (Fr p k) e (Fin d ⊕ Fin d) (Fin d ⊕ Fin d)
    (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) hinL0 hinR0

  set A : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst (fun i => Katz.lift p (μ i)) (Katz.lift p (φ j)) with hA
  set B : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst U (Katz.lift p (ν j)) with hB
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => constantCoeff_subst_eq_zero hLμs hLμ0 (hΦ0 j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU0) hU0 (hLν0 j)
  have hRA : ∀ j, Red p (A j) (subst μ (φ j)) := fun j =>
    (_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hLμ0 (fun i => (RR _).2.2.1 (μ i))).1 _ _ (hRedΦ j)
  have hRB : ∀ j, Red p (B j) (subst μ (φ j)) := fun j => by
    rw [hφ.hom j]
    exact hIU.1 _ _ ((RR _).2.2.1 (ν j))
  have hD := GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d ⊕ Fin d) A B (fun j => subst μ (φ j)) f hA0 hB0 hRA hRB hf1

  have hid : cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f) =
      (subst A f - subst B f) + subst U (cob1 (fun j => Katz.lift p (ν j)) f) := by
    have e1 : subst U (cob1 (fun j => Katz.lift p (ν j)) f) =
        subst B f - subst (fun j => inL (Katz.lift p (φ j))) f - subst (fun j => inR (Katz.lift p (φ j))) f := by
      change at2 (cob1 (fun j => Katz.lift p (ν j)) f) _ _ = _
      unfold cob1
      rw [(C6.2.2.1 _ _).2, (C6.2.2.1 _ _).2, C6.1, C6.2.1, C6.2.2.2.2.2.1 e _ hLν0]
      rfl
    rw [e1]
    unfold cob1 inL inR
    rw [subst_comp_subst_apply hΦs hLμs, subst_comp_subst_apply hΦs hXls,
      subst_comp_subst_apply hΦs hXrs]
    abel
  have part2 : ∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c →
      Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c) := by
    intro c hc
    rw [hid]
    have h1 := ((RR _).2.2.2.2.2.1 _).1 hD
    have h2 := hIU.1 _ _ hc
    have := ((RR _).2.2.2.1 _ _ _ _ h1 h2).1
    rwa [zero_add] at this
  refine ⟨⟨_root_.GlobalTheory.Katz.subst_mem_quasiInt p k (Fin e) (Fin d) _ f hΦ0
      (fun j => ((RR _).1 _).2 ⟨φ j, hRedΦ j⟩) hf1, ?_⟩, part2, ?_⟩
  · obtain ⟨c, hc⟩ := ((RR _).1 _).1 hf2
    exact ((RR _).1 _).2 ⟨_, part2 c hc⟩
  · intro w hw i
    rw [lin_subst _ hΦ0]
    choose a ha ha' using hw
    refine ⟨∑ j, a j * WittVector.teichmuller p (lin (φ j) i), ?_, ?_⟩
    · simp only [pullLin, map_sum, map_mul, ha]
      simp only [lin, coeff_lift]
    · simp only [pullLin, ← WittVector.constantCoeff_apply, map_sum, map_mul,
        WittVector.constantCoeff_apply, ha', WittVector.teichmuller_coeff_zero]

end GlobalTheory.KatzPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegOneSubEqDifferentialStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.red_chern_deg_one
  | exact GlobalTheory.EtC.RedChern.red_chern_deg_one
  | (intros; apply GlobalTheory.EtC.RedChern.red_chern_deg_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegTwoSubEqDefectsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  first
  | exact @GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | exact GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | (intros; apply GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundariesStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ i, constantCoeff (μ i) = 0) → (∀ g c, Red p g c → Red p (cob2 (fun i => Katz.lift p (μ i)) g) (cob2 μ c) ∧ Red p (swap g) (swap c)) ∧ (∀ b b', Red p b b' → Red p (cob1 (fun i => Katz.lift p (μ i)) b) (cob1 μ b') ∧ RedV p (lin b) (lin b')) ∧ (∀ i, Red p (op (fun i => Katz.lift p (μ i)) x1 (op (fun i => Katz.lift p (μ i)) x2 x3) i) (op μ x1 (op μ x2 x3) i) ∧ Red p (op (fun i => Katz.lift p (μ i)) (op (fun i => Katz.lift p (μ i)) x1 x2) x3 i) (op μ (op μ x1 x2) x3 i)) ∧ ∀ (c : WittVector p k) g, g ∈ intBy p k (Fin d ⊕ Fin d) c → cob2 (fun i => Katz.lift p (μ i)) g ∈ intBy p k _ c ∧ swap g ∈ intBy p k _ c := by
  first | exact @GlobalTheory.Katz.red_coboundaries | exact GlobalTheory.Katz.red_coboundaries | (intros; apply GlobalTheory.Katz.red_coboundaries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigToLieBijectiveAndDualRigOfOmegaBijectiveOfIsE
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (h : (p : k) = 0)
      (G : PDivGroup p k), G.IsEt →
      Function.Bijective (G.rigToLie h) ∧ Function.Bijective G.dual.rigOfOmega := by
  intro p _ k _ _ _ h G hG
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.PDivGroup.subsingleton_omega_of_isEt p k G hG
  refine ⟨⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, G.rigToLie_surjective h⟩,
    ⟨G.dual.rigOfOmega_injective_of_eq_zero h, fun y => ?_⟩⟩
  · obtain ⟨w, rfl⟩ := (G.exact_rigOfOmega_rigToLie h x).1 hx
    rw [Subsingleton.elim w 0, map_zero]
  · refine (G.dual.exact_rigOfOmega_rigToLie h y).1 ?_
    exact LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, LinearMap.zero_apply]

end PDivGroup

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionOnGroupSchemeIntCombinationEqProdZpowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringActionOnGroupScheme_intCombination_eq_prod_zpow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k := by
  first | (exact @GlobalTheory.ActSum.act_sum_zsmul) | (exact GlobalTheory.ActSum.act_sum_zsmul) | (intros; apply GlobalTheory.ActSum.act_sum_zsmul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomConnectedFactorThroughPart
section
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem PDivGroup.semiHom_app_eq_conn_part :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hEt hConn hsplit x n a
  have h1 : ∀ c : C.A n,
      i₁.app n (x.app n c) = algebraMap k' (G'₁.A n) (σ (counit (R := k) c)) := by
    intro c
    haveI := hEt n
    have hmem : c - algebraMap k (C.A n) (counit (R := k) c) ∈ augIdeal k (C.A n) := by
      rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
        ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    have h := (((hConn n _ hmem).map (x.app n).toRingHom).map (i₁.app n)).eq_zero
    change i₁.app n (x.app n (c - _)) = 0 at h
    rw [map_sub, SemiBialgHom.map_algebraMap, map_sub, AlgHomClass.commutes, sub_eq_zero] at h
    exact h
  have hP₁ : ∀ c : C.A n, (q₁ ≫ i₁).app n (x.app n c) =
      algebraMap k' (G'.A n) (σ (counit (R := k) c)) := by
    intro c
    rw [comp_app, BialgHom.comp_apply, h1, AlgHomClass.commutes]
  have hid : ∀ b : G'.A n, ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n).ofConv b = b := by
    intro b
    have h := congrArg (fun f : G' ⟶ G' => f.app n b) hsplit
    exact h
  have key : ∀ c : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two c) =
      (q₀ ≫ i₀).app n (x.app n (TensorProduct.rid k (C.A n)
        (LinearMap.lTensor (C.A n) (counit (R := k)) c))) := by
    intro c
    induction c with
    | add c d hc hd => simp only [map_add (f := _), hc, hd]
    | tmul b c =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
      change _ * (q₁ ≫ i₁).app n (x.app n c) = _
      rw [hP₁, (x.app n).smul_map, map_smul, Algebra.smul_def, mul_comm]
      rfl
  have e : (toPts ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n)).ofConv (x.app n a) = x.app n a :=
    hid (x.app n a)
  rw [map_mul, AlgHom.convMul_apply, toPts_ofConv, toPts_ofConv, ← (x.app n).two_comul] at e
  have e2 := key (comul (R := k) a)
  rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul] at e2
  exact e2.symm.trans e

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomEtaleFactorThroughPart
section
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem app_app_eq_algebraMap_counit_of_isConn_of_isEt {p : ℕ} [Fact p.Prime] {k k' : Type}
    [Field k] [CharP k p] [PerfectRing k p] [Field k'] {σ : k →+* k'} {G' G'₀ : PDivGroup p k'}
    {C : PDivGroup p k} (i₀ : G'₀ ⟶ G') (hG : G'₀.IsConn) (hC : C.IsEt) (x : SemiHom σ G' C)
    (n : ℕ) (a : C.A n) :
    i₀.app n (x.app n a) = algebraMap k' (G'₀.A n) (σ (counit (R := k) a)) := by
  have hmem : a - algebraMap k (C.A n) (counit (R := k) a) ∈ augIdeal k (C.A n) := by
    rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
      ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  suffices h : i₀.app n ((x.app n).toRingHom (a - algebraMap k (C.A n) (counit (R := k) a))) = 0 by
    rw [map_sub, map_sub, sub_eq_zero] at h
    refine h.trans ?_
    change i₀.app n ((x.app n) (algebraMap k (C.A n) (counit (R := k) a))) = _
    rw [(x.app n).map_algebraMap, AlgHomClass.commutes]
  haveI := hC n
  haveI : IsNoetherianRing (G'₀.A n) := isNoetherian_of_tower k' inferInstance
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (augIdeal k' (G'₀.A n)))).2 fun y hy => mem_nilradical.2 (hG n y hy)
  obtain ⟨b, hb, hab⟩ := exists_augIdeal_pow_eq (A := C.A n) N _ hmem
  have hfb : i₀.app n ((x.app n).toRingHom b) ∈ augIdeal k' (G'₀.A n) := by
    rw [mem_augIdeal_iff', CoalgHomClass.counit_comp_apply]
    change counit (R := k') ((x.app n) b) = 0
    rw [(x.app n).counit_map, (mem_augIdeal_iff' b).1 hb, map_zero]
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h1 := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hfb (p ^ N))
  rw [hN] at h1
  rw [hab, map_pow, map_pow]
  exact (Submodule.mem_bot _).1 h1

theorem add_app_eq_lift_comul {p : ℕ} {k : Type} [CommRing k] {G H : PDivGroup p k}
    (f g : G ⟶ H) (n : ℕ) (c : H.A n) :
    Hom.app (f + g) n c = Algebra.TensorProduct.lift (f.app n : H.A n →ₐ[k] G.A n)
      (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => .all _ _) (comul c) := by
  have h := DFunLike.congr_fun (congrArg ofConv (map_mul toPts (f.conv n) (g.conv n))) c
  rw [AlgHom.convMul_apply] at h
  exact h

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hG hC hs x n a
  have key : ∀ t : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two t) =
      (q₁ ≫ i₁).app n (x.app n (TensorProduct.lid k _ (LinearMap.rTensor _ counit t))) := by
    intro t
    induction t with
    | add u v hu hv =>
      rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _), map_add (f := _), ← map_add (f := _), ← map_add (f := _)]
    | tmul a₁ a₂ =>
      rw [TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply,
        Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      change q₀.app n (i₀.app n (x.app n a₁)) * _ = _
      rw [app_app_eq_algebraMap_counit_of_isConn_of_isEt i₀ hG hC x n a₁, AlgHomClass.commutes,
        ← Algebra.smul_def, (x.app n).smul_map]
      change _ = ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (σ (counit a₁) • x.app n a₂)
      rw [map_smul]
  have h1 : x.app n a = Hom.app (q₀ ≫ i₀ + q₁ ≫ i₁) n (x.app n a) := by rw [hs]; rfl
  rw [add_app_eq_lift_comul, ← SemiBialgHom.two_comul, key, Coalgebra.rTensor_counit_comul,
    TensorProduct.lid_tmul, one_smul] at h1
  exact h1.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTwStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqv_spMap_tw_of_isUnit : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  first | (exact @GlobalTheory.EtC.sh_eqv_tw) | (exact GlobalTheory.EtC.sh_eqv_tw) | (intros; apply GlobalTheory.EtC.sh_eqv_tw  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionPrimitiveLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_smallExt : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  intro R R' R₀ _ _ _ t σ σ₀ g A _ A' _ A₀ _ φ φ₀ h h₀ hS hA _ hP hN x
  haveI := hA.smooth
  have hF : Flat A.hom := inferInstance
  have hF2 : Flat (A ⊗ A).hom := by
    show Flat (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  obtain ⟨Φ, hΦ, hm, h1, h2, -, -⟩ := _root_.GlobalTheory.AbCoh.prod_pullback_sq R R' σ A A' φ h
  obtain ⟨Φ₀, hΦ₀, hm₀, h1₀, h2₀, -, -⟩ := _root_.GlobalTheory.AbCoh.prod_pullback_sq R R₀ σ₀ A A₀ φ₀ h₀
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.AbCoh.exists_bock R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x

  have nat : ∀ (ψ : (A ⊗ A).left ⟶ A.left) (ψ' : (A' ⊗ A').left ⟶ A'.left) (ψ₀ : (A₀ ⊗ A₀).left ⟶ A₀.left)
      (w : ψ ≫ A.hom = (A ⊗ A).hom ≫ spMap (RingHom.id R)) (w' : ψ' ≫ A'.hom = (A' ⊗ A').hom ≫ spMap (RingHom.id R'))
      (w₀ : ψ₀ ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = Φ ≫ ψ → ψ₀ ≫ φ₀ = Φ₀ ≫ ψ →
      ∀ z', Bock hΦ.w hΦ₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
    intro ψ ψ' ψ₀ w w' w₀ e e₀ z' hz'
    exact _root_.GlobalTheory.AbCoh.bock_natural R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1
      (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom Φ Φ₀ hΦ hΦ₀
      ψ ψ' ψ₀ w w' w₀ e e₀ hS hF hF2 x z z' hz hz'
  have ex : ∀ y : HO1 (A' ⊗ A').hom, ∃ z' : HO2 (A₀ ⊗ A₀).hom, Bock hΦ.w hΦ₀.w t y z' := fun y ↦
    _root_.GlobalTheory.AbCoh.exists_bock R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom
      Φ Φ₀ hΦ hΦ₀ hS hF2 y
  obtain ⟨z1, hz1⟩ := ex (pO1 (fst A' A') x)
  obtain ⟨z2, hz2⟩ := ex (pO1 (snd A' A') x)
  have e1 : z1 = structureSheafH2Pullback (fst A₀ A₀) z := nat _ _ _ (ovw (fst A A)) (ovw (fst A' A')) (ovw (fst A₀ A₀)) h1 h1₀ z1 hz1
  have e2 : z2 = structureSheafH2Pullback (snd A₀ A₀) z := nat _ _ _ (ovw (snd A A)) (ovw (snd A' A')) (ovw (snd A₀ A₀)) h2 h2₀ z2 hz2
  have hsum := _root_.GlobalTheory.AbCoh.Bock_add R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom
    (A₀ ⊗ A₀).hom Φ Φ₀ hΦ.w hΦ₀.w _ _ z1 z2 hz1 hz2
  rw [← hP x] at hsum
  have em : z1 + z2 = structureSheafH2Pullback μ[A₀] z := nat _ _ _ (ovw μ[A]) (ovw μ[A']) (ovw μ[A₀]) hm hm₀ _ hsum
  have z0 : z = 0 := hN z (by rw [← em, e1, e2])
  subst z0
  exact _root_.GlobalTheory.AbCoh.exists_lift_of_bock_zero R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x hz

end GlobalTheory.AbCoh
end

