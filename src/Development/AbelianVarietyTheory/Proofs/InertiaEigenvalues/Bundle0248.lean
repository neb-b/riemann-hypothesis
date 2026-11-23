module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Formalism.UnipotentAdelicQuotients.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenDiscConvergentRingWithExpansions
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharExistsOfGreen
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GreenExists

open Polynomial Formalism.D.Classical Formalism.CyclotomicNorms Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq

variable {g : ℕ} [hg : Fact g.Prime]

theorem mem_grUnipBlock_iff {d a : ℕ} (ha : a < d) (u : Gn g d) :
    u ∈ (grUnipBlock d a : Set (GL (Fin d) (ZMod g))) ↔
      InPar a (u : Mt g d) ∧ tl a (u : Mt g d) = ((1 : Gn g a) : Mt g a) ∧
        br a (d - a) (u : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a)) := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · rcases h i j with h1 | h1
      · rw [h1, if_neg]; rintro rfl; omega
      · omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : (i : ℕ) < d ∧ (j : ℕ) < d := by omega
      rcases h ⟨i, hij.1⟩ ⟨j, hij.2⟩ with h1 | h1
      · simp only [tl, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff]
      · simp only at h1; omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : a + (i : ℕ) < d ∧ a + (j : ℕ) < d := by omega
      rcases h ⟨a + i, hij.1⟩ ⟨a + j, hij.2⟩ with h1 | h1
      · simp only [br, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff, add_right_inj]
      · simp only at h1; omega
  · rintro ⟨h1, h2, h3⟩ i j
    have hi := i.2
    have hj := j.2
    by_cases hia : (i : ℕ) < a
    · by_cases hja : (j : ℕ) < a
      · left
        have := congrFun (congrFun h2 ⟨i, hia⟩) ⟨j, hja⟩
        simpa only [tl, entN, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply, Fin.ext_iff] using this
      · right; omega
    · left
      by_cases hja : (j : ℕ) < a
      · rw [h1 i j hja (by omega), if_neg]; rintro rfl; omega
      · have := congrFun (congrFun h3 ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
        have e1 : a + (i - a) = (i : ℕ) := by omega
        have e2 : a + (j - a) = (j : ℕ) := by omega
        have e3 : ((i : ℕ) - a = j - a) ↔ (i : ℕ) = j := by omega
        simpa only [br, entN, e1, e2, e3, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply,
          Fin.ext_iff] using this

theorem pow_eq_self_iff {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g} (hz : aeval z f = 0) (n : ℕ) :
    z ^ g ^ n = z ↔ f.natDegree ∣ n := by
  have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  have has : Associated (minpoly (ZMod g) z) f :=
    (minpoly.irreducible hx).associated_of_dvd hf (minpoly.dvd _ _ hz)
  rw [hf.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← has.dvd_iff_dvd_left, minpoly.dvd_iff]
  simp [sub_eq_zero]

theorem rootsBar_eq {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g} (hz : aeval z f = 0) :
    rootsBar f = (Finset.range f.natDegree).val.map fun i => z ^ g ^ i := by
  have hroot : ∀ i, aeval (z ^ g ^ i) f = 0 := fun i => by
    have := aeval_algHom_apply ((FiniteField.frobeniusAlgHom (ZMod g) (Fbar g)) ^ i) z f
    rw [hz, map_zero] at this
    rw [← this]
    congr 1
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hinj : ∀ i j, i < j → j < f.natDegree → z ^ g ^ i ≠ z ^ g ^ j := fun i j hij hj h => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h2 : (z ^ g ^ i) ^ g ^ (m + 1) = z ^ g ^ i := by
      rw [← pow_mul, ← pow_add, ← add_assoc, ← h]
    have := Nat.le_of_dvd (Nat.succ_pos m) ((pow_eq_self_iff hf (hroot i) _).1 h2)
    omega
  have hnd : ((Finset.range f.natDegree).val.map fun i => z ^ g ^ i).Nodup := by
    refine Multiset.Nodup.map_on (fun i hi j hj h => ?_) (Finset.range _).nodup
    rw [← Finset.mem_def, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with h1 | h1 | h1
    · exact absurd h (hinj i j h1 hj)
    · exact h1
    · exact absurd h.symm (hinj j i h1 hi)
  symm
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 fun w hw => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hw
    simpa [rootsBar, hf.ne_zero, aeval_def, eval_map] using hroot i
  · have := card_roots' (f.map (algebraMap (ZMod g) (Fbar g)))
    simpa [rootsBar] using this

end GlobalTheory.GreenExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTower
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem act_root_eq_pow_of_chi_nat {l : ℕ} [Fact l.Prime] (P : LocPrime l) (g : GQ l) (u : ℕ)
    (hg : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) (m : ℕ) (ζ : Om l) (hζ : ζ ^ (l ^ m) = 1) :
    g ζ = ζ ^ u := by
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m ζ hζ
  rw [hg] at ha
  have h2 : ‖((((u : ℤ) - (a : ℤ) : ℤ)) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    push_cast; exact ha
  have h3 : ((l : ℤ) ^ m) ∣ ((u : ℤ) - (a : ℤ)) := (Padic.norm_int_le_pow_iff_dvd _ _).mp h2
  have h4 : a ≡ u [MOD l ^ m] := by
    rw [Nat.modEq_iff_dvd]
    push_cast
    exact h3
  rw [hga, pow_eq_pow_mod a hζ, pow_eq_pow_mod u hζ, h4]

theorem actT_εroot_eq_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l)
    (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) →
      ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  intro l _ P AI g u hg j
  have hz : ∀ m, P.ζQ m ^ l ^ m = 1 := by
    intro m
    induction m with
    | zero => simpa using P.ζQ_zero
    | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  refine Perfection.ext fun n => ?_
  have hc : PreTilt.coeff n (AI.εroot j) =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (n + j)) := by
    rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm]
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g _ n _ hc
  have h3 : y' = AI.ζ (n + j) ^ u := by
    apply Subtype.ext
    rw [h1, SubmonoidClass.coe_pow, AI.ζ_eq, AI.actC_ext,
      act_root_eq_pow_of_chi_nat P g u hg (n + j) _ (hz _)]
    exact map_pow (algebraMap (Om l) (PadicComplex l)) _ _
  change PreTilt.coeff n _ = PreTilt.coeff n _
  rw [h2, map_pow, hc, h3]
  exact map_pow _ _ _

end GlobalTheory.ExpImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicAdmissibleSemistable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Inhab

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

include P in
theorem fixed_frob (c : ↥(MaximalUnramifiedExtension l)) (hc : frobUr (l := l) c = c) : ∃ q : ℚ_[l], algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q = c := by
  let K := adjExt (c : Om l)
  let x : ↥(K0 K) := ⟨c, mem_adjExt _, c.2⟩
  have h1 : (P.PD K).φ (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c := by
    rw [P.PD_φ, phiB_algebraMap, hc]
  have h2 : (P.PD K).ι (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) ∈ (P.PD K).Fil 0 := by
    have e : (P.PD K).ι (algebraMap ↥(K0 K) P.R.B x) = algebraMap ↥(K0 K) P.R.BdR x := (P.PD K).ι.commutes x
    have e2 : algebraMap ↥(K0 K) P.R.BdR x = (algebraMap ↥(K0 K) ↥K.1 x) • (1 : P.R.BdR) := by
      rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR, Algebra.algebraMap_eq_smul_one]
    have e3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c = algebraMap ↥(K0 K) P.R.B x := rfl
    rw [e3, e, e2]
    exact Submodule.smul_mem _ _ (P.PD K).one_mem
  obtain ⟨q, hq⟩ := (P.PD K).fund _ h1 h2
  haveI := nontrivial_B P
  refine ⟨q, (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective ?_⟩
  rw [← hq, ← IsScalarTower.algebraMap_apply]

theorem kd_alg (q : ℚ_[l]) : kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] P.R.BdR q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]; rfl

theorem act_zpow (g : GQ l) (a : ℤ) :
    P.actQ g (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) =
      algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (isUnit_tB P).unit =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * (isUnit_tB P).unit := by
    ext; simp [localPrime_galoisAction_periodT, Algebra.smul_def]
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at h2
  rw [← map_zpow P.χQ]
  exact h2

end GlobalTheory.PMon.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroups
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem le_v_of_norm_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (k : ℕ)
    (hx : ‖x‖ ≤ (l : ℝ) ^ (-(k : ℤ))) :
    ((k : ℚ) : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlk : (l : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero k hl
  have hy : ‖x / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow, div_le_one (zpow_pos hlpos _)]
    exact hx
  obtain ⟨y, hxy⟩ : ∃ y : ℤ_[l], x = (l : ℚ_[l]) ^ k * (y : ℚ_[l]) := by
    refine ⟨⟨x / (l : ℚ_[l]) ^ k, hy⟩, ?_⟩
    show x = (l : ℚ_[l]) ^ k * (x / (l : ℚ_[l]) ^ k)
    field_simp
  have hmem : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) ∈ OL LL := by
    have e : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) = algebraMap ℤ_[l] ↥LL.1 y := rfl
    rw [e]
    exact (OL LL).algebraMap_mem y
  have hv0 : 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l])) := (P.27 LL _).2 hmem
  have hk : k • (1 : WithTop ℚ) = ((k : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_one]
  rw [hxy, map_mul, map_pow, map_natCast, (P.v LL).map_mul, (P.v LL).map_pow, P.26 LL, hk]
  exact le_add_of_nonneg_right hv0

theorem grp_GKs_H : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  intro l _ P _ K s LL _ W hW g
  have hcyc : IsCyc P.χQ := P.20
  have hχ : ((P.PD K).χ g : ℚ_[l]) = (P.χQ (g : GQ l) : ℚ_[l]) := P.PD_χ K g
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · unfold Gj at hg
    obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) s
    have hmem : ζ ∈ Ks K s := by
      unfold Ks
      exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ _)
        (IntermediateField.subset_adjoin ℚ_[l] _ hζ.pow_eq_one)
    have hfix : (g : GQ l) ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have hn : ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) :=
      hcyc.norm_sub_one_le_of_prim (g : GQ l) s hζ hfix
    have hv := le_v_of_norm_le P LL ((P.χQ (g : GQ l) : ℚ_[l]) - 1) s hn
    have e : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) - 1 =
        algebraMap ℚ_[l] ↥LL.1 ((P.χQ (g : GQ l) : ℚ_[l]) - 1) := by
      rw [hχ, map_sub, map_one]
    rw [W.GKs_def g, hW, e]
    exact_mod_cast hv
  · unfold Hinf at hg
    have hall : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      intro m
      refine (hcyc.fix_iff (g : GQ l) m).1 (fun ζ hζ => ?_)
      have hmem : ζ ∈ Kinf K := by
        unfold Kinf
        exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | ∃ j : ℕ, x ^ l ^ j = 1} ≤ _)
          (IntermediateField.subset_adjoin ℚ_[l] _ ⟨m, hζ⟩)
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      by_contra hne
      have hpos : 0 < ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hpos
      exact absurd (hall m) (not_le.2 hm)
    have h2 : (algebraMap ↥(OL LL) ↥LL.1) ↑(W.χΓ (W.resΓ g)) = 1 := by
      rw [W.χΓ_res g, hχ, h1, map_one]
    have h3 : ((W.χΓ (W.resΓ g) : ↥(OL LL))) = 1 := Subtype.ext h2
    have h4 : W.χΓ (W.resΓ g) = 1 := Units.val_eq_one.1 h3
    exact W.χΓ_inj (by rw [h4, map_one])

end GlobalTheory.Cyc.Decomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilInvariantJumpDescendsFinExtStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l), K.1 ≤ E.1 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]), (∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y) → (∀ i, y i ∈ (P.PD K).Fil a) → ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1)) → ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧ ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  first | exact @GlobalTheory.InvDescent.jump_descends | exact GlobalTheory.InvDescent.jump_descends | (intros; apply GlobalTheory.InvDescent.jump_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionFrameOfMatrixForm
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem act_eq_of_mem_intC {l : ℕ} [Fact l.Prime]
    {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {σ : GQ l} (hσ : σ ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ intC F) : act σ y = y := by
  simp only [intC, inC, Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe] at hy
  obtain ⟨⟨x, hxF, rfl⟩, -⟩ := hy
  rw [ha.1 σ x, (IntermediateField.mem_fixingSubgroup_iff F σ).1 hσ x hxF]

theorem isDec_of_matrix : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (K : FinExt l) (m d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsActC act → IsGen χ K m g → (∀ i j, ContinuousOn (fun σ => M σ i j) (Gj K m)) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, M (σ * τ) = M σ * M τ) → (∀ σ ∈ Gj K m, ∀ τ ∈ Gj K m, (M τ).map (act σ) = M τ) → (∀ i j, ‖D i j‖ ≤ 1) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ ≤ 1) ∧ D * X = (l : PadicComplex l) • (1 : Matrix (Fin d) (Fin d) (PadicComplex l))) → (∀ σ ∈ Gj K m, ∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, X i j ∈ intC (Ks K m)) ∧ M σ * D.map (act σ) = D * X) → (∀ σ ∈ Hinf K, M σ * D.map (act σ) = D) → (∃ X : Matrix (Fin d) (Fin d) (PadicComplex l), (∀ i j, ‖X i j‖ < rho1 l) ∧ M g * D.map (act g) - D = D * X) → ∃ U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l), IsDec act χ K m M D U g := by
  intro l _ act χ K m d M D g ha hg hMc hMmul hMfix hD hDinv hInt hH hgclose
  obtain ⟨Y, hY, hDY⟩ := hDinv
  have hl : (l : PadicComplex l) ≠ 0 := by
    exact_mod_cast (Fact.out : l.Prime).ne_zero

  have hright : D * ((l : PadicComplex l)⁻¹ • Y) = 1 := by
    rw [Matrix.mul_smul, hDY, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hdet : IsUnit D.det := Matrix.isUnit_det_of_right_inverse hright
  have hinv : D⁻¹ = (l : PadicComplex l)⁻¹ • Y := Matrix.inv_eq_right_inv hright
  have hDD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hdet
  have hDD' : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hdet

  have hmapmul : ∀ (e : PadicComplex l ≃+* PadicComplex l) (A B : Matrix (Fin d) (Fin d) (PadicComplex l)),
      (A * B).map e = A.map e * B.map e := by
    intro e A B
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum, map_mul]
  have hmapcomp : ∀ σ τ : GQ l, D.map (act (σ * τ)) = (D.map (act τ)).map (act σ) := by
    intro σ τ
    ext i j
    simp only [Matrix.map_apply, map_mul]
    rfl

  refine ⟨fun σ => D⁻¹ * (M σ * D.map (act σ)), hdet, hD, ?_, ⟨hg, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b
    rw [hinv, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hl, one_mul]
    exact hY a b
  · intro a b
    simp only [Matrix.mul_apply, Matrix.map_apply]
    refine continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_
    refine continuousOn_finsetSum _ fun j _ => (hMc k j).mul ?_
    exact (IsActC.continuous_orbit l act ha (D j b)).continuousOn
  · intro σ hσ a b
    obtain ⟨X, hX, hMX⟩ := hInt σ hσ
    show (D⁻¹ * (M σ * D.map (act σ))) a b ∈ intC (Ks K m)
    rw [hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    exact hX a b
  · intro σ hσ τ hτ
    obtain ⟨X, hX, hMX⟩ := hInt τ hτ
    have hUτ : D⁻¹ * (M τ * D.map (act τ)) = X := by
      rw [hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]

    have hXfix : X.map (act σ) = X := by
      ext i j
      exact act_eq_of_mem_intC ha (show σ ∈ (Ks K m).fixingSubgroup from hσ) (hX i j)
    show D⁻¹ * (M (σ * τ) * D.map (act (σ * τ)))
      = D⁻¹ * (M σ * D.map (act σ)) * (D⁻¹ * (M τ * D.map (act τ)))
    calc D⁻¹ * (M (σ * τ) * D.map (act (σ * τ)))
        = D⁻¹ * (M σ * (M τ * D.map (act τ)).map (act σ)) := by
          rw [hMmul σ hσ τ hτ, hmapmul, hMfix σ hσ τ hτ, hmapcomp]
          simp only [Matrix.mul_assoc]
      _ = D⁻¹ * (M σ * (D.map (act σ) * X)) := by rw [hMX, hmapmul, hXfix]
      _ = D⁻¹ * (M σ * D.map (act σ)) * (D⁻¹ * (M τ * D.map (act τ))) := by
          rw [hUτ]
          simp only [Matrix.mul_assoc]
  · intro σ hσ
    show D⁻¹ * (M σ * D.map (act σ)) = 1
    rw [hH σ hσ, hDD]
  · intro a b
    obtain ⟨X, hX, hMX⟩ := hgclose
    have hU : D⁻¹ * (M g * D.map (act g)) - 1 = X := by
      rw [← hDD, ← Matrix.mul_sub, hMX, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    show ‖(D⁻¹ * (M g * D.map (act g)) - 1) a b‖ < rho1 l
    rw [hU]
    exact hX a b
  · intro σ hσ
    show D * (D⁻¹ * (M σ * D.map (act σ))) = M σ * D.map (act σ)
    rw [← Matrix.mul_assoc, hDD', Matrix.one_mul]

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.FinExtIntegers

set_option synthInstance.maxHeartbeats 200000 in
theorem dvr_complete : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l), ∃ _ : IsDiscreteValuationRing ↥(OL LL), IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro l _ LL
  unfold OL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsScalarTower ℤ_[l] ℚ_[l] ↥LL.1 := inferInstance
  have hfin : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have : FaithfulSMul ℤ_[l] ↥LL.1 := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] ↥LL.1
  have hdvr : IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥LL.1) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[l] ℚ_[l] ↥LL.1
  have hloc : IsLocalHom (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] ↥LL.1
  refine ⟨hdvr, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] _, ?_⟩
  intro hu
  have hl : ¬IsUnit (l : ℤ_[l]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  apply hl
  apply (isUnit_map_iff (algebraMap ℤ_[l] ↥(integralClosure ℤ_[l] ↥LL.1)) _).mp
  simpa using hu

end GlobalTheory.FinExtIntegers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwistStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI → ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ, (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧ (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a, sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧ (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧ ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a, sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  intro l _ P AI h K
  exact GlobalTheory.DeRhamSymbol.exists_symbol l P AI h K
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasisStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), ∃ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (a : ℤ) (z : V ⊗[Qp] BdR), z ∈ FilV PD (LL := LL) (V := V) a ↔ ∀ i, Φ z i ∈ PD.Fil a) ∧ ∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i)) := by
  first | exact @GlobalTheory.exists_coord_tensor_dR | exact GlobalTheory.exists_coord_tensor_dR | (intros; apply GlobalTheory.exists_coord_tensor_dR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenDiscConvergentRingWithExpansionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openDiscConvergentRing_with_expansions : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ J, IsEval I β J → (∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a)) → (∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i))) → ∃ D : Disc R (β.comp I.io.toRingHom) ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) (algebraMap (Om l) P.R.BdR (P.ζQ s)), (∀ a : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)), (∀ i, Conv (a i)) → a ∈ D.C) ∧ (D.t : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K))) = fun _ => logS LL := by
  first | exact @GlobalTheory.HWL.Cmp.OpenDisc.exists_disc | exact GlobalTheory.HWL.Cmp.OpenDisc.exists_disc | (intros; apply GlobalTheory.HWL.Cmp.OpenDisc.exists_disc <;> assumption)
end

