module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAverageKillsFockComplementRelInvariants
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslate
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormAction

theorem exists_rangeRestrict_eq {G H : Type} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : ∀ g, ∃ a ∈ f.ker, ∃ k ∈ K, g = a * k) (x : f.range) : ∃ k ∈ K, f.rangeRestrict k = x := by
  obtain ⟨_, g, rfl⟩ := x
  obtain ⟨a, ha, k, hk, rfl⟩ := h g
  refine ⟨k, hk, Subtype.ext ?_⟩
  show f k = f (a * k)
  rw [map_mul, MonoidHom.mem_ker.1 ha, one_mul]

theorem exists_lift {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (q : (levEnv V β L).Q) : ∃ κ, (finHom V).rangeRestrict κ = q.1 ∧
    IsLevelLift V β L (rTup β L (Formalism.UG.bc (swapAE D) q.1.1)) κ ∧
      ((((levEnv V β L).ch q)⁻¹ : ℂˣ) : ℂ) = (levChi V β (flagL L) κ)⁻¹ := by
  refine (exists_rangeRestrict_eq (finHom V) (GfC V) (GlobalTheory.UnitarySplit.real_finite_split D V).1 q.1).imp fun k hk => ?_
  have e0 : finHom V k = q.1.1 := congrArg Subtype.val hk.2
  have e1 : finE V k = Formalism.UG.bc (swapAE D) q.1.1 := (finE_eq V k).trans (congrArg (Formalism.UG.bc (swapAE D)) e0)
  have e2 : (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl
  have hc : levChi V β (flagL L) k = (((levEnv V β L).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans e2.symm)
  have h1 : Formalism.UG.bc (swapAE D) q.1.1 ∈ lev D.sp.cm V.gram β (flagL L) := q.2
  have hp : finE V k ∈ parLev D.sp.cm V.gram β L := e1.symm ▸ h1.1
  exact ⟨hk.2, ⟨hk.1, hp, congrArg (rTup β L) e1⟩, (Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hc.symm)⟩

theorem act_eq_translate : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_red_R → R.models_jX → ∀ t (g : G) (x : (A.fam.R t).S.Forms), ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ ∧ ∀ h, (R.HX t).e (R.jX t ((A.fam.R t).r g x)) h = (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ • (R.HX t).e (R.jX t x) (h * (finHom _).rangeRestrict κ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hred hj t g x
  refine ((R.B.R t).act_tie.red_surj g).elim fun q hq => ?_
  have hg : rTup R.βX (R.datXt t) (Formalism.UG.bc (swapAE D) q.1.1) = R.eG g := (hred t q).symm.trans (congrArg R.eG hq)
  have ha := (R.B.R t).act_tie.act_eq g q hq x
  refine (exists_lift D.sp.X' R.βX (R.datXt t) q).imp fun κ hκ => ⟨hg ▸ hκ.2.1, fun h => ?_⟩
  have e1 := congrFun (hj t ((A.fam.R t).r g x)) h
  have e2 := hj t x
  have e3 := congrFun ha h
  refine (e1.trans e3).trans ?_
  exact congrArg₂ (fun (a : ℂ) (z : R.cX.W) => a • z) hκ.2.2 ((congrFun e2 _).trans (congrArg (fun z => R.B.jR t x (h * z)) hκ.1)).symm

end GlobalTheory.FormAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AverageDetCharMonomialEqSumProdMinors
section
noncomputable section

open Classical MeasureTheory MvPolynomial

namespace GlobalTheory.MinorFrame.AvgCore

variable {ι : Type} [Fintype ι] {a d : ℕ}

theorem continuous_colSub_mul (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) : ∀ Q : Pol ι d a,
    Continuous (fun G : ι → Fin a → Fin a → ℂ => Λ (colSub (fun τ => Matrix.of (G τ)) P * Q)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, colSub (d := d) (fun τ => Matrix.of (G τ)) (C c) = C c := by
      intro G; simp [colSub, MvPolynomial.algebraMap_eq]
    simp only [h]
    exact continuous_const
  | add p q hp hq =>
    intro Q
    simp only [map_add (f := _), add_mul]
    exact (hp Q).add (hq Q)
  | mul_X p y hp =>
    intro Q
    have h : ∀ G : ι → Fin a → Fin a → ℂ, Λ (colSub (fun τ => Matrix.of (G τ)) (p * X y) * Q) =
        ∑ j' : Fin a, G y.1 j' y.2.2 * Λ (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j') * Q)) := by
      intro G
      have hX : colSub (d := d) (fun τ => Matrix.of (G τ)) (X y) =
          ∑ j' : Fin a, C (G y.1 j' y.2.2) * X (y.1, y.2.1, j') := by
        simp [colSub]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul (colSub (fun τ => Matrix.of (G τ))) p (X y), hX, Finset.mul_sum, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show colSub (fun τ => Matrix.of (G τ)) p * (C (G y.1 j y.2.2) * X (y.1, y.2.1, j)) * Q =
          C (G y.1 j y.2.2) * (colSub (fun τ => Matrix.of (G τ)) p * (X (y.1, y.2.1, j) * Q)) by ring,
        ← smul_eq_C_mul, map_smul, smul_eq_mul]
    simp only [h]
    refine continuous_finsetSum _ fun j _ => ?_
    exact Continuous.mul (by fun_prop) (hp _)

theorem norm_det_unitary (u : Matrix.unitaryGroup (Fin a) ℂ) : ‖(u : Matrix (Fin a) (Fin a) ℂ).det‖ = 1 := by
  exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary u.2)

theorem integrable_avg {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ))
    (hmeas : ∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) (z : ι → ℤ)
    (Λ : Pol ι d a →ₗ[ℂ] ℂ) (P : Pol ι d a) :
    Integrable (fun g => (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (z τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P)) ν := by
  let F : (ι → Fin a → Fin a → ℂ) → ℂ := fun G => Λ (colSub (fun τ => Matrix.of (G τ)) P)
  have hF : Continuous F := by simpa [F] using continuous_colSub_mul Λ P 1
  let e : K → (ι → Fin a → Fin a → ℂ) := fun g τ i j => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j
  have he : Measurable e := Measurable.of_eval fun τ => Measurable.of_eval fun i =>
    Measurable.of_eval fun j => hmeas τ i j
  have hFe : ∀ g, Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) P) = F (e g) := fun g => rfl
  have hdetc : ∀ τ, Continuous fun G : ι → Fin a → Fin a → ℂ => (Matrix.of (G τ)).det :=
    fun τ => Continuous.matrix_det (continuous_apply τ)
  have hdete : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det = (Matrix.of (e g τ)).det := fun g τ => rfl
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ι → Fin a → Fin a → ℂ) 1).exists_bound_of_continuousOn hF.continuousOn
  have hball : ∀ g, e g ∈ Metric.closedBall (0 : ι → Fin a → Fin a → ℂ) 1 := by
    intro g
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => entry_norm_bound_of_unitary (ρ g τ).2 i j
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun g => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    simp only [hFe, hdete]
    refine Measurable.mul ?_ (hF.measurable.comp he)
    refine Finset.measurable_prod _ fun τ _ => ?_
    exact Measurable.pow_const ((hdetc τ).measurable.comp he) _
  · rw [norm_mul, norm_prod]
    simp only [norm_zpow, norm_det_unitary, one_zpow, Finset.prod_const_one, one_mul, hFe]
    exact hC _ (hball g)

theorem average_monomial_eq_sum_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ), ∃ n : ι → ℕ,
  ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  (∀ g0 : K, AEMeasurable (g0 * ·) ν) →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) → Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℂ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), (∀ p, IsAlgebraic ℚ (r p)) ∧
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) ∂ν =
    ∑ p, r p * Λ (GlobalTheory.MinorFrame.prodMinors (U p)) := by
  intro ι _ a d m
  refine ⟨fun τ => (-m τ).toNat, ?_⟩
  intro K _ _ ν hP hInv hleft ρ hmeas hsurj Λ k
  haveI := hP
  by_cases hpos : 0 < a ∧ ∃ τ₀, 0 < m τ₀
  · obtain ⟨ha, τ₀, hτ₀⟩ := hpos
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, ?_⟩
    rw [GlobalTheory.T.integral_detCharacter_fockColumnSubstitution_eq_zero a d m τ₀ ha hτ₀ ν hP hInv hleft ρ hmeas hsurj Λ _]
    simp
  obtain ⟨M, r, U, hR⟩ := _root_.GlobalTheory.MinorFrame.RatProj.exists_rat_proj (ι := ι) a d (fun τ => (-m τ).toNat) k
  refine ⟨M, fun p => ((r p : ℚ) : ℂ), U, fun p => isAlgebraic_ratCast ℚ (r p), ?_⟩
  set R : Pol ι d a := MvPolynomial.monomial k 1 - ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) with hRdef
  have hperp : ∀ I ∈ inv a d (fun τ => (-m τ).toNat), Formalism.L2.DIV.fockS I R = 0 := by
    intro I hI
    have hspan := GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors a d (fun τ => (-m τ).toNat) hI
    clear hI
    show Formalism.L2.DIV.fockL I R = 0
    induction hspan using Submodule.span_induction with
    | mem x hx => obtain ⟨T, rfl⟩ := hx; exact hR T
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]
  have h0 := _root_.GlobalTheory.UnitaryAvg.avg_perp a d (fun τ => (-m τ).toNat) ν hP hInv hleft ρ hmeas hsurj Λ R hperp
  have hdet0 : ∀ g τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 := fun g τ => by
    rw [← norm_ne_zero_iff, norm_det_unitary]; exact one_ne_zero
  have hD : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) =
      ∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ)) := by
    intro g
    refine Finset.prod_congr rfl fun τ _ => ?_
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.det_fin_zero]
    · have hm : m τ ≤ 0 := by
        by_contra h
        exact hpos ⟨ha, τ, by omega⟩
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
  have hinv : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
      detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
    intro g
    unfold detChar
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (hdet0 g τ))]
  have hmono : MvPolynomial.monomial k 1 = ∑ p, ((r p : ℚ) : ℂ) • prodMinors (U p) + R := by
    rw [hRdef]; abel
  have hpoint : ∀ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) =
      ∑ p, ((r p : ℚ) : ℂ) * Λ (prodMinors (U p)) +
        (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          Λ (colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) R) := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hD g, hmono, map_add (f := _), map_sum, map_add (f := _), map_sum, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_smul, colSub_prodMinors, smul_smul, map_smul, smul_eq_mul]
    rw [show (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
        ((((r p : ℚ) : ℂ) * detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          Λ (prodMinors (U p))) =
        ((∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (-(((-m τ).toNat : ℕ) : ℤ))) *
          detChar (fun τ => (-m τ).toNat) (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ))) *
          (((r p : ℚ) : ℂ) * Λ (prodMinors (U p))) by ring, hinv g, one_mul]
  refine (integral_congr_ae (Filter.Eventually.of_forall hpoint)).trans ?_
  rw [integral_add (integrable_const _) (integrable_avg ν ρ hmeas _ Λ R), integral_const, h0]
  simp

end GlobalTheory.MinorFrame.AvgCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseChangeThetaLiftSatakeParameterEqAddSegment
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

private theorem multiset_range_map_eq_sum_singleton (f : ℕ → ℂˣ) (N : ℕ) :
    (Multiset.range N).map f = ∑ j ∈ Finset.range N, ({f j} : Multiset ℂˣ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ← ih, add_comm, Multiset.singleton_add]

theorem str_eq_sum (q : ℂˣ) (t : ℤ) :
    str q t = ∑ j ∈ Finset.range t.toNat, ({q ^ (2 * (j : ℤ) - (t - 1))} : Multiset ℂˣ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str]
  exact multiset_range_map_eq_sum_singleton _ _

theorem str_even (q : ℂˣ) (d : ℕ) (t : ℤ) (ht : t = 2 * d) :
    str q t = ∑ k ∈ Finset.range d, ({q ^ (t - 1 - 2 * (k : ℤ)), q ^ (-(t - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) := by
  rw [str_eq_sum, show t.toNat = d + d by omega, Finset.sum_range_add]
  conv_lhs => arg 2; rw [← Finset.sum_range_reflect]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < d := Finset.mem_range.mp hk
  rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
  congr 3 <;> omega

theorem str_odd (q : ℂˣ) (d : ℕ) (t : ℤ) (ht : t = 2 * d + 1) :
    str q t = ∑ k ∈ Finset.range d, ({q ^ (t - 1 - 2 * (k : ℤ)), q ^ (-(t - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) + {1} := by
  rw [str_eq_sum, show t.toNat = d + (d + 1) by omega, Finset.sum_range_add, Finset.sum_range_succ']
  conv_lhs => arg 2; arg 1; rw [← Finset.sum_range_reflect]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < d := Finset.mem_range.mp hk
    rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
    congr 3 <;> omega
  · rw [← zpow_zero q]
    congr 2
    omega

theorem lift_key (q : ℂˣ) (n n' : ℕ) (h : n ≤ n') :
    ∑ k ∈ Finset.range (n' / 2 - n / 2),
        ({q ^ ((n' : ℤ) - n - 1 - 2 * (k : ℤ)), q ^ (-((n' : ℤ) - n - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) +
      Multiset.replicate (n' % 2) ((-1 : ℂˣ) ^ n)⁻¹ =
    Multiset.replicate (n % 2) ((-1 : ℂˣ) ^ n')⁻¹ + str q ((n' : ℤ) - n) := by
  have hsq : ∀ m : ℕ, (-1 : ℂˣ) ^ (2 * m) = 1 := fun m => by rw [pow_mul, neg_one_sq, one_pow]
  rcases Nat.even_or_odd' n with ⟨a, rfl | rfl⟩ <;> rcases Nat.even_or_odd' n' with ⟨b, rfl | rfl⟩
  · rw [str_even q (b - a) _ (by omega), show 2 * b / 2 - 2 * a / 2 = b - a by omega,
      show 2 * b % 2 = 0 by omega, show 2 * a % 2 = 0 by omega]
    simp only [Multiset.replicate_zero, add_zero, zero_add]
  · rw [str_odd q (b - a) _ (by omega), show (2 * b + 1) / 2 - 2 * a / 2 = b - a by omega,
      show (2 * b + 1) % 2 = 1 by omega, show 2 * a % 2 = 0 by omega, hsq, inv_one]
    simp only [Multiset.replicate_zero, Multiset.replicate_one, zero_add]
  · have e0 : ((2 * b : ℕ) : ℤ) - ((2 * a + 1 : ℕ) : ℤ) - 1 - 2 * ((b - a - 1 : ℕ) : ℤ) = 0 := by omega
    rw [str_odd q (b - a - 1) _ (by omega), show 2 * b / 2 - (2 * a + 1) / 2 = b - a - 1 + 1 by omega,
      Finset.sum_range_succ, e0, neg_zero, zpow_zero,
      show 2 * b % 2 = 0 by omega, show (2 * a + 1) % 2 = 1 by omega, hsq, inv_one]
    simp only [Multiset.replicate_zero, Multiset.replicate_one, add_zero, Multiset.insert_eq_cons,
      ← Multiset.singleton_add]
    abel
  · have hodd : ∀ m : ℕ, (-1 : ℂˣ) ^ (2 * m + 1) = -1 := fun m => by rw [pow_succ, hsq, one_mul]
    rw [str_even q (b - a) _ (by omega), show (2 * b + 1) / 2 - (2 * a + 1) / 2 = b - a by omega,
      show (2 * b + 1) % 2 = 1 by omega, show (2 * a + 1) % 2 = 1 by omega, hodd, hodd, add_comm]

private theorem sum_pi_single_one_smul {ι : Type} (s : Finset ι) (f : ι → ℂˣ) :
    ∑ i ∈ s, ({f i} : Multiset ℂˣ) = s.val.map f := by
  rw [Finset.sum_eq_multiset_sum]
  generalize s.val = m
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons, Multiset.singleton_add]


open GlobalTheory.LGrp (bcParam) in
theorem bcParam_map_mul (c : ℂˣ) (N : ℕ) (γ : Fin (N / 2) → ℂˣ) :
    (bcParam N γ).map (fun x => c * x) =
      ∑ i, ({c * γ i, c * (γ i)⁻¹} : Multiset ℂˣ) + Multiset.replicate (N % 2) c := by
  have hpair : ∀ i, ({c * γ i, c * (γ i)⁻¹} : Multiset ℂˣ) = {c * γ i} + {c * (γ i)⁻¹} := fun i => by
    rw [Multiset.insert_eq_cons, Multiset.singleton_add]
  simp only [hpair, Finset.sum_add_distrib, sum_pi_single_one_smul, bcParam, Multiset.map_add (f := _), Multiset.map_map,
    Multiset.map_replicate, mul_one]
  rfl

theorem neg_one_pow_inv (k : ℕ) : ((-1 : ℂˣ) ^ k)⁻¹ = (-1) ^ k := by rw [← inv_pow, inv_neg_one]

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂˣ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem pair_inv_mul_eq_of_mul_self_eq_one (s t a : ℂˣ) (hs : s * s = 1) (ht : t * t = 1) :
    ({s⁻¹ * (s * t * a⁻¹), s⁻¹ * (s * t * a⁻¹)⁻¹} : Multiset ℂˣ) = {t⁻¹ * a, t⁻¹ * a⁻¹} := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have e1 : s⁻¹ * (s * t * a⁻¹) = t⁻¹ * a⁻¹ := by rw [mul_assoc, inv_mul_cancel_left, ht']
  have e2 : s⁻¹ * (s * t * a⁻¹)⁻¹ = t⁻¹ * a := by
    simp only [mul_inv, inv_inv]
    rw [hs', ← mul_assoc, ← mul_assoc, hs, one_mul]
  rw [e1, e2, Multiset.pair_comm]

theorem bcParam_liftPar (q : ℂˣ) (n n' : ℕ) (h : n ≤ n') (α : Fin (n / 2) → ℂˣ) :
    (bcParam n' (liftPar q n n' α)).map (fun x => ((-1 : ℂˣ) ^ n)⁻¹ * x) =
      (bcParam n α).map (fun x => ((-1 : ℂˣ) ^ n')⁻¹ * x) + str q ((n' : ℤ) - n) := by
  have hD : n' / 2 - n / 2 + n / 2 = n' / 2 := by omega
  have hs : (-1 : ℂˣ) ^ n * (-1) ^ n = 1 := neg_one_pow_mul_self n
  have hsum : (∑ i : Fin (n' / 2), ({((-1 : ℂˣ) ^ n)⁻¹ * liftPar q n n' α i,
        ((-1 : ℂˣ) ^ n)⁻¹ * (liftPar q n n' α i)⁻¹} : Multiset ℂˣ)) =
      ∑ k ∈ Finset.range (n' / 2 - n / 2),
        ({q ^ ((n' : ℤ) - n - 1 - 2 * (k : ℤ)), q ^ (-((n' : ℤ) - n - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) +
      ∑ i : Fin (n / 2), ({((-1 : ℂˣ) ^ n')⁻¹ * α i, ((-1 : ℂˣ) ^ n')⁻¹ * (α i)⁻¹} : Multiset ℂˣ) := by
    rw [← Equiv.sum_comp (finCongr hD), Fin.sum_univ_add, ← Fin.sum_univ_eq_sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hL : liftPar q n n' α (finCongr hD (Fin.castAdd (n / 2) i)) =
          (-1) ^ n * q ^ ((n' : ℤ) - n - 1 - 2 * ((i : ℕ) : ℤ)) := by
        unfold liftPar
        rw [dite_eq_left (by simp)]
        simp
      rw [hL, mul_inv, inv_mul_cancel_left, neg_one_pow_inv, ← mul_assoc, hs, one_mul, ← _root_.zpow_neg]
    · refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
      have hL : liftPar q n n' α (finCongr hD (Fin.natAdd (n' / 2 - n / 2) j)) =
          (-1) ^ n * (-1) ^ n' * (α (Fin.revPerm j))⁻¹ := by
        unfold liftPar
        rw [dite_eq_right (by simp), pow_add]
        congr 3
        ext
        simp
        omega
      rw [hL]
      exact pair_inv_mul_eq_of_mul_self_eq_one _ _ _ hs (neg_one_pow_mul_self n')
  rw [bcParam_map_mul, bcParam_map_mul, hsum, add_assoc _ (Multiset.replicate (n % 2) _), ← lift_key q n n' h]
  abel

end GlobalTheory.SphTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CayleyUnitaryTorusInvDetIntegralOrder
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CayleyTorus

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_one_add_inv_unif {ϖ : L}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (1 + ϖ⁻¹) = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h1 : Valued.v (ϖ⁻¹) = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_inv₀, hv]; rfl
  rw [Valuation.map_add_eq_of_lt_right, h1]
  rw [h1, map_one]; exact WithZero.coe_lt_coe.2 (by decide)

theorem v_one_add_unif {ϖ : L}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (1 + ϖ) = 1 := by
  rw [Valuation.map_add_eq_of_lt_left, map_one]
  rw [hv, map_one]; exact WithZero.coe_lt_coe.2 (by decide)

theorem inv_diagonal_field {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → L) (hf : ∀ i, f i ≠ 0) :
    (Matrix.diagonal f)⁻¹ = Matrix.diagonal (fun i => (f i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i; exact inv_mul_cancel₀ (hf i)

theorem cayley_torus_inv : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → ∀ (n' : ℕ) (k : Fin (n' / 2)) (t : GU σ n'), t.1.1 = tMat ϖ n' (n' / 2) (Pi.single k 1) → (1 + (t⁻¹).1.1).det ≠ 0 ∧ (1 + (t⁻¹).1.1)⁻¹ ∈ intMat L (Fin n') (Fin n') ∧ ordL (1 + (t⁻¹).1.1).det = -1 := by
  intro L _ _ ϖ σ q hU h2 n' k t ht
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    hU.2.2.2.1
  have hϖ : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  set d : Fin n' → L := fun i => if h : i.val < n' / 2 then ϖ ^ ((Pi.single k (1 : ℤ) : Fin (n' / 2) → ℤ) ⟨i.val, h⟩)
    else if h' : n' - n' / 2 ≤ i.val ∧ n' - 1 - i.val < n' / 2 then
      ϖ ^ (-((Pi.single k (1 : ℤ) : Fin (n' / 2) → ℤ) ⟨n' - 1 - i.val, h'.2⟩)) else 1 with hd
  have htd : t.1.1 = Matrix.diagonal d := ht
  have hdne : ∀ i, d i ≠ 0 := by
    intro i; simp only [hd]; split_ifs <;> simp [zpow_ne_zero, hϖ]
  have hinv : (t⁻¹).1.1 = Matrix.diagonal (fun i => (d i)⁻¹) := by
    rw [show (t⁻¹).1.1 = (t.1.1)⁻¹ by simp [Matrix.coe_units_inv], htd, inv_diagonal_field d hdne]
  have hone : 1 + (t⁻¹).1.1 = Matrix.diagonal (fun i => 1 + (d i)⁻¹) := by
    rw [hinv, ← Matrix.diagonal_one, Matrix.diagonal_add]
  have hk : k.val < n' := by omega
  have hval : ∀ i, Valued.v (1 + (d i)⁻¹) =
      if i = ⟨k.val, hk⟩ then ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) else 1 := by
    intro i
    by_cases hi : i.val < n' / 2
    · by_cases hik : (⟨i.val, hi⟩ : Fin (n' / 2)) = k
      · have : d i = ϖ := by simp only [hd, dif_pos hi, hik, Pi.single_eq_same, zpow_one]
        rw [this, v_one_add_inv_unif hv, if_pos (show i = ⟨k.val, hk⟩ from Fin.ext (by have e := congrArg Fin.val hik; simpa using e))]
      · have : d i = 1 := by simp only [hd, dif_pos hi, Pi.single_eq_of_ne hik, zpow_zero]
        rw [this, inv_one, one_add_one_eq_two, h2, if_neg]
        intro e; apply hik; ext; simp [e]
    · rw [if_neg (fun e => hi (by rw [e]; exact k.2))]
      by_cases h' : n' - n' / 2 ≤ i.val ∧ n' - 1 - i.val < n' / 2
      · by_cases hik : (⟨n' - 1 - i.val, h'.2⟩ : Fin (n' / 2)) = k
        · have : d i = ϖ⁻¹ := by simp only [hd, dif_neg hi, dif_pos h', hik, Pi.single_eq_same, _root_.zpow_neg, zpow_one]
          rw [this, inv_inv, v_one_add_unif hv]
        · have : d i = 1 := by simp only [hd, dif_neg hi, dif_pos h', Pi.single_eq_of_ne hik, neg_zero, zpow_zero]
          rw [this, inv_one, one_add_one_eq_two, h2]
      · have : d i = 1 := by simp only [hd, dif_neg hi, dif_neg h']
        rw [this, inv_one, one_add_one_eq_two, h2]
  have hfne : ∀ i, 1 + (d i)⁻¹ ≠ 0 := by
    intro i e
    have := hval i
    rw [e, map_zero] at this
    split_ifs at this with h
    · exact WithZero.zero_ne_coe this
    · exact zero_ne_one this
  have hdet : Valued.v (1 + (t⁻¹).1.1).det =
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [hone, Matrix.det_diagonal, map_prod]
    simp_rw [hval]
    rw [Finset.prod_ite_eq']; simp
  refine ⟨?_, ?_, ?_⟩
  · intro e; rw [e, map_zero] at hdet; exact WithZero.zero_ne_coe hdet
  · rw [hone, inv_diagonal_field _ hfne]
    intro i j
    rw [mem_intL, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [map_inv₀, hval i]
      split_ifs
      · rw [← WithZero.coe_inv]; exact WithZero.coe_le_coe.2 (by decide)
      · simp
    · simp
  · have hne : Valued.v (1 + (t⁻¹).1.1).det ≠ 0 := by rw [hdet]; exact WithZero.coe_ne_zero
    have hu : WithZero.unzero hne = Multiplicative.ofAdd (1 : ℤ) :=
      WithZero.coe_inj.mp ((WithZero.coe_unzero hne).trans hdet)
    rw [ordL, dif_neg hne, hu]; rfl

end GlobalTheory.CayleyTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTensorEquivLeviCharacter
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL.Exponents

theorem nonempty_piTensor_detRep_equiv (R β : Type) [CommRing R] [Fintype β] (c : β → Type)
    [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) :
    Nonempty ((piTensor fun j => detRep (c j) (χ j)).Equiv (ofChar (leviChar c χ))) := by
  classical
  refine ⟨LocGL.equivOfBijective
    ⟨(PiTensorProduct.constantBaseRingEquiv β ℂ).toLinearMap, fun g => ?_⟩
    (PiTensorProduct.constantBaseRingEquiv β ℂ).bijective⟩
  ext x
  simp [leviChar_apply, detRep, Finset.prod_mul_distrib]

end GlobalTheory.SmGL.Exponents
end
end

