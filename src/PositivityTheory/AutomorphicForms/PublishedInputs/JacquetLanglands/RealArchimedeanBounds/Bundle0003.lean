module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UopSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DProdP
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HeightProductFormula

theorem reAt_eq {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = sg v x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

theorem rowF_apply {F : Type} [Field F] [NumberField F] (s : Fin 2 → F) (x : GF F) (i : Fin 2) :
    rowF s x i = algebraMap F (Af F) (s 0) * x.val 0 i + algebraMap F (Af F) (s 1) * x.val 1 i := by
  simp [rowF, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem det_id {F : Type} [Field F] [NumberField F] (s s' : Fin 2 → F) (x : GF F) :
    algebraMap F (Af F) (s 0 * s' 1 - s 1 * s' 0) * (Matrix.GeneralLinearGroup.det x : Af F) =
      rowF s x 0 * rowF s' x 1 - rowF s x 1 * rowF s' x 0 := by
  rw [rowF_apply, rowF_apply, rowF_apply, rowF_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [map_sub, map_mul]
  ring

end UpperTheory.Esk.HeightProductFormula

namespace UpperTheory.Esk

open HeightProductFormula in
theorem dProd : AMem → AMono → ARow → DProd := by
  intro hM hMo hR F _ _ _ c _ χ s s' hΔ x
  obtain ⟨hpos, hmul, -, hprod⟩ := UpperTheory.V.Sd.Hm.absf F
  have hs : s ≠ 0 := fun h => hΔ (by simp [h])
  have hs' : s' ≠ 0 := fun h => hΔ (by simp [h])
  obtain ⟨t, k, hk, ht⟩ := (hR F s x).1 hs
  obtain ⟨t', k', hk', ht'⟩ := (hR F s' x).1 hs'
  have hn : nF s x = absF t := (hR F s x).2 t k hk ht
  have hn' : nF s' x = absF t' := (hR F s' x).2 t' k' hk' ht'
  obtain ⟨hK, hO, -⟩ := hM F
  have hle : ∀ (g : GF F), g ∈ K0 F → ∀ i j (w : Pl F), Valued.v (pLoc F w (g.val i j)) ≤ 1 :=
    fun g hg i j w => (hO _).1 (((hK g).1 hg).1 i j) w
  set Δ := s 0 * s' 1 - s 1 * s' 0 with hΔd
  set U1 : (Af F)ˣ := ratU F (Units.mk0 Δ hΔ) * Matrix.GeneralLinearGroup.det x
  have key : absF U1 ≤ absF (t * t') := by
    refine hMo F _ _ fun w => ?_
    have e : (U1 : Af F) = (t * t' : (Af F)ˣ) * (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0) := by
      change algebraMap F (Af F) Δ * (Matrix.GeneralLinearGroup.det x : Af F) = _
      rw [det_id, ht, ht, ht', ht', Units.val_mul]
      ring
    rw [e, map_mul, map_mul]
    have h1 : Valued.v (pLoc F w (k.val 1 0 * k'.val 1 1 - k.val 1 1 * k'.val 1 0)) ≤ 1 := by
      rw [map_sub, map_mul, map_mul]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 0 w) (hle k' hk' 1 1 w)
      · rw [map_mul]; exact mul_le_one' (hle k hk 1 1 w) (hle k' hk' 1 0 w)
    calc _ ≤ Valued.v (pLoc F w ((t * t' : (Af F)ˣ) : Af F)) * 1 := mul_le_mul_right h1 _
      _ = _ := mul_one _
  have hU1 : absF U1 = absF (ratU F (Units.mk0 Δ hΔ)) * absF (Matrix.GeneralLinearGroup.det x) := hmul _ _
  have hP := hprod (Units.mk0 Δ hΔ)
  change (∏ v, |reAt v Δ|) * absF (ratU F (Units.mk0 Δ hΔ)) = 1 at hP
  simp only [reAt_eq] at hP
  change absF (Matrix.GeneralLinearGroup.det x) / nF s x ^ 2 * (absF (Matrix.GeneralLinearGroup.det x) / nF s' x ^ 2) ≤
    ∏ v, sg v Δ ^ 2
  rw [hn, hn']
  have hsq : ∏ v, sg v Δ ^ 2 = (∏ v, |sg v Δ|) ^ 2 := by
    rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun v _ => (sq_abs _).symm
  rw [hsq]
  set P := ∏ v, |sg v Δ|
  set R := absF (ratU F (Units.mk0 Δ hΔ))
  set A := absF (Matrix.GeneralLinearGroup.det x)
  have hA := hpos (Matrix.GeneralLinearGroup.det x)
  have hT := hpos t
  have hT' := hpos t'
  have hRp := hpos (ratU F (Units.mk0 Δ hΔ))
  have hPp : 0 ≤ P := Finset.prod_nonneg fun v _ => abs_nonneg _
  rw [hU1, hmul t t'] at key
  have hA2 : A ≤ absF t * absF t' * P := by
    have : A = P * (R * A) := by rw [← mul_assoc, hP, one_mul]
    rw [this, mul_comm (absF t * absF t') P]
    exact mul_le_mul_of_nonneg_left key hPp
  rw [div_mul_div_comm, div_le_iff₀ (by positivity), ← sq, ← mul_pow, ← mul_pow]
  exact pow_le_pow_left₀ hA.le (by linarith) 2

end UpperTheory.Esk
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DRepsP
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.DeterminantRepresentatives

variable {F : Type} [Field F] [NumberField F]

theorem norm_one' {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 := by
  have := (Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le
  have h2 := (Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge
  exact le_antisymm this h2

theorem fin_supp (y : (Af F)ˣ) : Function.HasFiniteMulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖ := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (norm_one' (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

theorem absF_mul (y z : (Af F)ˣ) : absF (y * z) = absF y * absF z := by
  unfold absF
  rw [← finprod_mul_distrib (fin_supp y) (fin_supp z)]
  simp

theorem aff_mul {R : Type} [CommRing R] (y z : Rˣ) (x t : R) : aff y x * aff z t = aff (y * z) (x + y * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

@[simp] theorem aff_one {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

theorem det_aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : Matrix.GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, aff, Matrix.det_fin_two_of]

theorem det_centralSection {R : Type} [CommRing R] (y : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) y * (aff y 0)⁻¹) = y := by
  rw [map_mul, map_inv, det_aff]
  ext
  simp [pow_two]

theorem pLoc_det (v : Pl F) (g : GF F) : pLoc F v ((Matrix.GeneralLinearGroup.det g : (Af F)ˣ) : Af F) =
    ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (pLoc F v) g) : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]

theorem absF_loc (w : Pl F) (g : GL (Fin 2) (w.adicCompletion F))
    (hg : Matrix.GeneralLinearGroup.det g = atFin w (unif w)) :
    absF (Matrix.GeneralLinearGroup.det (locGL F 2 w g)) = (normV w : ℝ)⁻¹ := by
  rw [absF, finprod_eq_single _ w fun v hv => by rw [pLoc_det, pLoc_locGL_of_ne hv]; simp, pLoc_det, pLoc_locGL, hg,
    FinitePlace.norm_def, unif_spec, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]

  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem step {c : Pl F → ℕ} {w : Pl F} {W : List (Pl F)} {ι κ : Type} [Fintype ι] [Fintype κ] {b : ι → GF F}
    (hb : IsReps c W b) (r : κ → GL (Fin 2) (w.adicCompletion F))
    (hr1 : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V),
      ∀ x ∈ Hi.fixd ρ (K1 w (c w)), Uop w ρ (c w) x = ∑ j, ρ (r j) x)
    (hr2 : ∀ j, Matrix.GeneralLinearGroup.det (r j) = atFin w (unif w))
    (hr3 : c w ≠ 0 → ∀ j, ∃ u : w.adicCompletionIntegers F, r j = aff (atFin w (unif w)) (u : w.adicCompletion F)) :
    IsReps c (w :: W) (fun p : κ × ι => locGL F 2 w (r p.1) * b p.2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ ρ x hx
    obtain ⟨hy, he⟩ := hb.act V ρ x hx
    have hy' : (∑ i, ρ (b i) x) ∈ Hi.fixd (ρ.comp (locGL F 2 w)) (K1 w (c w)) :=
      fun k hk => hy _ ((kcTop F).2.2.2.2.2 c w k hk)
    have hs : ∑ p : κ × ι, ρ (locGL F 2 w (r p.1) * b p.2) x =
        Uop w (ρ.comp (locGL F 2 w)) (c w) (∑ i, ρ (b i) x) := by
      rw [hr1 V (ρ.comp (locGL F 2 w)) _ hy', Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, Module.End.mul_apply]
      rfl
    rw [hs]
    refine ⟨(hkComm (hkReps uopSum) kcTop F V ρ c _ hy w).1, ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ← he]
  · intro p
    rw [map_mul, absF_mul, absF_loc w _ (hr2 p.1), hb.det, List.map_cons, List.prod_cons]
  · intro p w' hw'
    classical
    obtain ⟨u', hu'⟩ := hb.loc p.2 w' hw'
    rw [map_mul]
    by_cases h : w' = w
    · subst h
      obtain ⟨u, hu⟩ := hr3 hw' p.1
      have hm : ((atFin w' (unif w') : (w'.adicCompletion F)ˣ) : w'.adicCompletion F) ∈ w'.adicCompletionIntegers F := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, unif_spec, ← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      refine ⟨u + ⟨_, hm⟩ * u', ?_⟩
      rw [pLoc_locGL, hu, hu', aff_mul, List.count_cons_self, pow_succ']
      push_cast
      rfl
    · refine ⟨u', ?_⟩
      rw [pLoc_locGL_of_ne h, one_mul, hu']
      simp [List.count_cons, Ne.symm h]

theorem base (c : Pl F → ℕ) : IsReps c ([] : List (Pl F)) (fun _ : Unit => (1 : GF F)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ ρ x hx
    simpa using hx
  · intro i
    simp [absF]
  · intro i w hw
    exact ⟨0, by simp⟩

theorem reindex {c : Pl F → ℕ} {W : List (Pl F)} {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) {a : ι → GF F}
    (h : IsReps c W a) : IsReps c W (a ∘ e) := by
  refine ⟨?_, fun i => h.det (e i), fun i => h.loc (e i)⟩
  intro V _ _ ρ x hx
  rw [show ∑ i, ρ ((a ∘ e) i) x = ∑ i, ρ (a i) x from Equiv.sum_comp e (fun i => ρ (a i) x)]
  exact h.act V ρ x hx

theorem ex (c : Pl F → ℕ) (W : List (Pl F)) : ∃ (ι : Type) (_ : Fintype ι) (a : ι → GF F), IsReps c W a := by
  induction W with
  | nil => exact ⟨Unit, inferInstance, _, base c⟩
  | cons w W ih =>
    obtain ⟨ι, _, b, hb⟩ := ih
    classical
    haveI := Formalism.UG.P.glint_finite_residueField w
    letI := Fintype.ofFinite (IsLocalRing.ResidueField (w.adicCompletionIntegers F))
    choose s hs using (IsLocalRing.residue_surjective (R := w.adicCompletionIntegers F))
    have hS : Set.BijOn (IsLocalRing.residue (w.adicCompletionIntegers F))
        ((Finset.univ.image s : Finset (w.adicCompletionIntegers F)) : Set (w.adicCompletionIntegers F)) Set.univ := by
      refine ⟨fun _ _ => Set.mem_univ _, ?_, fun r _ => ⟨s r, by simp, hs r⟩⟩
      intro x hx y hy h
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      obtain ⟨r', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      rw [hs, hs] at h
      rw [h]
    generalize Finset.univ.image s = S at hS
    by_cases hc : c w = 0
    · refine ⟨Option S × ι, inferInstance, _, step hb (fun o => o.elim
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w)) * (aff (atFin w (unif w)) 0)⁻¹)
        (fun u => aff (atFin w (unif w)) ((u : w.adicCompletionIntegers F) : w.adicCompletion F))) ?_ ?_ ?_⟩
      · intro V _ _ ρ x hx
        rw [(uopSum F w V ρ (c w) x hx).2 S hS, if_pos hc, Fintype.sum_option, add_comm, ← Finset.sum_coe_sort S]
        rfl
      · intro j
        cases j with
        | none => exact det_centralSection _
        | some u => exact det_aff _ _
      · exact fun h => absurd hc h
    · refine ⟨S × ι, inferInstance, _, step hb (fun u : S => aff (atFin w (unif w))
        ((u : w.adicCompletionIntegers F) : w.adicCompletion F)) ?_ (fun _ => det_aff _ _) (fun _ u => ⟨u, rfl⟩)⟩
      intro V _ _ ρ x hx
      rw [(uopSum F w V ρ (c w) x hx).2 S hS, if_neg hc, add_zero, ← Finset.sum_coe_sort S]

end UpperTheory.Esk.DeterminantRepresentatives

open UpperTheory.Esk.DeterminantRepresentatives in
theorem UpperTheory.Esk.dReps : UpperTheory.Esk.DReps := by
  intro F _ _ c W
  obtain ⟨ι, _, a, ha⟩ := ex c W
  exact ⟨Fintype.card ι, a ∘ (Fintype.equivFin ι).symm, reindex _ ha⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DScaleP
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.CentralScalingLemmas

def cb (K P1 P2 : ℝ) (n : ℕ) : ℝ := max (max 1 (K ^ n * P2)) (min 1 (P1 / K ^ n))⁻¹

theorem cb_pos (K P1 P2 : ℝ) (n : ℕ) : 0 < cb K P1 P2 n :=
  lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _))

theorem bal {ι : Type} [Fintype ι] [Nonempty ι] (a : ι → ℝ) {K P1 P2 : ℝ} (hK : 0 < K) (hP1 : 0 < P1)
    (ha : ∀ v, 0 < a v) (hb : ∀ v v', a v ≤ K * a v') (h1 : P1 ≤ ∏ v, a v) (h2 : ∏ v, a v ≤ P2) (v : ι) :
    (cb K P1 P2 (Fintype.card ι))⁻¹ ≤ a v ∧ a v ≤ cb K P1 P2 (Fintype.card ι) := by
  have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hKn : 0 < K ^ Fintype.card ι := pow_pos hK _
  have hup : a v ^ Fintype.card ι ≤ K ^ Fintype.card ι * P2 := by
    calc a v ^ Fintype.card ι = ∏ _v' : ι, a v := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ ∏ v' : ι, K * a v' := Finset.prod_le_prod₀ (fun _ _ => (ha v).le) fun v' _ => hb v v'
      _ = K ^ Fintype.card ι * ∏ v', a v' := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ ≤ K ^ Fintype.card ι * P2 := mul_le_mul_of_nonneg_left h2 hKn.le
  have hlo : P1 / K ^ Fintype.card ι ≤ a v ^ Fintype.card ι := by
    rw [div_le_iff₀ hKn]
    calc P1 ≤ ∏ v', a v' := h1
      _ ≤ ∏ _v' : ι, K * a v := Finset.prod_le_prod₀ (fun v' _ => (ha v').le) fun v' _ => hb v' v
      _ = a v ^ Fintype.card ι * K ^ Fintype.card ι := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ, mul_comm]
  have hm : 0 < min 1 (P1 / K ^ Fintype.card ι) := lt_min one_pos (div_pos hP1 hKn)
  have hmv : min 1 (P1 / K ^ Fintype.card ι) ≤ a v := by
    rcases le_total (a v) 1 with h | h
    · exact le_trans (min_le_right _ _) (le_trans hlo (pow_le_of_le_one (ha v).le h hn))
    · exact le_trans (min_le_left _ _) h
  refine ⟨le_trans (inv_le_of_inv_le₀ hm (le_max_right _ _)) hmv, ?_⟩
  refine le_trans ?_ (le_max_left _ _)
  rcases le_total (a v) 1 with h | h
  · exact le_trans h (le_max_left _ _)
  · exact le_trans (le_self_pow₀ h hn) (le_trans hup (le_max_right _ _))

variable {F : Type} [Field F] [NumberField F]

def good (N : ℕ) (A : GF F) : Prop := ∀ i j, (N : Af F) * A.val i j ∈ Ohat F

theorem good_mul {a b : ℕ} {A B : GF F} (hA : good a A) (hB : good b B) : good (a * b) (A * B) := by
  intro i j
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_mul]
  have e : (a : Af F) * b * (A.val i 0 * B.val 0 j + A.val i 1 * B.val 1 j) =
      (a * A.val i 0) * (b * B.val 0 j) + (a * A.val i 1) * (b * B.val 1 j) := by ring
  rw [e]
  exact add_mem (mul_mem (hA i 0) (hB 0 j)) (mul_mem (hA i 1) (hB 1 j))

theorem good_dvd {a b : ℕ} {A : GF F} (hA : good a A) (h : a ∣ b) : good b A := by
  obtain ⟨c, rfl⟩ := h
  intro i j
  rw [Nat.cast_mul, mul_comm (a : Af F), mul_assoc]
  exact mul_mem (natCast_mem _ c) (hA i j)

omit [NumberField F] in
theorem scal_center (s : Fˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ Subgroup.center (GL (Fin 2) F) :=
  Subgroup.mem_center_iff.2 fun g => Units.ext (Matrix.scalar_commute (n := Fin 2) (s : F) (fun _ => Commute.all _ _) g.val).symm.eq

theorem jF_scalar (s : Fˣ) : jF F (Matrix.GeneralLinearGroup.scalar (Fin 2) s) = zc F (ratU F s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jF, zc, ratU]

theorem det_jF (g : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (jF F g) = ratU F (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [jF, ratU, Matrix.det_fin_two]

theorem zc_val (a : (Af F)ˣ) (i j : Fin 2) : (zc F a).val i j = if i = j then (a : Af F) else 0 := by
  fin_cases i <;> fin_cases j <;> simp [zc]

theorem reAt_eq [IsTotallyReal F] (v : InfinitePlace F) (t : F) : reAt v t = sg v t := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

end UpperTheory.Esk.CentralScalingLemmas

namespace UpperTheory.Esk

open CentralScalingLemmas in
theorem dScale : AMem → ACls → AUnit → DScale := by
  intro hM hC hU F _ _ _ c hc χ ω
  obtain ⟨hK0, -, hKc, hHc, hdet, hint, hN, hunit⟩ := hM F
  obtain ⟨T, hT⟩ := hC F
  obtain ⟨C0, hC0, hU'⟩ := hU F
  obtain ⟨x, rfl⟩ : ∃ x : GF F, (x : GF F ⧸ Hc c) = ω := QuotientGroup.mk_surjective ω
  obtain ⟨N1, hN1, hx1⟩ := hN x
  obtain ⟨N2, hN2, hx2⟩ := hN x⁻¹
  choose Nf hNf0 hNf using hN
  have hzK : ∀ a : (Af F)ˣ, (a : Af F) ∈ Ohat F → ((a⁻¹ : (Af F)ˣ) : Af F) ∈ Ohat F → zc F a ∈ K0 F := by
    intro a h1 h2
    refine (hK0 _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [zc_val]; split_ifs
      · exact h1
      · exact zero_mem _
    · rw [← map_inv, zc_val]; split_ifs
      · exact h2
      · exact zero_mem _
  refine ⟨N1 * (∏ r ∈ T, Nf (zc F r)) * N2,
    cb (C0 ^ 2) (∑ r ∈ T, absF (Matrix.GeneralLinearGroup.det (zc F r)))⁻¹
      (∑ r ∈ T, (absF (Matrix.GeneralLinearGroup.det (zc F r)))⁻¹) (Fintype.card (InfinitePlace F)), ?_, cb_pos _ _ _ _, ?_⟩
  · exact Nat.mul_ne_zero (Nat.mul_ne_zero hN1 (Finset.prod_ne_zero_iff.2 fun r _ => hNf0 _)) hN2
  intro γ hγ
  induction γ using QuotientGroup.induction_on with
  | H γ₀ =>
  have h1 : x⁻¹ * (jF F γ₀ * x) ∈ Hc c := by
    have e : ((jF F γ₀ * x : GF F) : GF F ⧸ Hc c) = (x : GF F ⧸ Hc c) := hγ
    have := inv_mem (QuotientGroup.eq.1 e)
    convert this using 1
  obtain ⟨k, hk, z, hkz⟩ := (hHc c _).1 h1
  obtain ⟨y, u, r, hr, hu, hz⟩ := hT z
  set d : F := γ₀.val.det * ((y⁻¹ : Fˣ) : F) ^ 2 with hd
  have hd0 : d ≠ 0 := mul_ne_zero γ₀.det_ne_zero (pow_ne_zero _ (Units.ne_zero _))
  obtain ⟨ε, hε0, hεi, hεi', hεb⟩ := hU' (fun v => Real.sqrt (abs (sg v d)))
    (fun v => (Real.sqrt_pos.2 (abs_pos.2 ((map_ne_zero (sg v)).2 hd0))).ne')
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin 2) F, g = γ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) (y⁻¹ * Units.mk0 ε hε0) := ⟨_, rfl⟩
  have hK' : k * zc F (u * ratU F (Units.mk0 ε hε0)) ∈ K0 F := by
    refine mul_mem (hKc c hk) ?_
    rw [map_mul]
    refine mul_mem (hunit u hu).1 (hzK _ ?_ ?_)
    · exact (hint ε).1 hεi
    · rw [← map_inv]
      simpa [ratU] using (hint ε⁻¹).1 hεi'
  have hconj : x⁻¹ * (jF F g * x) = (k * zc F (u * ratU F (Units.mk0 ε hε0))) * zc F r := by
    have hjγ : jF F γ₀ = x * (k * zc F z) * x⁻¹ := by rw [← hkz]; group
    have hcomm := Subgroup.mem_center_iff.1 (zc_center (ratU F (y⁻¹ * Units.mk0 ε hε0))) x
    have hzS : z * ratU F (y⁻¹ * Units.mk0 ε hε0) = r * (u * ratU F (Units.mk0 ε hε0)) := by
      rw [hz, map_mul, map_inv]
      rw [show ratU F y * r * u * ((ratU F y)⁻¹ * ratU F (Units.mk0 ε hε0)) =
        (ratU F y * (ratU F y)⁻¹) * (r * (u * ratU F (Units.mk0 ε hε0))) by ac_rfl, mul_inv_cancel, one_mul]
    calc x⁻¹ * (jF F g * x)
        = x⁻¹ * (x * (k * zc F z) * x⁻¹ * zc F (ratU F (y⁻¹ * Units.mk0 ε hε0)) * x) := by
          rw [hg, map_mul, jF_scalar, hjγ]
      _ = x⁻¹ * (x * (k * zc F z) * x⁻¹ * (x * zc F (ratU F (y⁻¹ * Units.mk0 ε hε0)))) := by
          rw [mul_assoc _ (zc F _) x, ← hcomm]
      _ = k * (zc F z * zc F (ratU F (y⁻¹ * Units.mk0 ε hε0))) := by group
      _ = k * zc F (r * (u * ratU F (Units.mk0 ε hε0))) := by rw [← map_mul, hzS]
      _ = k * zc F (u * ratU F (Units.mk0 ε hε0)) * zc F r := by rw [mul_comm r, map_mul, mul_assoc]
  have hjg : jF F g = x * ((k * zc F (u * ratU F (Units.mk0 ε hε0))) * zc F r) * x⁻¹ := by
    rw [← hconj]; group
  refine ⟨g, ?_, fun i j => ?_, ?_⟩
  · rw [hg, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 (scal_center _), mul_one]
  ·
    have hgood : good (N1 * 1 * Nf (zc F r) * N2) (jF F g) := by
      rw [hjg, ← mul_assoc x]
      refine good_mul (good_mul (good_mul hx1 ?_) (hNf _)) hx2
      intro i j
      rw [Nat.cast_one, one_mul]
      exact ((hK0 _).1 hK').1 i j
    have hg2 := good_dvd (b := N1 * (∏ r ∈ T, Nf (zc F r)) * N2) hgood (by
      rw [mul_one]
      exact Nat.mul_dvd_mul (Nat.mul_dvd_mul_left _ (Finset.dvd_prod_of_mem _ hr)) dvd_rfl) i j
    refine (hint _).2 ?_
    rw [map_mul, map_natCast]
    exact hg2
  ·
    have hV : ∀ r' : (Af F)ˣ, 0 < absF (Matrix.GeneralLinearGroup.det (zc F r')) := fun r' => (Hm.absf F).1 _
    have habs : absF (ratU F (Matrix.GeneralLinearGroup.det g)) = absF (Matrix.GeneralLinearGroup.det (zc F r)) := by
      rw [← det_jF, hjg, map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det x), mul_assoc,
        mul_inv_cancel, mul_one, map_mul, (Hm.absf F).2.1, (Hm.absf F).2.2.1 _ fun w => (hdet _ hK' w).1, one_mul]
    have hprod : ∏ v, |sg v g.val.det| = (absF (Matrix.GeneralLinearGroup.det (zc F r)))⁻¹ := by
      have := (Hm.absf F).2.2.2 (Matrix.GeneralLinearGroup.det g)
      have e : ∀ v, |reAt v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)| = |sg v g.val.det| := fun v => by
        rw [reAt_eq, Matrix.GeneralLinearGroup.val_det_apply]
      simp only [e] at this
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← habs]
      exact this
    have hdg : g.val.det = d * ε ^ 2 := by
      rw [hg, Units.val_mul, Matrix.det_mul, hd]
      simp [Matrix.det_fin_two]
      ring
    have ha : ∀ v, |sg v g.val.det| = |sg v ε * Real.sqrt (abs (sg v d))| ^ 2 := by
      intro v
      rw [hdg, map_mul, map_pow, abs_mul, sq_abs, mul_pow, Real.sq_sqrt (abs_nonneg _), abs_pow, sq_abs, mul_comm]
    intro v
    refine bal (fun v => |sg v g.val.det|) (pow_pos hC0 2) ?_ ?_ ?_ ?_ ?_ v
    · exact inv_pos.2 (lt_of_lt_of_le (hV r) (Finset.single_le_sum (fun r' _ => (hV r').le) hr))
    · intro v
      exact abs_pos.2 ((map_ne_zero (sg v)).2 g.det_ne_zero)
    · intro v v'
      rw [ha, ha, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hεb v v') 2
    · rw [hprod]
      exact inv_anti₀ (hV r) (Finset.single_le_sum (fun r' _ => (hV r').le) hr)
    · rw [hprod]
      exact Finset.single_le_sum (fun r' _ => (inv_pos.2 (hV r')).le) hr

end UpperTheory.Esk
end
end

