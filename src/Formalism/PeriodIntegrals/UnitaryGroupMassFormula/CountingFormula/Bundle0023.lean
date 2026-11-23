module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralHeckeForms
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataHost

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CoordLInjective
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable (D : D7)

theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem aaI_ne_zero (a : Fin D.R.rS) : aaI D a ≠ 0 := by
  unfold aaI
  exact zpow_ne_zero _ (ddS_ne_zero D)

theorem int_mul_of_ne {b : 𝓞 D.host.E} (hb : b ≠ 0) : ∃ k : ℕ, k ≠ 0 ∧ ∃ c : 𝓞 D.host.E, (k : 𝓞 D.host.E) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

theorem fi_nat_mul {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} (hI : I ≠ 0) (x : D.host.E) :
    ∃ k : ℕ, k ≠ 0 ∧ (k : D.host.E) * x ∈ I := by
  obtain ⟨y, hyI, hy0⟩ : ∃ y ∈ I, y ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    ext z
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h z, fun hz => hz ▸ fi_zero D I⟩
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (𝓞 D.host.E) y
  have hb0' : algebraMap (𝓞 D.host.E) D.host.E b0 ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact nonZeroDivisors.ne_zero hb0
  have ha0I : algebraMap (𝓞 D.host.E) D.host.E a0 ∈ I := by
    have := fi_mul D b0 hyI
    have e : (b0 : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a0 / algebraMap (𝓞 D.host.E) D.host.E b0) =
        algebraMap (𝓞 D.host.E) D.host.E a0 := by
      rw [show (b0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b0 from rfl, mul_div_cancel₀ _ hb0']
    rwa [e] at this
  have ha00 : a0 ≠ 0 := by
    rintro rfl
    simp at hy0
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 D.host.E) x
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact hbne
  obtain ⟨k, hk, c, hc⟩ := int_mul_of_ne D hbne
  obtain ⟨k0, hk0, c0, hc0⟩ := int_mul_of_ne D ha00
  refine ⟨k0 * k, mul_ne_zero hk0 hk, ?_⟩
  have hcE : (k : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b * algebraMap (𝓞 D.host.E) D.host.E c := by
    rw [← map_mul, ← hc]; simp
  have hc0E : (k0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a0 * algebraMap (𝓞 D.host.E) D.host.E c0 := by
    rw [← map_mul, ← hc0]; simp
  have e : ((k0 * k : ℕ) : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E b) =
      ((c0 * c * a : 𝓞 D.host.E) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E a0 := by
    rw [Nat.cast_mul, hcE, hc0E]
    show _ = algebraMap (𝓞 D.host.E) D.host.E (c0 * c * a) * _
    rw [map_mul, map_mul]
    field_simp
  rw [e]
  exact fi_mul D _ ha0I

variable {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (f : Fin D.R.rS → (VS D).V)

theorem M_nat_smul (M : Submodule (𝓞 D.host.E) (WbQ D F0)) (hsp : Submodule.span D.host.E (M : Set (WbQ D F0)) = ⊤)
    (m : WbQ D F0) : ∃ k : ℕ, k ≠ 0 ∧ (k : 𝓞 D.host.E) • m ∈ M := by
  first | exact UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul .. | (apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M hsp m | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M hsp | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D

theorem vPr_perp (hf : PartnerOK D F0 f) (v : (VS D).V) : vPr D F0 f v ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    simp [vPr, hf.1]
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def vPrLin : (VS D).V →ₗ[D.host.E] (VS D).V where
  toFun := vPr D F0 f
  map_add' := vPr_add D F0 f
  map_smul' := vPr_smul D F0 f

def coordL (hf : PartnerOK D F0 f) :
    (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E) :=
  LinearMap.prod (LinearMap.pi fun a => ((VS D).hT (f a)).comp (vPrLin D F0 f))
    (LinearMap.prod ((nX D F0).mkQ.comp (LinearMap.codRestrict _ (vPrLin D F0 f) (vPr_perp D F0 f hf)))
      (LinearMap.pi fun a => (VS D).hT (F0.e a)))

theorem coordL_apply (hf : PartnerOK D F0 f) (v : (VS D).V) :
    coordL D F0 f hf v = ((fun a => (VS D).hT (f a) (vPr D F0 f v)),
      (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0),
      (fun a => (VS D).hT (F0.e a) v)) := rfl

theorem coordL_injective (hf : PartnerOK D F0 f) : Function.Injective (coordL D F0 f hf) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [coordL_apply] at hv
  simp only [Prod.mk_eq_zero] at hv
  obtain ⟨h1, h2, h3⟩ := hv
  have hb : ∀ a, (VS D).hT (F0.e a) v = 0 := fun a => congrFun h3 a
  have hvv : vPr D F0 f v = v := by simp [vPr, hb]
  have hX : v ∈ F0.X := by
    rw [Submodule.Quotient.mk_eq_zero] at h2
    have : vPr D F0 f v ∈ F0.X := h2
    rwa [hvv] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun D.host.E |>.1 hX
  have ha : ∀ a, (VS D).hT (f a) v = 0 := fun a => by
    have := congrFun h1 a
    rwa [hvv] at this
  have hc0 : ∀ a, c a = 0 := by
    intro a
    have h := ha a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum] at h
    have e : ∀ b, (VS D).hT (f a) (c b • F0.e b) = c b * (if b = a then 1 else 0) := by
      intro b
      rw [map_smul, smul_eq_mul, ← (VS D).herm.eq (F0.e b) (f a), hf.1 b a]
      split_ifs <;> simp
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  rw [← hc]
  simp [hc0]

theorem fi_bound (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    ∃ d : D.host.E, ∀ x ∈ I, ∃ o : 𝓞 D.host.E, x = (o : D.host.E) * d := by
  obtain ⟨d, hdS, hd⟩ := I.isFractional
  refine ⟨(algebraMap (𝓞 D.host.E) D.host.E d)⁻¹, fun x hx => ?_⟩
  obtain ⟨o, ho⟩ := hd x hx
  have hd0 : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact nonZeroDivisors.ne_zero hdS
  refine ⟨o, ?_⟩
  rw [Algebra.smul_def] at ho
  show x = algebraMap (𝓞 D.host.E) D.host.E o * _
  rw [ho]
  field_simp

theorem pi_mem_span {x : Fin D.R.rS → D.host.E} {d : Fin D.R.rS → D.host.E}
    (h : ∀ a, ∃ o : 𝓞 D.host.E, x a = (o : D.host.E) * d a) :
    x ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (d a) : Fin D.R.rS → D.host.E)) := by
  choose o ho using h
  have e : x = ∑ a, o a • (Pi.single a (d a) : Fin D.R.rS → D.host.E) := by
    ext b
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    simp [ho b]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem lamC_fg (hf : PartnerOK D F0 f) (M : Submodule (𝓞 D.host.E) (WbQ D F0)) (hM : M.FG) :
    (lamC D F0 f M).FG := by
  choose dα hdα using fun a => fi_bound D (aaI D a)
  choose dβ hdβ using fun a => fi_bound D (aaI D a)⁻¹
  let P : Submodule (𝓞 D.host.E) ((Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E)) :=
    (Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (dα a) : Fin D.R.rS → D.host.E))).prod
      (M.prod (Submodule.span (𝓞 D.host.E) (Set.range fun a =>
        (Pi.single a (star (dβ a)) : Fin D.R.rS → D.host.E))))
  have hPfg : P.FG := Submodule.FG.prod (Submodule.fg_span (Set.finite_range _))
    (Submodule.FG.prod hM (Submodule.fg_span (Set.finite_range _)))
  have hle : (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) ≤ P := by
    rintro _ ⟨v, ⟨h1, ⟨w, hw, hwM⟩, h3⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact pi_mem_span D (fun a => hdα a _ (h3 a))
    · have e : (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) = w := Subtype.ext hw.symm
      show (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M
      rw [e]; exact hwM
    · refine pi_mem_span D (fun a => ?_)
      obtain ⟨o, ho⟩ := hdβ a _ (h1 a)
      obtain ⟨o', ho'⟩ := star_int D o
      refine ⟨o', ?_⟩
      show (VS D).hT (F0.e a) v = _
      rw [ho', ← star_mul, mul_comm, ← ho, star_star]
  exact Submodule.fg_of_fg_map_injective ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) (coordL_injective D F0 f hf)
    (Submodule.FG.of_le (S := (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E))) hPfg hle)

theorem lamC_span (hf : PartnerOK D F0 f) (M : Submodule (𝓞 D.host.E) (WbQ D F0))
    (hsp : Submodule.span D.host.E (M : Set (WbQ D F0)) = ⊤) :
    Submodule.span D.host.E (lamC D F0 f M : Set (VS D).V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  choose kα hkα hα using fun a => fi_nat_mul D (aaI_ne_zero D a) ((VS D).hT (f a) (vPr D F0 f v))
  choose kβ hkβ hβ using fun a => fi_nat_mul D (inv_ne_zero (aaI_ne_zero D a)) (star ((VS D).hT (F0.e a) v))
  obtain ⟨kM, hkM, hM⟩ := M_nat_smul D F0 M hsp
    (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X))
  set K : ℕ := (∏ a, kα a) * kM * ∏ a, kβ a with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => hkα a) hkM)
      (Finset.prod_ne_zero_iff.2 fun a _ => hkβ a)
  have hdvd : ∀ {k : ℕ} {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x : D.host.E},
      k ∣ K → (k : D.host.E) * x ∈ I → (K : D.host.E) * x ∈ I := by
    rintro k I x ⟨m, hm⟩ hx
    rw [hm, Nat.cast_mul, mul_comm (k : D.host.E) (m : D.host.E), mul_assoc]
    have := fi_mul D (m : 𝓞 D.host.E) hx
    simpa using this
  have hmem : (K : 𝓞 D.host.E) • v ∈ lamC D F0 f M := by
    have hs : (K : 𝓞 D.host.E) • v = (K : D.host.E) • v := by
      rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast]
    rw [hs]
    refine ⟨fun a => ?_, ⟨(K : 𝓞 D.host.E) • ⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩, ?_, ?_⟩, fun a => ?_⟩
    · rw [map_smul, smul_eq_mul, star_mul, star_natCast, mul_comm]
      exact hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ a) |>.trans (dvd_mul_left _ _)) (hβ a)
    · rw [vPr_smul]
      show (K : 𝓞 D.host.E) • vPr D F0 f v = _
      rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E), map_natCast]
    · rw [Submodule.Quotient.mk_smul]
      obtain ⟨m, hm⟩ : kM ∣ K := by
        rw [hK]; exact (dvd_mul_left _ _).mul_right _
      rw [hm, Nat.cast_mul, mul_comm, mul_smul]
      exact M.smul_mem _ hM
    · rw [vPr_smul, map_smul, smul_eq_mul]
      exact hdvd ((Finset.dvd_prod_of_mem _ (Finset.mem_univ a)).mul_right _ |>.mul_right _) (hα a)
  have hK' : (K : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hK0
  have e : v = (K : D.host.E)⁻¹ • ((K : 𝓞 D.host.E) • v) := by
    rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast, smul_smul, inv_mul_cancel₀ hK', one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem lattice_integral : LamLattice := by
  intro D u F0 f M hf hM
  exact Submodule.IsLattice.of_fg D.host.E (lamC_fg D F0 f hf M hM.1.fg)

end Lat

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentCoprimeSplit
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev ddI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

def DdOffG : Prop :=
  ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)), ((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ¬ ddI D ≤ P.asIdeal

section LocLemmas

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem mem_localization_iff' (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s : 𝓞 E, s ∉ p ∧ s • x ∈ L := by
  exact Iff.rfl

theorem localization_le_of_le_localization' (p : Ideal (𝓞 E)) [p.IsPrime] {L L' : Submodule (𝓞 E) V} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  intro x hx
  rw [mem_localization_iff'] at hx ⊢
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := (mem_localization_iff' p L' _).1 (h hsx)
  refine ⟨t * s, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim ht hs, ?_⟩
  rwa [mul_smul]

theorem locGen_ideal (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ d ∈ J, d ≠ 0 ∧ ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∀ y ∈ J, ∃ o : 𝓞 E, t * y = d * o := by
  have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : J * P.asIdeal < J := by
    refine lt_of_le_of_ne (Ideal.mul_le_inf.trans inf_le_left) ?_
    intro h
    apply hP
    have h2 : J * P.asIdeal = J * ⊤ := by rw [h, Ideal.mul_top]
    exact mul_left_cancel₀ hJ h2
  obtain ⟨d, hdJ, hdP⟩ := SetLike.exists_of_lt hlt
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hdP (zero_mem _)
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hle
    apply hdP
    have h3 : Ideal.span {d} ≤ J * P.asIdeal := by
      rw [hI]
      exact Ideal.mul_mono_right hle
    exact h3 (Ideal.mem_span_singleton_self d)
  obtain ⟨t, htI, htP⟩ := SetLike.not_le_iff_exists.mp hIP
  refine ⟨d, hdJ, hd0, t, htP, fun y hy => ?_⟩
  have h4 : y * t ∈ J * I := Ideal.mul_mem_mul hy htI
  rw [← hI, Ideal.mem_span_singleton'] at h4
  obtain ⟨o, ho⟩ := h4
  exact ⟨o, by rw [mul_comm t y, ← ho, mul_comm]⟩

end LocLemmas

section XS

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem aaI_eq (a : Fin D.R.rS) :
    aaI D a = (((ddI D ^ (D.R.rS - (a : ℕ)) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  unfold aaI
  have h : ((D.R.rS : ℤ) - (a : ℕ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
    have := a.isLt
    omega
  rw [h, zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]
  try rfl

theorem ddI_ne_bot : ddI D ≠ ⊥ := by
  rw [ne_eq, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _

theorem mem_inv_coe {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) (x : D.host.E) :
    x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ ↔
      ∀ y ∈ J, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (y : D.host.E) := by
  have hJ' : (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [FractionalIdeal.mem_inv_iff hJ']
  constructor
  · intro h y hy
    have h2 := h _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨y, hy, rfl⟩)
    rw [FractionalIdeal.mem_one_iff] at h2
    obtain ⟨o, ho⟩ := h2
    exact ⟨o, ho⟩
  · intro h y hy
    rw [FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨o, ho⟩ := h y' hy'
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨o, ho⟩

theorem localization_eq_localization_span (P : Ideal (𝓞 D.host.E)) [P.IsPrime] (c : Fin D.R.rS → D.host.E)
    (h1 : ∀ a, ∀ x ∈ aaI D a, ∃ s : 𝓞 D.host.E, s ∉ P ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * x = c a * o)
    (h2 : ∀ a, ∃ s : 𝓞 D.host.E, s ∉ P ∧ (s : D.host.E) * c a ∈ aaI D a) :
    Formalism.HermitianLatticesTheory.localization₂ P (XS D F0) =
      Formalism.HermitianLatticesTheory.localization₂ P (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)) := by
  have hgen_le : XS D F0 ≤ Formalism.HermitianLatticesTheory.localization₂ P (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)) := by
    unfold XS
    rw [Submodule.span_le]
    rintro y ⟨a, x, hx, rfl⟩
    obtain ⟨s, hs, o, ho⟩ := h1 a x hx
    refine (mem_localization_iff' P _ _).mpr ⟨s, hs, ?_⟩
    have e1 : s • (x • F0.e a) = o • (c a • F0.e a) := by
      rw [← smul_assoc, ← smul_assoc]
      congr 1
      rw [Algebra.smul_def, Algebra.smul_def, mul_comm (algebraMap _ _ o)]
      exact ho
    rw [e1]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨a, rfl⟩)
  have hgen_ge : Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a) ≤ Formalism.HermitianLatticesTheory.localization₂ P (XS D F0) := by
    rw [Submodule.span_le]
    rintro y ⟨a, rfl⟩
    obtain ⟨s, hs, hsc⟩ := h2 a
    refine (mem_localization_iff' P _ _).mpr ⟨s, hs, ?_⟩
    rw [← smul_assoc]
    unfold XS
    apply Submodule.subset_span
    exact ⟨a, s • c a, by rw [Algebra.smul_def]; exact hsc, rfl⟩
  exact le_antisymm (localization_le_of_le_localization' P hgen_le) (localization_le_of_le_localization' P hgen_ge)

end XS

theorem locGenXS_of (hD : DdOffG) : LocGenXS := by
  intro D u F0 P
  haveI := P.isPrime
  have hJ : ∀ a : Fin D.R.rS, (ddI D ^ (D.R.rS - (a : ℕ))) ≠ ⊥ := fun a => pow_ne_zero _ (ddI_ne_bot D)
  have h1P : (1 : 𝓞 D.host.E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top
  by_cases hg : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨t, htd, htP⟩ := SetLike.not_le_iff_exists.mp (hD D P hg)
    refine ⟨fun _ => 1, fun _ => one_ne_zero, fun _ _ => rfl, localization_eq_localization_span D F0 P.asIdeal _ ?_ ?_⟩
    · intro a x hx
      rw [aaI_eq, mem_inv_coe D (hJ a)] at hx
      obtain ⟨o, ho⟩ := hx (t ^ (D.R.rS - (a : ℕ))) (Ideal.pow_mem_pow htd _)
      refine ⟨t ^ (D.R.rS - (a : ℕ)), fun h => htP (P.isPrime.mem_of_pow_mem _ h), o, ?_⟩
      rw [one_mul, ho, mul_comm]
    · intro a
      refine ⟨1, h1P, ?_⟩
      rw [aaI_eq, mem_inv_coe D (hJ a)]
      intro y _
      exact ⟨y, by simp⟩
  · choose d hdJ hd0 t htP ht using fun a : Fin D.R.rS => locGen_ideal (ddI D ^ (D.R.rS - (a : ℕ))) (hJ a) P
    have hdE : ∀ a, ((d a : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun a h =>
      hd0 a (NumberField.RingOfIntegers.coe_eq_zero_iff.mp h)
    refine ⟨fun a => ((d a : 𝓞 D.host.E) : D.host.E)⁻¹, fun a => inv_ne_zero (hdE a), fun h => absurd h hg,
      localization_eq_localization_span D F0 P.asIdeal _ ?_ ?_⟩
    · intro a x hx
      rw [aaI_eq, mem_inv_coe D (hJ a)] at hx
      obtain ⟨o, ho⟩ := hx (d a) (hdJ a)
      refine ⟨1, h1P, o, ?_⟩
      rw [ho]
      have := hdE a
      field_simp
      try simp
      try ring
    · intro a
      refine ⟨t a, htP a, ?_⟩
      rw [aaI_eq, mem_inv_coe D (hJ a)]
      intro y hy
      obtain ⟨o, ho⟩ := ht a y hy
      refine ⟨o, ?_⟩
      have hoE : ((t a : 𝓞 D.host.E) : D.host.E) * (y : D.host.E) = ((d a : 𝓞 D.host.E) : D.host.E) * (o : D.host.E) := by
        have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ho
        simpa using this
      rw [eq_comm, mul_comm ((t a : 𝓞 D.host.E) : D.host.E) _, mul_assoc, hoE, ← mul_assoc, inv_mul_cancel₀ (hdE a),
        one_mul]

theorem different_coprime_split : DdOffG := by
  intro D P hg hle
  have hg' : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have e : ((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
      simp [Formalism.MainNotions.S.Lat.gS, Nat.cast_mul]
    rw [e] at hg
    rcases P.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg'
  have hp : (D.host.g i).Prime := D.host.g_prime i
  have hvp : (P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime := Ideal.IsPrime.comap _
  have hpv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hi
  have hvb : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpv
    exact hp.ne_zero (by exact_mod_cast hpv)
  let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨_, hvp, hvb⟩
  have hv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := hpv
  have hef := Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.F D.host.E hp (D.nd.g_split i) v hv
  have hq0 := Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp
  have hmap : Ideal.map (algebraMap ℤ (𝓞 D.host.F)) (Ideal.span {((D.host.g i : ℕ) : ℤ)}) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hq0
  have hcount := Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap v.isPrime v.ne_bot
  rw [hef.1] at hcount
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQ1, hQ2⟩ := Ideal.eq_prime_pow_mul_coprime hmap v.asIdeal
  rw [← hcount, pow_one] at hQ2
  haveI := Formalism.L2.SG.Pf.TypedLoc.span_p_maximal hp
  haveI : NeZero (D.host.g i) := ⟨hp.ne_zero⟩
  haveI : Finite (ℤ ⧸ Ideal.span {((D.host.g i : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod (D.host.g i)).symm.toEquiv
  have hnd := not_dvd_differentIdeal_of_isCoprime ℤ v.asIdeal Q (Ideal.isCoprime_iff_sup_eq.mpr hQ1) hQ2.symm
  apply hnd
  rw [Ideal.dvd_iff_le]
  exact Ideal.map_le_iff_le_comap.mp hle

theorem local_genus_exists : LocGenXS := locGenXS_of different_coprime_split

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

