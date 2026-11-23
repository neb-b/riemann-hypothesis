module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResEqOneIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0413
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaMulGaloisCompositum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.InertiaLift


open ReciprocityTheory.DiscreteGroups.LocalClassField in
theorem unr_inf_le {l : ℕ} [Fact l.Prime] (F K'' : IntermediateField ℚ_[l] (Om l))
    (hF : FiniteDimensional ℚ_[l] F) (hK : FiniteDimensional ℚ_[l] K'') (hFK : F ≤ K'') :
    (F ⊔ MaximalUnramifiedExtension l) ⊓ K'' ≤ F ⊔ (K'' ⊓ MaximalUnramifiedExtension l) := by
  set N := (F ⊔ MaximalUnramifiedExtension l) ⊓ K'' with hNdef
  have hN : FiniteDimensional ℚ_[l] N :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_right : N ≤ K'')).toLinearMap
      (IntermediateField.inclusion (inf_le_right : N ≤ K'')).injective
  have hNur : N ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l F := by
    rw [Kur_eq hF]
    refine inf_le_left.trans (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) F)
    rintro x ⟨m, -, hm, hx⟩
    exact ⟨m, hm, hx⟩
  obtain ⟨n, hn, hNn⟩ := exists_le_Kn_of_le_Kur hF hN hNur
  have hFN : F ≤ N := le_inf le_sup_left hFK
  have hdvd : Module.finrank ℚ_[l] F ∣ Module.finrank ℚ_[l] N :=
    IntermediateField.finrank_dvd_of_le_right hFN
  have hpos : 0 < Module.finrank ℚ_[l] N := Module.finrank_pos
  have hFpos : 0 < Module.finrank ℚ_[l] F := Module.finrank_pos
  set d := Module.finrank ℚ_[l] N / Module.finrank ℚ_[l] F
  have hd : 0 < d := Nat.div_pos (Nat.le_of_dvd hpos hdvd) hFpos
  have hNeq : N = Kn l F d := eq_Kn_of_norm l F hF hFN hd (Nat.div_mul_cancel hdvd).symm
    (fun x hx => norm_Kn l F hF hn (hNn hx))
  rw [hNeq]
  refine UnramifiedExtensions.Kn_le F le_sup_left fun ζ hζ => (le_sup_right : K'' ⊓ MaximalUnramifiedExtension l ≤ _) ⟨?_, ?_⟩
  · have h1 : ζ ∈ N := by rw [hNeq]; exact mem_Kn_of_pow l F hζ
    exact h1.2
  · refine IntermediateField.subset_adjoin _ _ ⟨_, ?_, UnramifiedExtensions.not_dvd_qK_pow_sub_one F hF hd, hζ⟩
    have := one_lt_qK l F hF
    have : 1 < qK l F ^ d := Nat.one_lt_pow hd.ne' this
    omega

end GlobalTheory.InertiaLift

namespace GlobalTheory.InertiaLift

theorem exists_mul_of_fixes {l : ℕ} [Fact l.Prime] (M K'' : IntermediateField ℚ_[l] (Om l))
    (hK : FiniteDimensional ℚ_[l] K'')
    (hconj : ∀ s ∈ M.fixingSubgroup, ∀ k ∈ K''.fixingSubgroup, s⁻¹ * k * s ∈ K''.fixingSubgroup)
    (h : GQ l) (hh : ∀ x ∈ M ⊓ K'', h x = x) :
    ∃ i ∈ M.fixingSubgroup, i⁻¹ * h ∈ K''.fixingSubgroup := by
  let T : Subgroup (GQ l) :=
    { carrier := {g | ∃ s ∈ M.fixingSubgroup, s⁻¹ * g ∈ K''.fixingSubgroup}
      one_mem' := ⟨1, M.fixingSubgroup.one_mem, by simpa using K''.fixingSubgroup.one_mem⟩
      mul_mem' := by
        rintro g₁ g₂ ⟨s₁, hs₁, hk₁⟩ ⟨s₂, hs₂, hk₂⟩
        refine ⟨s₁ * s₂, M.fixingSubgroup.mul_mem hs₁ hs₂, ?_⟩
        have e : (s₁ * s₂)⁻¹ * (g₁ * g₂) = (s₂⁻¹ * (s₁⁻¹ * g₁) * s₂) * (s₂⁻¹ * g₂) := by group
        rw [e]
        exact K''.fixingSubgroup.mul_mem (hconj s₂ hs₂ _ hk₁) hk₂
      inv_mem' := by
        rintro g ⟨s, hs, hk⟩
        refine ⟨s⁻¹, M.fixingSubgroup.inv_mem hs, ?_⟩
        have e : s⁻¹⁻¹ * g⁻¹ = (s⁻¹)⁻¹ * (s⁻¹ * g)⁻¹ * s⁻¹ := by group
        rw [e]
        exact hconj _ (M.fixingSubgroup.inv_mem hs) _ (K''.fixingSubgroup.inv_mem hk) }
  have hNT : K''.fixingSubgroup ≤ T := fun k hk => ⟨1, M.fixingSubgroup.one_mem, by simpa using hk⟩
  have hMT : M.fixingSubgroup ≤ T := fun s hs => ⟨s, hs, by simpa using K''.fixingSubgroup.one_mem⟩
  have hopen : IsOpen (T : Set (GQ l)) := Subgroup.isOpen_mono hNT (IntermediateField.fixingSubgroup_isOpen K'')
  let Tc : ClosedSubgroup (GQ l) := ⟨T, Subgroup.isClosed_of_isOpen T hopen⟩
  have hfix : IntermediateField.fixedField T ≤ M ⊓ K'' := by
    refine le_inf ?_ ?_
    · rw [← InfiniteGalois.fixedField_fixingSubgroup M]
      intro x hx s
      exact hx ⟨s.1, hMT s.2⟩
    · rw [← InfiniteGalois.fixedField_fixingSubgroup K'']
      intro x hx s
      exact hx ⟨s.1, hNT s.2⟩
  have hT : h ∈ (IntermediateField.fixedField (Tc : Subgroup (GQ l))).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hh x (hfix hx)
  rw [InfiniteGalois.fixingSubgroup_fixedField Tc] at hT
  exact hT

theorem inertia_of_fixes_Kur {l : ℕ} [Fact l.Prime] (i : GQ l) (hi : ∀ x ∈ MaximalUnramifiedExtension l, i x = x) :
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖i x - x‖ < 1 := by
  have hn : ∀ y : Om l, ‖i y‖ = ‖y‖ := fun y => (spectralNorm_eq_of_equiv i y).symm
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact lt_of_le_of_lt (ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [hn]; exact hlt) hlt)
  · obtain ⟨ζ, m, hm, hζ, hxζ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar x heq
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
    have h1 : i ζ = ζ := hi ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm0, hm, hζ⟩)
    have h2 : i x - x = i (x - ζ) - (x - ζ) := by rw [map_sub, h1]; ring
    rw [h2]
    exact lt_of_le_of_lt (ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_le_max' _ _) (max_lt (by rw [hn]; exact hxζ) hxζ)

theorem lift : ∀ (l : ℕ) [Fact l.Prime] (K' F K'' : FinExt l), (GK K').Normal → K''.1 = K'.1 ⊔ F.1 →
    ∀ h : GQ l, h ∈ GK F → (∀ x ∈ K0 K'', h x = x) →
      ∃ i : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)), i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (i : GQ l) ∈ GK F ∧
        (i : GQ l)⁻¹ * h ∈ GK K'' := by
  intro l _ K' F K'' hnorm hK'' h hF h0
  have hFK : F.1 ≤ K''.1 := hK'' ▸ le_sup_right
  have hfK : FiniteDimensional ℚ_[l] K''.1 := K''.2
  have hfF : FiniteDimensional ℚ_[l] F.1 := F.2

  have h1 : h ∈ (F.1 ⊔ (K''.1 ⊓ MaximalUnramifiedExtension l)).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hF, (IntermediateField.mem_fixingSubgroup_iff _ _).2 h0⟩
  have h2 : ∀ x ∈ (F.1 ⊔ MaximalUnramifiedExtension l) ⊓ K''.1, h x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 h1 x (unr_inf_le F.1 K''.1 hfF hfK hFK hx)
  have hconj : ∀ s ∈ (F.1 ⊔ MaximalUnramifiedExtension l).fixingSubgroup, ∀ k ∈ K''.1.fixingSubgroup,
      s⁻¹ * k * s ∈ K''.1.fixingSubgroup := by
    intro s hs k hk
    rw [IntermediateField.fixingSubgroup_sup] at hs
    rw [hK'', IntermediateField.fixingSubgroup_sup] at hk ⊢
    refine ⟨?_, F.1.fixingSubgroup.mul_mem (F.1.fixingSubgroup.mul_mem
      (F.1.fixingSubgroup.inv_mem hs.1) hk.2) hs.1⟩
    have := hnorm.conj_mem k hk.1 s⁻¹
    rw [inv_inv] at this
    exact this
  obtain ⟨i, hi, hik⟩ := exists_mul_of_fixes (F.1 ⊔ MaximalUnramifiedExtension l) K''.1 hfK hconj h h2
  rw [IntermediateField.fixingSubgroup_sup] at hi
  have hiQ : i ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact i.commutes y
  refine ⟨⟨i, hiQ⟩, Subgroup.subset_closure ?_, hi.1, hik⟩
  exact inertia_of_fixes_Kur i ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hi.2)

end GlobalTheory.InertiaLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveRootsOfNcardRootSet
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem exists_injective_roots_of_ncard_rootSet {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra A O] (t : ℕ) (P : Polynomial A) (α : Fin t → FractionRing O)
    (hinj : Function.Injective (algebraMap A O))
    (hcard : ((P.map (toFr A)).rootSet (AlgebraicClosure (FractionRing A))).ncard = t)
    (hP : P.map ((toFr O).comp (algebraMap A O)) = ∏ c, (Polynomial.X - Polynomial.C (α c))) :
    ∃ β : Fin t → O, Function.Injective β ∧ P.map (algebraMap A O) = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  have hO : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hA : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective _ _
  set g : A →+* FractionRing O := (algebraMap O (FractionRing O)).comp (algebraMap A O) with hg
  have hgi : Function.Injective g := hO.comp hinj
  change P.map g = _ at hP
  change ((P.map (algebraMap A (FractionRing A))).rootSet _).ncard = t at hcard
  have hmon' : (P.map g).Monic := by
    rw [hP]; exact Polynomial.monic_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)
  have hmon : P.Monic := Polynomial.monic_of_injective hgi hmon'
  have hdeg : P.natDegree = t := by
    rw [← hmon.natDegree_map g, hP, Polynomial.natDegree_prod_of_monic _ _ (fun c _ => Polynomial.monic_X_sub_C _)]
    simp
  have hsep : (P.map (algebraMap A (FractionRing A))).Separable := by
    have hne : P.map (algebraMap A (FractionRing A)) ≠ 0 := (hmon.map _).ne_zero
    rw [← Polynomial.card_rootSet_eq_natDegree_iff_of_splits (K := AlgebraicClosure (FractionRing A)) hne (IsAlgClosed.splits _), hmon.natDegree_map, hdeg, ← hcard, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  obtain ⟨φ, hφ⟩ : ∃ φ : FractionRing A →+* FractionRing O, φ.comp (algebraMap A (FractionRing A)) = g :=
    ⟨IsFractionRing.lift hgi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := FractionRing A) hgi a⟩
  have hsep2 : (P.map g).Separable := by
    rw [← hφ, ← Polynomial.map_map]; exact hsep.map
  have hα : Function.Injective α := by
    rw [hP] at hsep2
    exact Polynomial.separable_prod_X_sub_C_iff.mp hsep2
  have hint : ∀ c, ∃ b : O, algebraMap O (FractionRing O) b = α c := by
    intro c
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    refine ⟨P.map (algebraMap A O), hmon.map _, ?_⟩
    rw [← Polynomial.eval_map, Polynomial.map_map, ← hg, hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by simp)
  choose β hβ using hint
  refine ⟨β, fun c d h => hα (by rw [← hβ, ← hβ, h]), ?_⟩
  apply Polynomial.map_injective _ hO
  rw [Polynomial.map_map, ← hg, hP, Polynomial.map_prod]
  simp [hβ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section Bounded

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]


omit [IsUnitBall O K] in
theorem norm_tail_mul_rad_le {f : K⟦X⟧} {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) (n : ℕ) :
    ‖tail l e f n‖ * rad l (1 / e) ^ n ≤ b := by
  have hρ := pow_pos (rad_pos l (1 / e)) n
  rw [← le_div_iff₀ hρ]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (div_nonneg hb hρ.le) fun j => ?_
  rw [le_div_iff₀ hρ, norm_term_eq]
  exact hf _

theorem coeff_sub_E_mul_quotE_of_lt [CompleteSpace K] {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) {n : ℕ}
    (hn : n < e) : coeff n (f - E K l e * quotE l e f) = tail l e f n := by
  rw [tail_rec l e hf n, map_sub, E, add_mul, map_add (f := _), coeff_X_pow_mul', if_neg (by omega),
    ← map_natCast (C : K →+* K⟦X⟧) l, coeff_C_mul, quotE, coeff_mk]
  ring

theorem norm_coeff_mul_rad_le_of_mem_S {f : K⟦X⟧} (hf : f ∈ S O K e) (n : ℕ) :
    ‖coeff n f‖ * rad l (1 / e) ^ n ≤ 1 := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hf.1 n)
  refine le_trans ?_ (norm_pow_le_norm_factorial (K := K) l (n / e))
  rw [← rad_pow (K := K) l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le n e)

theorem exists_bdd_div_E_pow [CompleteSpace K] (m : ℕ) {f : K⟦X⟧} (hf : f ∈ Rpi O K l e)
    {b : ℝ} (hb : 0 ≤ b) (hfb : ∀ n, ‖coeff n f‖ * rad l (1 / e) ^ n ≤ b) :
    ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ b * ‖(l : K)‖⁻¹ ^ m) ∧
      ∃ h ∈ Rpi O K l e, f = g + E K l e ^ m * h := by
  induction m generalizing f b with
  | zero => exact ⟨0, fun n => by simpa using hb, f, hf, by simp⟩
  | succ m ih =>
    have hl0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
    have hl1 : ‖(l : K)‖ < 1 := norm_l_lt_one l
    have hρe : rad l (1 / e) ^ e = ‖(l : K)‖ := rad_pow l e
    have hρ0 : 0 < rad l (1 / e) := rad_pos l _
    have hρ1 : rad l (1 / e) ≤ 1 := rad_le_one l (by positivity)
    have htail := norm_tail_mul_rad_le l e hb hfb
    have hq : ∀ n, ‖coeff n (quotE l e f)‖ * rad l (1 / e) ^ n ≤ b * ‖(l : K)‖⁻¹ := fun n => by
      have := htail (n + e)
      rw [pow_add, hρe] at this
      rw [quotE, coeff_mk, le_mul_inv_iff₀ hl0]
      simpa [mul_assoc] using this
    obtain ⟨g1, hg1, h1, hh1, hq1⟩ :=
      ih (quotE_mem_Rpi l e hf) (mul_nonneg hb (inv_nonneg.2 hl0.le)) hq
    have hpow : ‖(l : K)‖⁻¹ ≤ ‖(l : K)‖⁻¹ ^ (m + 1) := by
      simpa using pow_le_pow_right₀ (one_le_inv₀ hl0 |>.2 hl1.le) (Nat.succ_le_succ (Nat.zero_le m))
    refine ⟨(f - E K l e * quotE l e f) + E K l e * g1, fun n => ?_, h1, hh1, ?_⟩
    · rw [map_add (f := _)]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rcases lt_or_ge n e with hn | hn
        · rw [coeff_sub_E_mul_quotE_of_lt l e hf hn]
          have h2 := htail n
          have h3 : ‖(l : K)‖ ≤ rad l (1 / e) ^ n := by
            rw [← hρe]; exact pow_le_pow_of_le_one hρ0.le hρ1 hn.le
          have h4 : ‖tail l e f n‖ ≤ b * ‖(l : K)‖⁻¹ := by
            rw [le_mul_inv_iff₀ hl0]
            exact (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2
          exact h4.trans (mul_le_mul_of_nonneg_left hpow hb)
        · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
          rw [coeff_sub_E_mul_quotE l e hf, norm_zero]
          positivity
      · have hE : ∀ n, ‖coeff n (E K l e)‖ * (1 : ℝ) ≤ 1 := fun n => by
          simpa using (E_mem l e (A O K)) n
        have := norm_coeff_mul_le (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
          (fun _ _ => by simp) (a := 1) (b := b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) zero_le_one
          (by positivity) hE (g := g1) (fun n => by rw [mul_one]; exact hg1 n) n
        have e' : (1 : ℝ) * (b * ‖(l : K)‖⁻¹ * ‖(l : K)‖⁻¹ ^ m) = b * ‖(l : K)‖⁻¹ ^ (m + 1) := by
          ring
        rw [mul_one, e'] at this
        exact this
    · linear_combination E K l e * hq1

end Bounded

end GlobalTheory.BK

namespace GlobalTheory.BKReal

open PowerSeries GlobalTheory.BK

theorem exists_l_pow_iHat_toHatS_sub_dvd (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e)
    [CompleteSpace K] (m : ℕ) (s : S O K e) :
    ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣
      (l : OD l O) ^ m * ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) -
        toOD l O y := by
  obtain ⟨g, hg, h, hh, hs⟩ := exists_bdd_div_E_pow l e m (S_le_R l e s.2) zero_le_one
    (norm_coeff_mul_rad_le_of_mem_S l e s.2)
  have hl0 : ‖(l : K)‖ ≠ 0 := norm_ne_zero_iff.2 (GlobalTheory.BK.l_ne_zero (K := K) l)
  have hG : C ((l : K) ^ m) * g ∈ A O K := fun n => by
    rw [coeff_C_mul, norm_mul, norm_pow]
    calc _ ≤ ‖(l : K)‖ ^ m * (1 * ‖(l : K)‖⁻¹ ^ m) := by gcongr; exact hg n
      _ = 1 := by rw [one_mul, ← mul_pow, mul_inv_cancel₀ hl0, one_pow]
  have hH : C ((l : K) ^ m) * h ∈ Rpi O K l e := mul_mem (HasK.C_mem _) hh
  have key : (l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
      (algebraMap (S O K e) (invL l (S O K e)) s) =
      ⟨_, A_le_Rpi l e hG⟩ + EIn l e (Rpi O K l e) ^ m * ⟨_, hH⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_pow, SubringClass.coe_natCast,
      Subalgebra.coe_inclusion, coe_algebraMap_away, coe_EIn, map_pow, map_natCast]
    rw [hs]
    ring
  have e1 : ϖ.iHat O K (toHat O K l e ⟨_, A_le_Rpi l e hG⟩) = toOD l O (ϖ.iA O K ⟨_, hG⟩) :=
    (congrArg (ϖ.iHat O K)
      (toHat_eq_ofAl l e (g := algebraMap (A O K) (invL l (A O K)) ⟨_, hG⟩) rfl)).trans
      (ϖ.iHat_ofA O K _)
  have e2 : ϖ.iHat O K (Ehat O K l e) = ϖ.iAl O K (EIn l e _) := ϖ.iHat_ofAl O K _
  have h1 : (l : OD l O) ^ m *
      ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) =
      ϖ.iHat O K (toHat O K l e ((l : Rpi O K l e) ^ m * Subalgebra.inclusion (invL_S_le_Rpi l e)
        (algebraMap (S O K e) (invL l (S O K e)) s))) := by
    simp only [map_mul, map_pow, map_natCast]
    rfl
  refine ⟨ϖ.iA O K ⟨_, hG⟩, ϖ.iHat O K (toHat O K l e ⟨_, hH⟩), ?_⟩
  rw [h1, key]
  rw [map_add (toHat O K l e), map_add (ϖ.iHat O K), map_mul (toHat O K l e), map_mul (ϖ.iHat O K),
    map_pow (toHat O K l e), map_pow (ϖ.iHat O K), toHat_E, e1, e2]
  ring

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctor
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
namespace GlobalTheory.HWL.Assembly

theorem exists_wach (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (hF : FaithH AI) (hW : WachEx AI) :
    ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  obtain ⟨ht, hπ, -⟩ := GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI hT
  refine exists_of_layers P AI (fun K s LL g => ?_) ht hπ
  obtain ⟨Γ⟩ := GlobalTheory.HWL.GroupLayer.nonempty_gamS l P K s LL g
  obtain ⟨R⟩ := GlobalTheory.HWL.Ser.nonempty_wSer l P K s LL g Γ
  obtain ⟨I, hI⟩ := GlobalTheory.HWL.IoLayer.main l P AI K s LL g Γ R
  obtain ⟨E⟩ := GlobalTheory.HWL.EtMod.nonempty_wEt l P AI K s LL g Γ R I hI (GlobalTheory.EtaleBasis.exists_etBasis l P AI hF K s LL g Γ R I hI)
  obtain ⟨Mo⟩ := hW K s LL g Γ R I hI E
  obtain ⟨Cl⟩ := GlobalTheory.HerrClassMaps.exists_classMaps l P AI K s LL g Γ R I hI E
  obtain ⟨Cm⟩ := GlobalTheory.HWL.Cmp.nonempty_cmpS l P AI hT K s LL g Γ R I hI E Mo
  exact ⟨⟨Γ, R, I, hI, E, Mo, Cl, Cm⟩⟩

end GlobalTheory.HWL.Assembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulNormLe
section
namespace GlobalTheory.NatCastNormLtOne

theorem norm_natCast_lt_one {l : ℕ} [Fact (Nat.Prime l)] {K : Type} [NormedField K]
    [NormedAlgebra ℚ_[l] K] : ‖(l : K)‖ < 1 := by
  have h : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem exists_pow_mul_norm_le {K : Type} [NormedField K] {x : K} (hx : ‖x‖ < 1) (a : K) :
    ∃ n : ℕ, ‖x ^ n * a‖ ≤ 1 := by
  have h : Filter.Tendsto (fun n : ℕ => ‖x‖ ^ n * ‖a‖) Filter.atTop (nhds (0 * ‖a‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx).mul_const _
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rw [norm_mul, norm_pow]; exact hn.le⟩

theorem exists_pow_smul_mem {l : ℕ} [hl : Fact (Nat.Prime l)] {O K : Type} [CommRing O]
    [NormedField K] [Algebra O K] [GlobalTheory.BK.IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (T : Submodule O V) (hT : Submodule.span K (T : Set V) = ⊤) (v : V) :
    ∃ n : ℕ, (l : K) ^ n • v ∈ T := by
  have hpow : ∀ (k : ℕ) (w : V), w ∈ T → (l : K) ^ k • w ∈ T := by
    intro k w hw
    have h : (l : K) ^ k = algebraMap O K ((l : O) ^ k) := by simp
    rw [h, algebraMap_smul]
    exact T.smul_mem _ hw
  have hv : v ∈ Submodule.span K (T : Set V) := by rw [hT]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]; exact hpow _ _ hn
    · rw [pow_add, mul_smul]; exact hpow _ _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (norm_natCast_lt_one (l := l) (K := K)) a
    obtain ⟨b, hb⟩ := (GlobalTheory.BK.IsUnitBall.mem_range_iff (O := O) ((l : K) ^ m * a)).2 hm
    refine ⟨m + n, ?_⟩
    have h : (l : K) ^ (m + n) • a • x = b • ((l : K) ^ n • x) := by
      rw [← algebraMap_smul K b, hb, smul_smul, smul_smul]
      congr 1
      ring
    rw [h]
    exact T.smul_mem _ hn

theorem main : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {O K : Type} [inst : CommRing O]
    [inst_1 : NormedField K] [inst_2 : Algebra O K] [GlobalTheory.BK.IsUnitBall O K]
    [inst_4 : NormedAlgebra ℚ_[l] K] {G : Type} [inst_5 : Group G] [inst_6 : TopologicalSpace G]
    (T : Formalism.BasicNotions.LocLat G ℚ_[l] K O) (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : K) ^ n • v ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ O K _ _ _ _ _ G _ _ T v
  exact exists_pow_smul_mem T.L.T T.L.span v

end GlobalTheory.NatCastNormLtOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemLocalLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LatPow

theorem pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G]
    (T : LocLat G ℚ_[l] K O) (v : T.V), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x : ↥T.L.T, (x : T.V) = (l : K) ^ n • v := by
  intro l _ O K _ _ _ _ _ G _ _ T v
  have hv : v ∈ Submodule.span K (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  suffices h : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : K) ^ n • v ∈ T.L.T by
    obtain ⟨n₀, h⟩ := h
    exact ⟨n₀, fun n hn => ⟨⟨_, h n hn⟩, rfl⟩⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ => ?_⟩
    have : (l : K) ^ n • x = ((l : O) ^ n) • x := by
      rw [← algebraMap_smul K ((l : O) ^ n) x, map_pow, map_natCast]
    rw [this]
    exact T.L.T.smul_mem _ hx
  | zero => exact ⟨0, fun n _ => by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, fun n hn => by
      rw [smul_add]
      exact T.L.T.add_mem (ha n (le_of_max_le_left hn)) (hb n (le_of_max_le_right hn))⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := exists_pow_mul_mem (O := O) l c
    refine ⟨a + m, fun n hn => ?_⟩
    have e : (l : K) ^ n • c • x = b • ((l : K) ^ (n - m) • x) := by
      rw [← algebraMap_smul K b, ← hb, smul_smul, smul_smul]
      congr 1
      rw [mul_comm ((l : K) ^ m) c, mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega), mul_comm]
    rw [e]
    exact T.L.T.smul_mem _ (ha _ (by omega))

end GlobalTheory.LatPow
end

