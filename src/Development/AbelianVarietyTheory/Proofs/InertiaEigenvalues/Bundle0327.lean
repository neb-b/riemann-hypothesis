module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0314
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0309
public import GroundTheory.LocalFields.Examples
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL


set_option maxHeartbeats 1600000 in
theorem N_basis_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥((H.W K s LL h).N T)) := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T
  generalize H.W K s LL h = W at hproj ⊢
  obtain ⟨hfree, hrk⟩ := W.DD_free T
  rw [← hrk]
  haveI : Module.Finite (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(W.N T) :=
    Module.Finite.iff_fg.mpr (W.N_fg T)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  refine GlobalTheory.WachFree.basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (O := ↥(OL LL))
    (N := ↥(W.N T)) (E := W.EE) (D := W.DD T) W.EE_inj (W.N T).subtype (W.N_base T hT)
    ((l : ℕ) : ↥(OL LL)) hl0 hl ?_ ?_
  · intro x y hxy
    have h1 : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (x : W.DD T) =
        (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (y : W.DD T) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  · intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (PowerSeries.C ((l : ℕ) : ℤ_[l])) =
        fun _ => PowerSeries.C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) PowerSeries.X = fun _ => PowerSeries.X := by
      funext i
      simp [zlA]
    exact GlobalTheory.HWL.mem_smul_of_projective_comp _ hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) e1 e2 x y hxy

theorem N_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let _E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (AA K LL) ↥(W.N T)) :=
  fun _ HW _ l _ K s LL h T hT => N_basis_loc (HW l) K s LL h T hT

end GlobalTheory.NL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoGaloisInvariantsTorsionCoeffOfSelmerSetup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.NoGlobalInv

theorem sub_one_mem_of_pow {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {l : ℕ} (hp : l.Prime)
    (hl : (l : Λ) ∈ IsLocalRing.maximalIdeal Λ) (u : Λ) {n : ℕ} (hu : u ^ (l ^ n) = 1) :
    u - 1 ∈ IsLocalRing.maximalIdeal Λ := by
  haveI := Fact.mk hp
  have h0 : ((l : ℕ) : IsLocalRing.ResidueField Λ) = 0 := by
    rw [← map_natCast (IsLocalRing.residue Λ)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField Λ) l := (CharP.charP_iff_prime_eq_zero hp).2 h0
  rw [← IsLocalRing.residue_eq_zero_iff]
  have h1 : (IsLocalRing.residue Λ u - 1) ^ (l ^ n) = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hu]; simp
  simpa using pow_eq_zero_iff (pow_pos hp.pos n).ne' |>.1 h1

theorem exists_socle {Λ M : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] (I : Ideal Λ) (S : Submodule Λ M) :
    ∀ (n : ℕ) (x : M), x ∈ S → x ≠ 0 → (∀ a ∈ I ^ n, a • x = 0) →
      ∃ y ∈ S, y ≠ 0 ∧ ∀ a ∈ I, a • y = 0 := by
  intro n
  induction n with
  | zero => intro x _ hx h; exact absurd (by simpa using h 1 (by simp)) hx
  | succ n ih =>
    intro x hS hx h
    by_cases h1 : ∀ a ∈ I, a • x = 0
    · exact ⟨x, hS, hx, h1⟩
    push Not at h1
    obtain ⟨a, ha, hax⟩ := h1
    refine ih (a • x) (S.smul_mem a hS) hax fun b hb => ?_
    rw [smul_smul]
    exact h _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hb ha)

theorem eq_zero_of_span {Γ O Λ B : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ]
    [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ → Matrix (Fin r) (Fin r) O)
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) = ⊤)
    (x : Fin r → B) (hx : ∀ a ∈ IsLocalRing.maximalIdeal O, ∀ j, algebraMap O Λ a • x j = 0)
    (hs : ∀ g, ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (ρ g p q) • x q = algebraMap O Λ c • x p) : x = 0 := by
  classical
  have key : ∀ M : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), ∃ A : Matrix (Fin r) (Fin r) O,
      A.map (IsLocalRing.residue O) = M ∧
        ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro M
    have hM : M ∈ Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) := hρ ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M h => obtain ⟨g, rfl⟩ := h; exact ⟨ρ g, rfl, hs g⟩
    | zero => exact ⟨0, by ext; simp, 0, by simp⟩
    | add M M' _ _ h h' =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨A', rfl, c', hc'⟩ := h'
      refine ⟨A + A', by ext; simp, c + c', fun p => ?_⟩
      simp only [Matrix.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib, hc, hc']
    | smul t M _ h =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
      refine ⟨t • A, by ext; simp, t * c, fun p => ?_⟩
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum, hc]
  have key2 : ∀ A : Matrix (Fin r) (Fin r) O,
      ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro A
    obtain ⟨A', hA, c, hc⟩ := key (A.map (IsLocalRing.residue O))
    refine ⟨c, fun p => ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : A p q - A' p q ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (congrFun (congrFun hA p) q).symm
    have := hx _ this q
    rwa [map_sub, sub_smul, sub_eq_zero] at this
  funext b
  haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
  obtain ⟨a, hab⟩ := exists_ne b
  obtain ⟨c, hc⟩ := key2 (Matrix.single a b 1)
  obtain ⟨c', hc'⟩ := key2 (Matrix.single b b 1)
  have h1 := hc a
  have h2 := hc' a
  have h3 := hc' b
  simp [Matrix.single_apply, hab.symm, apply_ite, ite_smul] at h1 h2 h3
  rw [Pi.zero_apply, h3, h1, smul_comm, ← h2, smul_zero]

theorem invariants_eq_bot {Γ O Λ B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ]
    [Algebra O Λ] [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ)
    (κ : Γ →* Λˣ) (hloc : IsLocalHom (algebraMap O Λ))
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤)
    (hκ : ∀ g, ((κ g : Λˣ) : Λ) - 1 ∈ IsLocalRing.maximalIdeal Λ) (hB : Tors Λ B) :
    (repOn (twGL ρ χ) κ B).invariants = ⊥ := by
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ a ∈ IsLocalRing.maximalIdeal Λ :=
    fun a ha hu => ha (hloc.map_nonunit a hu)
  rw [eq_bot_iff]
  intro x hx
  by_contra hx0
  choose n hn using fun j => hB (x j)
  obtain ⟨y, hy, hy0, hym⟩ := exists_socle (IsLocalRing.maximalIdeal Λ) _
    (Finset.univ.sup n) x hx hx0 (fun a ha => funext fun j =>
      hn j a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ j)) ha))
  refine hy0 (eq_zero_of_span (O := O) (Λ := Λ) hr (fun g => (ρ g : Matrix (Fin r) (Fin r) O)) hρ y
    (fun a ha j => congrFun (hym _ (hm a ha)) j) fun g => ⟨(χ g : O), fun p => ?_⟩)
  have hk' : ∀ q, ((κ g : Λˣ) : Λ) • y q = y q := fun q => by
    have := congrFun (hym _ (hκ g)) q
    rwa [Pi.smul_apply, sub_smul, one_smul, Pi.zero_apply, sub_eq_zero] at this
  have hg : ((κ g : Λˣ) : Λ) • ∑ q, algebraMap O Λ ((twGL ρ χ g : Matrix (Fin r) (Fin r) O) p q) • y q = y p :=
    congrFun (hy g) p
  rw [← hg, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_comm ((κ g : Λˣ) : Λ), hk', smul_smul, ← map_mul]
  congr 2
  simp [twGL, scalGL, Matrix.diagonal_mul]

theorem noInv (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)) (h : Setup bkP i s κ Q) : NoInv i s κ := by
  intro B _ _ _ _ hB
  have hloc := h.2.1
  have hr : 100 ≤ D.R.r := h.1.2.2.2.2.2.2
  have hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))
  have hl : ((X.l i : ℕ) : Λ) ∈ IsLocalRing.maximalIdeal Λ := fun hu =>
    hl0 (hloc.map_nonunit _ (by simpa using hu))
  refine invariants_eq_bot (by omega) (X.rhoS i s) (chiS i s) κ hloc h.1.2.1.1 (fun g => ?_) hB
  obtain ⟨m, hgm⟩ := h.2.2.2.2.1 g
  exact sub_one_mem_of_pow (X.lPrime i).out hl _ (n := m)
    (by rw [← Units.val_pow_eq_pow_val, hgm, Units.val_one])

end GlobalTheory.NoGlobalInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptySubquotEquiv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.LocEulerScalars

theorem nonempty_subquot_equiv {R R' X : Type*} [Ring R] [Ring R'] [AddCommGroup X] [Module R X]
    [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    Nonempty ((Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype)) := by
  refine ⟨Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => ?_⟩
  change (B.comap Z.subtype).quotientRel a b ↔
    (B'.comap Z'.subtype).quotientRel (Equiv.subtypeEquivRight hZ a) (Equiv.subtypeEquivRight hZ b)
  rw [Submodule.quotientRel_def, Submodule.quotientRel_def, Submodule.mem_comap,
    Submodule.mem_comap]
  exact hB _

theorem localEulerChar_above : LocalFiniteness → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (ρ : Representation Λ (Dec (F := F) A) M), (∀ m : M, l • m = 0) → IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ContAction ρ → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ ReciprocityTheory.Gal.locDeg v := by
  intro hF hE F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ A v ρ hl hA hv hc

  let _ : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule fun m => by rw [pow_one]; exact hl m
  let ρ' : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M := zmodRep (l ^ 1) ρ
  have hc' : ContAction ρ' := hc

  have hd : ∀ c : Dec (F := F) A → M, d1 ρ c = d1 ρ' c := fun c => by
    funext p
    obtain ⟨g, h⟩ := p
    rw [d1_apply, d1_apply]
    rfl
  have hZ1 : ∀ f, f ∈ Z1 ρ ↔ f ∈ Z1 ρ' := fun f => by
    rw [mem_Z1_iff_cocycle, mem_Z1_iff_cocycle]
    exact Iff.rfl
  have hB1 : ∀ f, f ∈ B1 ρ ↔ f ∈ B1 ρ' := fun f => by
    rw [mem_coboundaries1, mem_coboundaries1]
    exact Iff.rfl
  have hZ2 : ∀ f, f ∈ Z2 ρ ↔ f ∈ Z2 ρ' := fun f => by
    rw [mem_cocycles2, mem_cocycles2]
    exact Iff.rfl
  have hB2 : ∀ f, f ∈ B2 ρ ↔ f ∈ B2 ρ' := fun f => by
    rw [separated_dvr_second_cohomology_mem, separated_dvr_second_cohomology_mem]
    simp only [hd]
  obtain ⟨e1⟩ := nonempty_subquot_equiv (Z1 ρ) (B1 ρ) (Z1 ρ') (B1 ρ') hZ1 hB1
  obtain ⟨e2⟩ := nonempty_subquot_equiv (Z2 ρ) (B2 ρ) (Z2 ρ') (B2 ρ') hZ2 hB2
  have c1 : Nat.card (H1 ρ) = Nat.card (H1 ρ') := Nat.card_congr e1
  have c2 : Nat.card (H2 ρ) = Nat.card (H2 ρ') := Nat.card_congr e2

  obtain ⟨-, h1, h2, -⟩ := hF F Ω l 1 M A ρ' v Nat.one_pos hA hc'
  have hχ := (hE F Ω l 1 M A ρ' v Nat.one_pos hA hc').1 hv
  refine ⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩
  rw [c1, c2]
  convert hχ using 3

  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

end GlobalTheory.LocEulerScalars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUntiltExtensionFinsetSumSubLe
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem untilt_ext_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [NormedField F] (ι : Fl l →+* F)
    (tsh : F →*₀ ℂ_[l]),
    (∀ z, ‖tsh z‖ = ‖z‖) → (∀ x, tsh (ι x) = sh x) → (∀ z : F, ‖z‖ ≤ 1 → ∃ x, ι x = z) →
    ∀ (α : Type) (s : Finset α) (z : α → F) (R : ℝ), 0 ≤ R → (∀ a ∈ s, ‖z a‖ ≤ R) →
      ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖(l : ℂ_[l])‖ * R := by
  intro l _ F _ ι tsh hn hι hsurj α s z R hR hz
  classical
  obtain ⟨-, -, -, -, -, hon, -, -⟩ := GlobalTheory.PSer.Laws.sh_laws l
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := GlobalTheory.PSer.Laws.norm_l
  have hlpos : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by rw [hl]; exact inv_lt_one_of_one_lt₀ hlpos
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := by rw [hl]; exact inv_pos.2 (by linarith)
  obtain ⟨w, hw⟩ := hon (l : ℂ_[l]) hl1.le
  have hnw : ‖ι w‖ = ‖(l : ℂ_[l])‖ := by rw [← hn, hι, hw]

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖ι w‖ ^ N * R ≤ 1 := by
    rcases le_or_gt R 1 with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (by linarith : (0:ℝ) < R)) (hnw ▸ hl1)
      refine ⟨N, ?_⟩
      have := mul_lt_mul_of_pos_right hN (by linarith : (0:ℝ) < R)
      rw [inv_mul_cancel₀ (by linarith)] at this
      exact this.le
  set c : F := ι w ^ N with hc
  have hcn : ‖c‖ = ‖ι w‖ ^ N := by rw [hc, norm_pow]
  have hcpos : 0 < ‖c‖ := by rw [hcn, hnw]; exact pow_pos hl0 N
  have hx : ∀ a, ∃ x : Fl l, ι x = if a ∈ s then c * z a else 0 := by
    intro a
    split_ifs with ha
    · refine hsurj _ ?_
      rw [norm_mul, hcn]
      calc ‖ι w‖ ^ N * ‖z a‖ ≤ ‖ι w‖ ^ N * R :=
            mul_le_mul_of_nonneg_left (hz a ha) (pow_nonneg (norm_nonneg _) _)
        _ ≤ 1 := hN
    · exact ⟨0, map_zero ι⟩
  choose x hxe using hx
  have hxa : ∀ a ∈ s, ι (x a) = c * z a := fun a ha => by rw [hxe, if_pos ha]
  have hsa : ∀ a ∈ s, sh (x a) = tsh c * tsh (z a) := fun a ha => by
    rw [← hι, hxa a ha, map_mul]
  have hss : sh (∑ a ∈ s, x a) = tsh c * tsh (∑ a ∈ s, z a) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hι, map_sum, Finset.sum_congr rfl hxa, ← Finset.mul_sum, map_mul]
  have hbd : ∀ a ∈ s, ‖sh (x a)‖ ≤ ‖c‖ * R := fun a ha => by
    rw [hsa a ha, norm_mul, hn, hn]
    exact mul_le_mul_of_nonneg_left (hz a ha) (norm_nonneg _)
  have key := (untilt_sum_sub_le l α s (‖c‖ * R) x (mul_nonneg (norm_nonneg _) hR) hbd).1
  rw [hss, Finset.sum_congr rfl hsa, ← Finset.mul_sum, ← mul_sub, norm_mul, hn] at key
  have : ‖c‖ * ‖tsh (∑ a ∈ s, z a) - ∑ a ∈ s, tsh (z a)‖ ≤ ‖c‖ * (‖(l : ℂ_[l])‖ * R) := by
    linarith [key]
  exact le_of_mul_le_mul_left this hcpos

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialTeichmullerRootTaylorModFil
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.ExpImage.PolyTaylor

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {R : Type*} [CommRing R]

theorem eval₂_mem_zero (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 0) (q : Polynomial R) : q.eval₂ φ τ ∈ FilB P 0 := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Submodule.sum_mem _ fun k _ => FilB_zero_mul (hφ _) (by simpa using FilB_pow hτ k)

theorem trunc_mul_sub_mem (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 1) (m : ℕ) (f g : PowerSeries R) :
    (f.trunc m).eval₂ φ τ * (g.trunc m).eval₂ φ τ - ((f * g).trunc m).eval₂ φ τ ∈
      FilB P (m : ℤ) := by
  have hd : Polynomial.X ^ m ∣ f.trunc m * g.trunc m - (f * g).trunc m := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd,
      PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g hd, ← Polynomial.coe_mul,
      Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hd
  rw [← Polynomial.eval₂_mul, ← Polynomial.eval₂_sub, hq, Polynomial.eval₂_mul,
    Polynomial.eval₂_X_pow, mul_comm]
  exact FilB_zero_mul (eval₂_mem_zero φ hφ (FilB_anti zero_le_one hτ) q)
    (by simpa using FilB_pow hτ m)

theorem eval₂_sub_trunc_mem (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 1) (m : ℕ) (E : PowerSeries R) {v : P.R.BdR} (hv : v ∈ FilB P 0)
    (hE : v - (E.trunc m).eval₂ φ τ ∈ FilB P (m : ℤ)) (p : Polynomial R) :
    p.eval₂ φ v - ((Polynomial.aeval E p).trunc m).eval₂ φ τ ∈ FilB P (m : ℤ) := by
  have hτ0 := FilB_anti zero_le_one hτ
  induction p using Polynomial.induction_on with
  | C a =>
    rcases m with _ | m
    · exact sub_mem (eval₂_mem_zero φ hφ hv _) (eval₂_mem_zero φ hφ hτ0 _)
    · rw [Polynomial.aeval_C, ← PowerSeries.C_eq_algebraMap, PowerSeries.trunc_C]
      simp
  | add p q hp hq =>
    have := add_mem hp hq
    rw [map_add (f := _), map_add (f := _), Polynomial.eval₂_add, Polynomial.eval₂_add]
    convert this using 1
    ring
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_X]
    have h1 := FilB_zero_mul hv h
    have h2 := FilB_zero_mul (eval₂_mem_zero φ hφ hτ0
      ((Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n)).trunc m)) hE
    have h3 := trunc_mul_sub_mem φ hφ hτ m
      (Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n)) E
    have := add_mem (add_mem h1 h2) h3
    convert this using 1
    ring

theorem poly_taylor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (s : ℕ) (ζ : ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) → ∀ (p : Polynomial ↥LL.1) (m : ℕ), Polynomial.eval₂ (ι : ↥LL.1 →+* P.R.BdR) (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) p - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) p)) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k ∈ GlobalTheory.ExpImage.FilB P (m : ℤ) := by
  intro l _ P AI T LL s ζ ι hζ p m
  have hφ : ∀ x, (ι : ↥LL.1 →+* P.R.BdR) x ∈ FilB P 0 := EmbFil.emb_mem_fil_zero l P AI T LL ι
  have hτ : (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB ∈ FilB P 1 := by
    rw [Algebra.smul_def]
    exact qB_mul_mem _ tD_mem
  have hv : P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1)) ∈ FilB P 0 := io_mem AI _
  have key := eval₂_sub_trunc_mem (ι : ↥LL.1 →+* P.R.BdR) hφ hτ m
    (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) hv ?_ p
  · rw [PowerSeries.eval₂_trunc_eq_sum_range] at key
    exact key
  rcases m with _ | m
  · exact sub_mem hv (eval₂_mem_zero _ hφ (FilB_anti zero_le_one hτ) _)
  have h := _root_.GlobalTheory.ExpImage.epsT_pow_taylor l P AI T s 1 (m + 1)
  rw [map_sub (PowerSeries.trunc (m + 1)), PowerSeries.trunc_one, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, PowerSeries.eval₂_trunc_eq_sum_range, ← io_apply, map_sub, map_one,
    sub_sub_sub_cancel_right]
  rw [pow_one, pow_one, Finset.mul_sum] at h
  suffices hs : ∑ k ∈ Finset.range (m + 1), (ι : ↥LL.1 →+* P.R.BdR)
      (PowerSeries.coeff k (PowerSeries.C ζ * PowerSeries.exp ↥LL.1)) *
        ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k = ∑ k ∈ Finset.range (m + 1), oB P (P.ζQ s) *
          (qB P ((((1 : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ k / (k.factorial : ℚ_[l])) * tD P ^ k) by
    rw [hs]
    exact h
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ι (algebraMap ℚ ↥LL.1 (1 / (k.factorial : ℚ))) = qB P (1 / (k.factorial : ℚ_[l])) := by
    rw [← ι.commutes]
    congr 1
    simp
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_exp, map_mul, RingHom.coe_coe, hζ, hk,
    Algebra.smul_def, mul_pow, ← map_pow, mul_assoc, ← mul_assoc (qB P _), ← map_mul]
  congr 3
  simp [div_eq_mul_inv, mul_comm]

end GlobalTheory.ExpImage.PolyTaylor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductMapTensorAinfToBcrisWachInclusionConstantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productMap_tensorAinfToBcris_wachInclusion_constants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), (∀ c : ↥(K0 K), ι (Γ.emb i c) = algebraMap ↥(K0 K) P.R.BdR c) → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), Algebra.TensorProduct.productMap ι P.ιB (β (I.io (fun j => PowerSeries.C (o j)))) = ι (o i : ↥LL.1) := by
  first | exact @GlobalTheory.EvalIdem.component_const | exact GlobalTheory.EvalIdem.component_const | (intros; apply GlobalTheory.EvalIdem.component_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictNormalHomMemLowerRamificationGroupZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem restrictNormalHom_mem_lowerRamificationGroup_zero : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (σ : GQ l), (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → AlgEquiv.restrictNormalHom L σ ∈ lowerRamificationGroup ℚ_[l] L 0 := by
  intro l _ L _ _ _ _ _ _ _ _ _ _ σ hσ
  rw [mem_lowerRamificationGroup_iff]
  intro x
  have h01 : ((0 : ℤ) + 1).toNat = 1 := rfl
  rw [h01, pow_one]
  have hx : ‖algebraMap L (Om l) (x : L)‖ ≤ 1 := ((_root_.GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt l L (x : L)).1).1 x.2
  have hc : algebraMap L (Om l) (AlgEquiv.restrictNormalHom L σ (x : L)) = σ (algebraMap L (Om l) (x : L)) :=
    AlgEquiv.restrictNormal_commutes σ L (x : L)
  have hlt : valuation L (AlgEquiv.restrictNormalHom L σ (x : L) - (x : L)) < 1 := by
    rw [(_root_.GlobalTheory.PMon.Ram.mem_integer_iff_norm_le_and_valuation_lt_one_iff_norm_lt l L _).2, map_sub, hc]
    exact hσ _ hx
  intro hu
  have h1 := (Valuation.integer.integers (valuation L)).isUnit_iff_valuation_eq_one.1 hu
  have h2 : ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) =
      AlgEquiv.restrictNormalHom L σ (x : L) - (x : L) := rfl
  change valuation L ((((integerAlgEquiv ℚ_[l] L) ((AlgEquiv.restrictNormalHom L) σ)) x - x : 𝒪[L]) : L) = 1 at h1
  rw [h2] at h1
  exact hlt.ne h1

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_descent_conditions_every_localisation : ∀ (D : D7) (i : D.nd.Loc), TameCharacterConditions D i ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions (D := D) i := by
  first | exact @GlobalTheory.TameDesign.main | exact GlobalTheory.TameDesign.main | (intros; apply GlobalTheory.TameDesign.main <;> assumption)
end

