module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfOrthoB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MeasureImageCosets
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0013

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GenSmulMem
section
noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem gen_mem (a : 𝓞 E) : inclR (F := F) (Fv F v) (a : E) ∈ OEv (E := E) v :=
  Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩

theorem gen_mul_mem (a : 𝓞 E) (y : Fv F v ⊗[F] E) (hy : y ∈ OEv (E := E) v) :
    inclR (F := F) (Fv F v) (a : E) * y ∈ OEv (E := E) v := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, -, rfl⟩ := hx
    rw [← map_mul]
    exact_mod_cast gen_mem v (a * b)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem oSub : OSub (E := E) v := by
  refine ⟨?_, ?_⟩
  · have := gen_mem (E := E) v 1
    simpa using this
  · intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, -, rfl⟩ := hz
      exact gen_mul_mem v b y hy
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
    | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem gen_smul_mem (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (a : 𝓞 E) (x : Fin n → Fv F v ⊗[F] E) (hx : x ∈ latLoc (E := E) v Λ) :
    inclR (F := F) (Fv F v) (a : E) • x ∈ latLoc (E := E) v Λ := by
  obtain ⟨L, -, rfl⟩ := hL
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hal : a • l ∈ L := L.smul_mem a hl
    have : inclR (F := F) (Fv F v) (a : E) • ratV (F := F) (Fv F v) l = ratV (F := F) (Fv F v) (a • l) := by
      funext i
      simp only [ratV, Pi.smul_apply, smul_eq_mul, ← map_mul]
      rfl
    rw [this]
    exact Submodule.subset_span ⟨_, hal, rfl⟩
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ r hx

theorem oSmul : OSmul v Λ := by
  intro hL c hc x hx
  induction hc using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, -, rfl⟩ := hz
    exact gen_smul_mem v Λ hL b x hx
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add c c' _ _ hc hc' => rw [add_smul]; exact Submodule.add_mem _ hc hc'
  | smul r c _ hc => rw [smul_assoc]; exact Submodule.smul_mem _ r hc

end PI.OmLocU.Orb
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRAddSmul
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def lamA (a : ℕ) : AddSubgroup (TupV (E := E) v n a) where
  carrier := LamT v Λ a
  add_mem' := fun hx hy i => (latLoc (E := E) v Λ).add_mem (hx i) (hy i)
  zero_mem' := fun _ => (latLoc (E := E) v Λ).zero_mem
  neg_mem' := fun hx i => (latLoc (E := E) v Λ).neg_mem (hx i)

def lamP (a : ℕ) (ϖ : Fv F v) : AddSubgroup (TupV (E := E) v n a) :=
  (lamA v Λ a).map (DistribSMul.toAddMonoidHom (TupV (E := E) v n a) (sc (E := E) v ϖ))

def clsU (a : ℕ) (ϖ : Fv F v) (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    Set (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) :=
  QuotientAddGroup.mk '' {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ T}

def MeasU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    MeasurableAdd (TupV (E := E) v n a) ∧ MeasurableSet (LamT v Λ a) ∧
      MeasurableSet (lamP v Λ a ϖ : Set (TupV (E := E) v n a))

def IdxU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a)

def ClsU (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ℝ) =
      qv v ^ (2 * n * a - a ^ 2) * prodEta (E := E) v n a

theorem hR_add_smul (s : Fv F v ⊗[F] E) (x z y w : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + s • z) (y + s • w) = hR (Fv F v) σ J x y + s * hR (Fv F v) σ J x w +
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ s * hR (Fv F v) σ J z y + Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ s * s * hR (Fv F v) σ J z w := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sigR_sc (x : Fv F v) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (sc (E := E) v x) = sc (E := E) v x := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, sc]

theorem unif_int {ϖ : Fv F v} (hϖ : IsUnif v ϖ) : ϖ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, hϖ]
  exact_mod_cast (show Multiplicative.ofAdd (-1 : ℤ) ≤ 1 by
    rw [← ofAdd_zero, Multiplicative.ofAdd_le]; norm_num)

theorem sc_mul_mem {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) {c : Fv F v ⊗[F] E}
    (hc : c ∈ OEv (E := E) v) : sc (E := E) v x * c ∈ OEv (E := E) v := by
  have h := (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).smul_mem
    (⟨x, hx⟩ : v.adicCompletionIntegers F) hc
  have e : (⟨x, hx⟩ : v.adicCompletionIntegers F) • c = sc (E := E) v x * c := by
    show x • c = sc (E := E) v x * c
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  rw [e] at h
  exact h

theorem oev_add {c d : Fv F v ⊗[F] E} (hc : c ∈ OEv (E := E) v) (hd : d ∈ OEv (E := E) v) :
    c + d ∈ OEv (E := E) v :=
  (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).add_mem hc hd

theorem nearT_add {a : ℕ} (hSD : IsSDLoc σ J v Λ) {ϖ : Fv F v} (hϖ : IsUnif v ϖ)
    (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (X Z : TupV (E := E) v n a)
    (hX : X ∈ LamT v Λ a) (hZ : Z ∈ LamT v Λ a) (hN : X ∈ NearT v σ J ϖ T) :
    X + sc (E := E) v ϖ • Z ∈ NearT v σ J ϖ T := by
  intro i j
  obtain ⟨c, hc, hce⟩ := hN i j
  have hh : ∀ p q : Fin a, ∀ P Q : TupV (E := E) v n a, P ∈ LamT v Λ a → Q ∈ LamT v Λ a →
      hR (Fv F v) σ J (P p) (Q q) ∈ OEv (E := E) v :=
    fun p q P Q hP hQ => (hSD (Q q)).1 (hQ q) (P p) (hP p)
  have hi := unif_int v hϖ
  refine ⟨c + (hR (Fv F v) σ J (X i) (Z j) + hR (Fv F v) σ J (Z i) (X j) +
      sc (E := E) v ϖ * hR (Fv F v) σ J (Z i) (Z j)), ?_, ?_⟩
  · exact oev_add v hc (oev_add v (oev_add v (hh i j X Z hX hZ) (hh i j Z X hZ hX))
      (sc_mul_mem v hi (hh i j Z Z hZ hZ)))
  · have e1 : gramR (Fv F v) σ J (X + sc (E := E) v ϖ • Z) i j =
        hR (Fv F v) σ J (X i + sc (E := E) v ϖ • Z i) (X j + sc (E := E) v ϖ • Z j) := rfl
    have e2 : gramR (Fv F v) σ J X i j = hR (Fv F v) σ J (X i) (X j) := rfl
    rw [e1, hR_add_smul, sigR_sc]
    rw [e2] at hce
    linear_combination hce

theorem countU_of (a : ℕ) (Y : TupV (E := E) v n a) (hM : MeasU σ J ψ v Λ a Y)
    (hI : IdxU σ J ψ v Λ a Y) (hC : ClsU σ J ψ v Λ a Y) : CountU σ J ψ v Λ a Y := by
  intro hG hμ ϖ hϖ
  obtain ⟨hMA, hL, hP⟩ := hM hG ϖ hϖ
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  have ha : a ≤ n := hG.2.2.2.2.1
  have hq := qv_pos v
  set μ := dX σ J ψ v a with hμdef
  have : μ.IsAddHaarMeasure := by
    rw [hμdef, dX, dite_eq_left hμ]
    exact hμ.choose_spec.1
  have hPL : lamP v Λ a ϖ ≤ lamA v Λ a := by
    rintro _ ⟨Z, hZ, rfl⟩ i
    have : (sc (E := E) v ϖ • Z) i = sc (E := E) v ϖ • Z i := rfl
    show (sc (E := E) v ϖ • Z) i ∈ latLoc (E := E) v Λ
    rw [this]
    have e : sc (E := E) v ϖ • Z i = (⟨ϖ, unif_int v hϖ⟩ : v.adicCompletionIntegers F) • Z i := by
      ext p
      simp only [Pi.smul_apply, smul_eq_mul]
      show _ = ϖ • Z i p
      rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
      rfl
    rw [e]
    exact (latLoc (E := E) v Λ).smul_mem _ (hZ i)
  have hIdx := hI hG ϖ hϖ
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h0
    have : qv v = 0 := by simp [qv, h0]
    linarith
  have hfin : (lamP v Λ a ϖ).relIndex (lamA v Λ a) ≠ 0 := by
    rw [hIdx]; exact pow_ne_zero _ hN0
  have eL := PI.VolStabSW.measure_eq_relIndex_mul μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hL hP hfin
  have eS := measure_image_cosets μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hP hfin
    {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)}
    (by
      rintro x hx y ⟨Z, hZ, hZe⟩
      simp only [Set.mem_setOf_eq]
      rw [AddSubgroup.coe_add, ← hZe]
      exact nearT_add σ J v Λ hSD hϖ _ _ _ x.2 hZ hx)
  have himg : ((↑) : lamA v Λ a → TupV (E := E) v n a) ''
      {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)} =
      LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext X
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨X, h1⟩, h2, rfl⟩
  rw [himg] at eS
  have eL' : μ (LamT v Λ a) = (((lamP v Λ a ϖ).relIndex (lamA v Λ a) : ℕ) : ENNReal) *
      μ (lamP v Λ a ϖ) := eL
  rw [eS, eL', ← mul_assoc]
  congr 1
  have hcard := hC hG ϖ hϖ
  change (Nat.card (clsU σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ENNReal) = _
  rw [← ENNReal.ofReal_natCast, hcard, hIdx, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]
  · congr 1
    have hqv : ((Ideal.absNorm v.asIdeal ^ (2 * n * a) : ℕ) : ℝ) = qv v ^ (2 * n * a) := by
      simp [qv]
    rw [hqv]
    have hle : a ^ 2 ≤ 2 * n * a := by nlinarith
    have e3 : qv v ^ (2 * n * a) = qv v ^ (2 * n * a - a ^ 2) * qv v ^ (a ^ 2) := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e3]
    have e4 : qv v ^ (-((a : ℤ) ^ 2)) * qv v ^ (a ^ 2) = 1 := by
      rw [zpow_neg, show ((a : ℤ) ^ 2) = ((a ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero _ hq.ne')
    linear_combination (-(qv v ^ (2 * n * a - a ^ 2) * prodEta (E := E) v n a)) * e4
  · have hP0 : 0 ≤ prodEta (E := E) v n a := by
      unfold prodEta
      refine Finset.prod_nonneg fun j _ => ?_
      have hq1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
      have habs : |((etaV (E := E) v : ℤ) : ℝ)| = 1 := by
        unfold etaV; split_ifs <;> norm_num
      have h1 : ((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := by
        calc _ ≤ |((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))| :=
              le_abs_self _
          _ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
              rw [abs_mul, abs_pow, habs, one_pow, one_mul, abs_of_nonneg (zpow_nonneg (by linarith) _)]
          _ ≤ 1 := zpow_le_one_of_nonpos₀ hq1 (by omega)
      linarith
    exact mul_nonneg (zpow_nonneg hq.le _) hP0

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory Topology
  Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem smul_eq_sc (r : Fv F v) (x : Fv F v ⊗[F] E) : r • x = sc (E := E) v r * x := by
  rw [Algebra.smul_def]
  rfl

theorem sc_mul (r s : Fv F v) : sc (E := E) v r * sc (E := E) v s = sc (E := E) v (r * s) := by
  unfold sc
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := rfl

theorem mem_uniformizer_hermitian_ideal (ϖ : Fv F v) (h0 : ϖ ≠ 0) (a : ℕ) (z : HermR (Fv F v) σ a) :
    z ∈ hN σ v ϖ a 0 ↔ ∀ i j, (z : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ PO (E := E) v ϖ := by
  unfold hN
  rw [PI.VolStabSW.mem_smulSub]
  constructor
  · rintro ⟨p, hp, rfl⟩ i j
    refine ⟨(p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, hp i j, ?_⟩
    rw [PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, pow_one, smul_eq_sc]
  · intro hz
    refine ⟨ϖ⁻¹ • z, ?_, ?_⟩
    · intro i j
      obtain ⟨c, hc, e⟩ := hz i j
      show ((ϖ⁻¹ • z : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v
      rw [PI.VolStabSW.coe_hermSMul, Matrix.smul_apply, e, smul_eq_sc, ← mul_assoc, sc_mul,
        inv_mul_cancel₀ h0, sc_one, one_mul]
      exact hc
    · rw [pow_one, smul_smul, mul_inv_cancel₀ h0, one_smul]

theorem latLoc_smul {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {x : Fin n → Fv F v ⊗[F] E}
    (hx : x ∈ latLoc (E := E) v Λ) : r • x ∈ latLoc (E := E) v Λ :=
  (latLoc (E := E) v Λ).smul_mem ⟨r, hr⟩ hx

theorem lamS_smul {a : ℕ} {r : Fv F v} (hr : r ∈ v.adicCompletionIntegers F) {x : TupV (E := E) v n a}
    (hx : x ∈ lamS v Λ a) : r • x ∈ lamS v Λ a :=
  fun i => latLoc_smul v Λ hr (hx i)

theorem fibU'_of (a : ℕ) (Y : TupV (E := E) v n a) (h1 : LamOC v Λ a) (h2 : HermOC σ v a)
    (h3 : FibHens σ J ψ v Λ a Y) : FibU' σ J ψ v Λ a Y := by
  intro hG hW hH hfib ϖ hϖ
  have hG' := hG
  obtain ⟨hS, hL, hSD, hUn, ha, hP, hdet⟩ := hG
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hS.1.2.2.2
  have hJ : ∀ i j, σ (J j i) = J i j := hS.2.1.1
  obtain ⟨h0, hπ, hint⟩ := unif_spec v ϖ hϖ
  obtain ⟨hLo, hLc⟩ := h1 hL
  obtain ⟨hHo', hHc'⟩ := h2
  have := PI.VolStabSW.secondCountable_Fv F v
  have := PI.VolStabSW.locallyCompact_Fv F v
  have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have hμ : SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
    unfold dX; rw [dite_eq_left hW]; exact hW.choose_spec
  have hν : SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
    unfold dT; rw [dite_eq_left hH]; exact hH.choose_spec
  have := hμ.1
  have := hν.1
  have hfibC : IsOm σ J ψ v a (omFam σ J ψ v a) := by
    unfold omFam; rw [dite_eq_left hfib]; exact hfib.choose_spec
  have hTm := PI.VolStabSW.gramR_mem (Fv F v) σ hσ J hJ Y
  have hom : omAt σ J ψ v (gramR (Fv F v) σ J Y) =
      omFam σ J ψ v a (PI.VolStabSW.gramH (Fv F v) σ hσ J hJ Y) := by
    unfold omAt; rw [dite_eq_left hTm]; rfl
  rw [hom]
  set G := PI.VolStabSW.gramH (n := a) (Fv F v) σ hσ J hJ with hGdef
  set T := G Y with hTdef
  set fb := omFam σ J ψ v a with hfb

  have hΛL : lamN v Λ ϖ a 0 ≤ lamS v Λ a := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := (PI.VolStabSW.mem_smulSub _ _ _).1 hx
    exact lamS_smul v Λ (pow_mem hint _) hp
  have hΛo : ∀ k, IsOpen (lamN v Λ ϖ a k : Set (TupV (E := E) v n a)) := fun k =>
    PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hLo
  have hΛc : ∀ k, IsCompact (lamN v Λ ϖ a k : Set (TupV (E := E) v n a)) := fun k =>
    PI.VolStabSW.isCompact_smulSub _ _ hLc
  have hΛa : Antitone (lamN v Λ ϖ a) := by
    intro m k hmk x hx
    simp only [lamN, PI.VolStabSW.mem_smulSub] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨ϖ ^ (k - m) • p, lamS_smul v Λ (pow_mem hint _) hp, ?_⟩
    rw [smul_smul, ← pow_add]
    congr 2
    omega
  have hHo : ∀ k, IsOpen (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) := fun k =>
    PI.VolStabSW.isOpen_smulSub _ (pow_ne_zero _ h0) _ hHo'
  have hHc : ∀ k, IsCompact (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) := fun k =>
    PI.VolStabSW.isCompact_smulSub _ _ hHc'
  have hHb : ∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ k, (hN σ v ϖ a k : Set (HermR (Fv F v) σ a)) ⊆ N' := by
    intro N hN'
    obtain ⟨k, hk⟩ := PI.VolStabSW.eventually_smul_sub (hermOE σ v a : Set (HermR (Fv F v) σ a))
      hHc' (fun k => ϖ ^ (k + 1)) (hπ.comp (tendsto_add_atTop_nat 1)) N hN'
    refine ⟨k, ?_⟩
    simp only [hN, PI.VolStabSW.coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp

  set Nb : Set (HermR (Fv F v) σ a) := {S | IsUnit (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)).det}
    with hNbdef
  have hTu : T ∈ Nb := by
    obtain ⟨w, -, -, hw⟩ := hdet
    exact IsUnit.of_mul_eq_one _ hw
  have hNb : Nb ∈ 𝓝 T :=
    (PI.VolStabSW.isOpen_unitHerm (Fv F v) (PI.VolStabSW.isOpen_units_Fv F v) σ a).mem_nhds hTu
  have hNbU : ∀ x ∈ LamT v Λ a, G x ∈ Nb → x ∈ IndepV (E := E) (n := n) v a := fun x _ hx =>
    PI.VolStabSW.linIndep_of_isUnit_det (Fv F v) σ J x hx
  have hLcl : IsClosed (LamT v Λ a) := AddSubgroup.isClosed_of_isOpen (lamS v Λ a) hLo
  have e := PI.VolStabSW.fibLatGen_holds _ _ _ (dX σ J ψ v a) (dT σ ψ v a) hμ.1 hν.1
    (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective G
    (PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ) (fun _ => rfl) (IndepV (E := E) (n := n) v a)
    Set.univ fb hfibC T Filter.univ_mem (lamS v Λ a) hLo hLc (lamN v Λ ϖ a) (hN σ v ϖ a) hΛL hΛo hΛc
    hΛa hHo hHc hHb (LamT v Λ a) subset_rfl (fun y hy Z hZ => (lamS v Λ a).add_mem hy (hΛL hZ))
    hLo hLcl Nb hNb hNbU (fun y hy hyT => h3 hG' ϖ hϖ hσ hJ y hy hyT)
  have hA : LamT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a 0} =
      LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [mem_uniformizer_hermitian_ideal σ v ϖ h0]
    rfl
  have hHP : (hN σ v ϖ a 0 : Set (HermR (Fv F v) σ a)) = HermP v σ a ϖ := by
    ext z
    exact mem_uniformizer_hermitian_ideal σ v ϖ h0 a z
  rw [hA, hHP] at e
  have hLm : MeasurableSet (LamT v Λ a) := hLo.measurableSet
  have hind : (LamT v Λ a).indicator (1 : TupV (E := E) v n a → ℂ) =
      fun x => (((LamT v Λ a).indicator (1 : TupV (E := E) v n a → ℝ) x : ℝ) : ℂ) := by
    funext x
    by_cases hx : x ∈ LamT v Λ a <;> simp [Set.indicator, hx]
  rw [hind, integral_complex_ofReal, integral_indicator_one hLm] at e
  have e' := Complex.ofReal_injective e

  have hGc : Continuous G := PI.VolStabSW.continuous_gramH (Fv F v) σ hσ J hJ
  obtain ⟨k, hk⟩ := hHb _ ((continuous_const.add continuous_id :
    Continuous fun w : HermR (Fv F v) σ a => T + w).continuousAt.preimage_mem_nhds
      (by simpa using hNb))
  set Q := LamT v Λ a ∩ G ⁻¹' {z | z - T ∈ hN σ v ϖ a k} with hQdef
  have hQo : IsOpen Q :=
    hLo.inter (((hHo k).preimage (continuous_id.sub continuous_const)).preimage hGc)
  have hQcl : IsClosed Q :=
    hLcl.inter (((AddSubgroup.isClosed_of_isOpen _ (hHo k)).preimage
      (continuous_id.sub continuous_const)).preimage hGc)
  have hQc : IsCompact Q := hLc.of_isClosed_subset hQcl Set.inter_subset_left
  have hQU : Q ⊆ IndepV (E := E) (n := n) v a := by
    rintro x ⟨hx, hxk⟩
    refine hNbU x hx ?_
    have := hk hxk
    have e2 : G x = T + (G x - T) := by abel
    rw [e2]
    exact this
  set φ : TupV (E := E) v n a → ℝ := Q.indicator (fun _ => (1 : ℝ)) with hφdef
  have hφc : Continuous φ :=
    (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℝ)) ⟨hQcl, hQo⟩).isLocallyConstant.continuous
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro' hQc hQcl fun x hx => Set.indicator_of_notMem hx _
  have hφU : tsupport φ ⊆ IndepV (E := E) (n := n) v a :=
    (closure_minimal Set.support_indicator_subset hQcl).trans hQU
  obtain ⟨hint', -⟩ := hfibC.2.2 φ hφc hφs hφU
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hfinQ : fb T Q ≠ ⊤ := by
    have h := hint' T (Set.mem_univ _)
    rw [hφdef, integrable_indicator_iff hQm] at h
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 h).resolve_left (by simp) |>.ne
  have hsub : LamT v Λ a ⊆ Q ∪ (gramR (Fv F v) σ J ⁻¹' {(T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))} ∩
      IndepV (E := E) (n := n) v a)ᶜ := by
    intro x hx
    by_cases h : x ∈ gramR (Fv F v) σ J ⁻¹' {(T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))} ∩
      IndepV (E := E) (n := n) v a
    · left
      refine ⟨hx, ?_⟩
      have hGx : G x = T := Subtype.ext h.1
      show G x - T ∈ hN σ v ϖ a k
      rw [hGx, sub_self]
      exact zero_mem _
    · right
      exact h
  have hz := hfibC.1 T
  have hfin : fb T (LamT v Λ a) ≠ ⊤ := by
    refine ((measure_mono hsub).trans_lt (lt_of_le_of_lt (measure_union_le _ _) ?_)).ne
    rw [hz, add_zero]
    exact hfinQ.lt_top
  have hR : dX σ J ψ v a (LamT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y)) /
      dT σ ψ v a (HermP v σ a ϖ) ≠ ⊤ := by
    refine (ENNReal.div_lt_top ?_ ?_).ne
    · exact ((measure_mono Set.inter_subset_left).trans_lt hLc.measure_lt_top).ne
    · rw [← hHP]
      exact ((hHo 0).measure_pos _ ⟨0, (hN σ v ϖ a 0).zero_mem⟩).ne'
  rw [measureReal_def] at e'
  exact (ENNReal.toReal_eq_toReal_iff' hfin hR).1 e'

end PI.OmLocU
end
end

