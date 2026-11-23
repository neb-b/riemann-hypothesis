module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelIffFramesOnPoints
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem frStab_iff_image {P : HeightOneSpectrum (𝓞 E)} {C : Set (Sp E n)} (g : ↥(GLint E n P)) :
    g ∈ frStab P C ↔ (fun v => g.1 v) '' C = C := by
  constructor
  · intro h
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hv
      have e : g.1 ((g⁻¹).1 v) = v := LinearEquiv.apply_symm_apply g.1 v
      refine ⟨(g⁻¹).1 v, ?_, e⟩
      have h' := h ((g⁻¹).1 v)
      rw [e] at h'
      exact h'.1 hv
  · intro h v
    constructor
    · intro hv
      rw [← h] at hv
      obtain ⟨w, hw, e⟩ := hv
      rwa [← g.1.injective e]
    · intro hv
      rw [← h]
      exact ⟨v, hv, rfl⟩

end SlopeTestRemainingChoices

theorem lev_iff_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} [NeZero n] (hc : Formalism.BasicNotions.CMData X.F X.E) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → ∀ (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (r : PtY ST SG Q y) (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar r = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq r = D → ∀ (q : QLoc hc n Q (GlobalTheory.Mem.Col2.ChEx.cutQ Θ D)) {g s : GL (Fin n) (AfE X.F X.E)}, g ∈ UAd hc n → g * s ∈ UAd hc n → ∀ (p : DecoF X.E n ST SG Q), FrExact q g r.1.1 → FrExact q (g * s) p → (s ∈ levUQ hc n ST SG Q (chG Λ C) q ↔ ∃ κ : FrmG Λ Θ, ufGL X.E n κ.1 = 1 ∧ (ya Λ Θ κ r).1.1 = p ∧ bar (ya Λ Θ κ r) = bar r ∧ cq (ya Λ Θ κ r) = cq r) := by
  intro X n ST SG Q y _ hc cq hact Λ Θ r C hC D hD q g s hg hgs p hr hp
  have hmul : ∀ P : Q, q.at P (g * s) = q.at P g * q.at P s := fun P => by simp only [QLoc.at, map_mul]
  have hat : ∀ P : Q, bc (q.phi P) (qGL n (r.1.1.fr P)) * q.at P s = bc (q.phi P) (qGL n (p.fr P)) := fun P => by
    rw [← hr.2 P, ← hp.2 P, hmul]
  have hcq : ∀ κ : FrmG Λ Θ, (∀ P : Q, κ.2.2.1 P ∈ frStab P.1 (D P)) ↔ cq (ya Λ Θ κ r) = cq r := by
    intro κ
    rw [funext_iff]
    refine forall_congr' fun P => ?_
    rw [hact Λ Θ κ r P, hD, frStab_iff_image]
  constructor
  · intro hs
    obtain ⟨hsU, hsQ⟩ := (mem_levUQ q _).1 hs
    have h1 := act_of_mem hc n _ 1 hg ⟨s, hsU⟩
    rw [DecoSet.dia_one, DecoSet.dia_one, hr.1, hp.1] at h1
    have h2 := mem_chG.1 ((Formalism.L2.Col.levRed hc n ST SG _ ⟨s, hsU⟩)⁻¹).2
    have hN : ∀ (P : Q) (x : Sp X.E n), x ∈ p.deco.1.at P.1 ↔ x ∈ r.1.1.deco.1.at P.1 := by
      intro P x
      rw [h1]
      exact (mem_localization_gmap P.1 ((1 : UF X.E n) : Sp X.E n ≃ₗ[X.E] Sp X.E n) r.1.1.deco.1.N x).trans Iff.rfl
    let t : GLQ X.E n Q := fun P => ⟨(r.1.1.fr P)⁻¹ * p.fr P, by
      show ∀ x, _ ↔ _
      intro x
      have A := r.1.1.2 P (((r.1.1.fr P)⁻¹ * p.fr P) x)
      have e : r.1.1.1.2 P (((r.1.1.fr P)⁻¹ * p.fr P) x) = p.fr P x := LinearEquiv.apply_symm_apply _ _
      rw [e] at A
      exact A.symm.trans ((hN P _).symm.trans (p.2 P x))⟩
    have hs_at : ∀ P : Q, q.at P s = bc (q.phi P) (qGL n (t P).1) := fun P => by
      rw [eq_inv_mul_of_mul_eq (hat P)]
      show _ = bc (q.phi P) (qGL n ((r.1.1.fr P)⁻¹ * p.fr P))
      simp only [qGL, map_mul, map_inv]
    have ht : ∀ P : Q, t P ∈ (cutQ Θ D P).H := fun P => by
      refine (q.U_rat P (t P)).1 ?_
      have h' := hsQ P
      rw [hs_at P] at h'
      exact h'
    have hθ : (fun P => (t P)⁻¹ : GLQ X.E n Q) ∈ Θ.grp := fun P _ => inv_mem (Subgroup.mem_inf.1 (ht P)).1
    let κ : FrmG Λ Θ := (1, ⟨_, h2.1⟩, ⟨_, hθ⟩)
    refine ⟨κ, map_one _, ?_, (bar_ya_eq_iff _ _ _ _).2 ?_, (hcq κ).1 fun P => inv_mem (Subgroup.mem_inf.1 (ht P)).2⟩
    · apply Subtype.ext
      apply Prod.ext
      · exact h1.symm
      · funext P
        show 1 * r.1.1.1.2 P * (((t P)⁻¹)⁻¹).1 = p.1.2 P
        rw [inv_inv, one_mul]
        exact mul_inv_cancel_left (r.1.1.fr P) (p.fr P)
    · rw [hC]
      exact h2.2
  · rintro ⟨⟨γ, h, θ⟩, h1, h2, h3, h4⟩
    have : γ = 1 := ufGL_inj hc n (h1.trans (map_one _).symm)
    subst this
    have hdeco : p.deco = ((1 : UF X.E n), h.1) • r.1.1.deco := by
      rw [← h2]
      rfl
    obtain ⟨hJ, hred⟩ := red_of_act hc n 1 hg hgs h.1 (by rw [DecoSet.dia_one, DecoSet.dia_one, hr.1, hp.1, hdeco])
    have hsU : s ∈ levU hc n ST SG (chG Λ C) := (mem_levU hc n ST SG _).2 ⟨hJ, by
      rw [hred]
      refine inv_mem (mem_chG.2 ⟨h.2, ?_⟩)
      rw [← hC]
      exact (bar_ya_eq_iff _ _ _ _).1 h3⟩
    refine (mem_levUQ q _).2 ⟨hsU, fun P => ?_⟩
    have hfr : p.fr P = r.1.1.fr P * ((θ.1 P)⁻¹).1 := by
      rw [← h2]
      show 1 * r.1.1.1.2 P * ((θ.1 P)⁻¹).1 = _
      rw [one_mul]
      rfl
    have hs_at : q.at P s = bc (q.phi P) (qGL n ((θ.1 P)⁻¹).1) := by
      rw [eq_inv_mul_of_mul_eq (hat P), hfr]
      simp only [qGL, map_mul, map_inv, inv_mul_cancel_left]
    rw [hs_at]
    refine (q.U_rat P ((θ.1 P)⁻¹)).2 ?_
    exact inv_mem (Subgroup.mem_inf.2 ⟨θ.2 P trivial, (hcq (1, h, θ)).2 h4 P⟩)

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetTwistPrimeEmptyOrCoset
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem cqOf_empty_or_coset : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (r : PtAt R sel mu cst u j) (P : QE sel (mu : Chr X.F X.E X.K)), GlobalTheory.Mem.Col2.ChEx.cqOf r P = ∅ ∨ ∃ (z : Sp X.E (R.N j)) (c : X.E), c ≠ 0 ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r P = {x | c⁻¹ • (x - z) ∈ stdAt X.E (R.N j) P.1} := by
  intro X Pr R sel S mu cst u j hQ r P
  classical
  have hP : P.1 ∉ Pr.vGs := hQ P.1 P.2
  by_cases hj : j + 1 = R.m
  · right
    have hyb := r.mem_ybSet hj
    simp only [ybSet, Set.mem_setOf_eq] at hyb
    obtain ⟨y0, -, hY⟩ := hyb
    have hq : ((qOf P.1 : X.E) ^ cst.M) ≠ 0 := pow_ne_zero _ (by
      rw [Nat.cast_ne_zero]
      unfold qOf
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.1.ne_bot)
    refine ⟨(frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0, (qOf P.1 : X.E) ^ cst.M, hq, ?_⟩
    ext x
    simp only [cqOf, cosetIn, Set.mem_setOf_eq, if_neg hP]
    constructor
    · rintro ⟨y, hy, hx⟩
      rw [hY] at hy
      have h1 := (mem_locLat _ _ _ _).1 hy ⟨P.1, Finset.mem_union_right _ P.2⟩
      simp only [if_neg hP, zpow_natCast] at h1
      have h2 := (GlobalTheory.ColPeriod.TopTwist.frsF_mem' sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩ hP
        (((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y -
          (frsF sel mu r.1.1 ⟨P.1, Finset.mem_union_right _ P.2⟩).symm y0))).1 (by
        rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        exact h1)
      have h3 := Submodule.add_mem _ hx h2
      convert h3 using 1
      rw [← smul_add]
      congr 1
      abel
    · intro hx
      exact ⟨y0, by rw [hY]; simp, hx⟩
  · left
    have h1 : r.1.2 = ∅ := by
      have := r.2
      rwa [ysAt_ys_of_ne _ _ _ hj] at this
    ext x
    simp [cqOf, cosetIn, h1]

end GlobalTheory.Mem.Col2.ChEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetsInFramesEqIffReductions
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.ChEx

section Pt

open Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem ptAt_cosetG (q : PtAt R sel mu cst u j) (h : j + 1 = R.m) :
    ∃ y : Sp X.E (R.N j), (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) ∧ y ∈ q.1.2 ∧
      ∀ z ∈ q.1.2, ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N := by
  obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
  refine ⟨y, fun w hw => ?_, ?_, fun z hz w hw => ?_⟩
  · have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w, Finset.mem_union_left _ hw⟩
    simpa [hw] using this
  · rw [hY, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  · rw [hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat] at hz
    simpa [hw] using hz ⟨w, Finset.mem_union_left _ hw⟩

theorem cosetIn_eqG (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)} (hy0 : y ∈ q.1.2)
    (hY : ∀ z ∈ q.1.2, ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    cosetIn q P = {z | z - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1} := by
  have hf := GlobalTheory.TopStep.liftFr_spec q.1.1.deco.2 ⟨P.1, hP⟩
  have hfr : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr ⟨P.1, hP⟩ := by
    unfold frsF
    rw [dite_eq_left hP]
  ext z
  simp only [cosetIn, Set.mem_setOf_eq, if_pos hP, pow_zero, inv_one, one_smul, hfr]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y' - (q.1.1.deco.1.liftFr ⟨P.1, hP⟩).symm y ∈ stdAt X.E (R.N j) P.1 := by
      rw [← map_sub]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hY y' hy' P.1 hP)
    have := add_mem hz h1
    rwa [sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, hy0, hz⟩

theorem bar_eqG (q : PtAt R sel mu cst u j) {y : Sp X.E (R.N j)}
    (hy : ∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (hy0 : y ∈ q.1.2)
    (hY : ∀ z ∈ q.1.2, ∀ w ∈ Pr.vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q.1.1.deco.1.N) (w : Pr.vGs) :
    bar q w = {redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)} := by
  have hd := q.1.1.deco.2
  have hf := GlobalTheory.TopStep.liftFr_spec hd w
  have hq := hy w.1 w.2
  have key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) =
      redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y) := by
    rw [← map_smul]
    have hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1 :=
      (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)
    rw [← hf.2 _ hs, LinearEquiv.apply_symm_apply]
  ext v
  simp only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← key]
    have ht : z - y ∈ q.1.1.deco.1.at w.1 := hY z hz w.1 w.2
    have e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht),
      GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · rintro rfl
    exact ⟨y, hy0, key.symm⟩

theorem cosetIn_eq_iff_bar_cq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ},
    (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) →
    ∀ (r r' : PtAt R sel mu cst u j), cosetIn r = cosetIn r' ↔ bar r = bar r' ∧ GlobalTheory.Mem.Col2.ChEx.cqOf r = GlobalTheory.Mem.Col2.ChEx.cqOf r' := by
  intro X Pr R sel S mu cst u j _ hq q q'
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hy0, hY⟩ := ptAt_cosetG q h
    obtain ⟨y', hy', hy0', hY'⟩ := ptAt_cosetG q' h
    have hA : ∀ (p : PtAt R sel mu cst u j) (y : Sp X.E (R.N j)),
        (∀ w ∈ Pr.vGs, ((qOf w : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal p.1.1.deco.1.N) → ∀ w : Pr.vGs,
        ((qOf w.1 : ℕ) : X.E) • (p.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 := by
      intro p y hy w
      have hf := GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 w
      rw [← map_smul]
      exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hy w.1 w.2)
    constructor
    · intro H
      refine ⟨funext fun w => ?_, funext fun P => ?_⟩
      · have := congrFun H ⟨w.1, Finset.mem_union_left _ w.2⟩
        rw [cosetIn_eqG q hy0 hY _ w.2, cosetIn_eqG q' hy0' hY' _ w.2] at this
        rw [bar_eqG q hy hy0 hY, bar_eqG q' hy' hy0' hY', Set.singleton_eq_singleton_iff]
        exact (coset_eq_iff_redV (hq w.1 w.2) (hA q y hy w) (hA q' y' hy' w)).1 this
      · unfold cqOf
        rw [H]
    · rintro ⟨H1, H2⟩
      funext P
      by_cases hP : P.1 ∈ Pr.vGs
      · have := congrFun H1 ⟨P.1, hP⟩
        rw [bar_eqG q hy hy0 hY, bar_eqG q' hy' hy0' hY', Set.singleton_eq_singleton_iff] at this
        rw [cosetIn_eqG q hy0 hY P hP, cosetIn_eqG q' hy0' hY' P hP]
        exact (coset_eq_iff_redV (hq P.1 hP) (hA q y hy ⟨P.1, hP⟩) (hA q' y' hy' ⟨P.1, hP⟩)).2 this
      · have hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp P.2).resolve_left hP
        have := congrFun H2 ⟨P.1, hQ⟩
        exact this
  · have e : ∀ p : PtAt R sel mu cst u j, p.1.2 = ∅ := fun p => by
      have := p.2
      rw [ysAt_ys_of_ne sel mu cst h] at this
      exact this
    have h1 : ∀ p : PtAt R sel mu cst u j, cosetIn p = fun _ => ∅ := fun p => by
      funext P
      ext z
      simp [cosetIn, e p]
    have h2 : ∀ p : PtAt R sel mu cst u j, bar p = fun _ => ∅ := fun p => by
      funext w
      ext v
      simp [bar, e p]
    have h3 : ∀ p : PtAt R sel mu cst u j, cqOf p = fun _ => ∅ := fun p => by
      funext P
      exact congrFun (h1 p) _
    rw [h1 q, h1 q', h2 q, h2 q', h3 q, h3 q']
    simp

end Pt

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColInJetsIn
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Col2

namespace JetEx

theorem hasLetters_of_over {K : Ctx} {P : Pre} (h : K.Over P) : StagesInhab.HasLetters P := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  have hx : 0 < K.s.x := zero_lt_one.trans K.s.one_lt_alt
  refine ⟨(Delv K.s K.cD : ℚ), K.c, Nat.cast_pos.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)), K.ok.inj,
    fun w τ l hl => ?_, K.ok.code⟩
  have h1 := (K.ok.hc w).1 τ
  change l + 1 < K.P.R.k - 1 at hl
  show (K.P.hcW w τ).v ⟨l, by omega⟩ - (K.P.hcW w τ).v ⟨l + 1, hl⟩ = _
  rw [h1, h1, show K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 by omega]
  push_cast
  ring

end JetEx

end GlobalTheory.Mem.Col2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivRowStageUnitaryStandardAdelic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.RowStdGrp

open GlobalTheory.Mem.R3.RowAd GlobalTheory.Mem.R3.RowDeco GlobalTheory.Mem.R3.LiftBrg

theorem ptE_eq_castGL (X : Stages) (h : Bridge.Gf X.toD7.sp.X') :
    ptE X h = castGL (rank_X' X) (Formalism.UG.bc (swapAE X.toD7) h.1) := rfl

def ptHom (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) :
    Bridge.Gf X.toD7.sp.X' →* Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) where
  toFun h := ⟨ptE X h, ptE_mem_UAd X I hI h⟩
  map_one' := Subtype.ext (by
    show ptE X 1 = 1
    exact mul_left_cancel (a := ptE X 1) (by rw [← ptE_mul, mul_one, mul_one]))
  map_mul' a b := Subtype.ext (ptE_mul X a b)

theorem ptHom_val (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) (h : Bridge.Gf X.toD7.sp.X') :
    (ptHom X I hI h).1 = ptE X h := rfl

theorem ptHom_injective (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) :
    Function.Injective (ptHom X I hI) := by
  intro a b hab
  have h1 := congrArg Subtype.val hab
  simp only [ptHom_val, ptE_eq_castGL] at h1
  have h2 := (castGL (rank_X' X)).injective h1
  exact Subtype.ext (StdGroups.bc_injective _ (Algebra.TensorProduct.comm _ _ _).injective h2)

theorem ptHom_surjective (X : Stages) {px : PreX X.B.toPre} (I : Col2.ColIn X.B px) (hI : I.Ok) :
    Function.Surjective (ptHom X I hI) := by
  intro x
  have hy : castGL (rank_X' X).symm x.1 ∈ Formalism.L2.DIV.UA X.toD7.sp.cm X.toD7.sp.X'.gram := by
    rw [gram_X'_eq_one X I hI]
    exact castGL_mem_UA_std _ _ _ x.2
  refine ⟨⟨finHom X.toD7.sp.X' (GlobalTheory.StdFrameExist.liftF X.toD7.sp.X' _ hy), _, rfl⟩, Subtype.ext ?_⟩
  rw [ptHom_val, ptE_eq_castGL]
  have e := GlobalTheory.StdFrameExist.finE_liftF X.toD7.sp.X' _ hy
  change castGL (rank_X' X) (finE X.toD7.sp.X' (GlobalTheory.StdFrameExist.liftF X.toD7.sp.X' _ hy)) = _
  rw [e, StdGroups.castGL_symm_castGL']

theorem ptE_equiv : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∃ e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X',
      ∀ x, RowAd.ptE X (e x) = x.1 := by
  intro X px I hI
  let e0 := MulEquiv.ofBijective (ptHom X I hI) ⟨ptHom_injective X I hI, ptHom_surjective X I hI⟩
  refine ⟨e0.symm, fun x => ?_⟩
  have h := e0.apply_symm_apply x
  exact congrArg Subtype.val h

end GlobalTheory.Mem.R3.RowStdGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupActionLiftFormsRightTranslationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteGroupAction_liftForms_rightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    ∃ a : Bridge.ActTie (Bridge.ratF (Vc X.toD7 i)) P (LiftBrg.envL X I hX U Xg tr L cV i t).lev.Q
        (LiftBrg.envL X I hX U Xg tr L cV i t).lev.ch ((famR X I hX U Xg tr).A.leftGroupActionLift i t),
      ∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG (a.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _)) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.ActQ.exists_actTie | exact GlobalTheory.Mem.R3.LiftBrg.ActQ.exists_actTie | (intros; apply GlobalTheory.Mem.R3.LiftBrg.ActQ.exists_actTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegerLiftModNatIntegralAdeleTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_lift_mod_nat_integralAdeleTensor : ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F), s ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E → ∃ α : 𝓞 D.host.E, ZMod' X.B.I X.B.g (s - Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))) := by
  first | exact @GlobalTheory.Mem.LiftModG.exists_lift_mod_g | exact GlobalTheory.Mem.LiftModG.exists_lift_mod_g | (intros; apply GlobalTheory.Mem.LiftModG.exists_lift_mod_g <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGeneratorsGreenCuspidalLabellingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tame_generators_green_cuspidal_labelling : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : Formalism.L2.Host.CharFrame D), (∀ j g, ∃ z : ℤ, Formalism.L2.Host.eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk), IsEmpty L.nd.Loc ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∃ Gs : GrpSide (setK D L hZ hη), ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Gs.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ ChiTOk (setK D L hZ hη) (cfK L hZ hη cf) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) := by
  first | exact @GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling | exact GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling | (intros; apply GlobalTheory.HeightCounting.TameGrp.exists_tame_generators_cuspidal_labelling <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpDivMulEqStdAddCharMulOfCoprimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_div_mul_eq_stdAddChar_mul_of_coprime : ∀ (p q : ℕ) [NeZero p] [NeZero q], Nat.Coprime p q → ∀ T : ℤ, Complex.exp (2 * Real.pi * Complex.I * (T : ℂ) / ((p * q : ℕ) : ℂ)) = ZMod.stdAddChar (((q : ZMod p))⁻¹ * (T : ZMod p)) * ZMod.stdAddChar (((p : ZMod q))⁻¹ * (T : ZMod q)) := by
  first | exact @GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul | exact GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul | (intros; apply GlobalTheory.exp_two_pi_I_div_mul_eq_stdAddChar_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPointsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_framedLevel_iff_two_adelic_points : ∀ (F E K : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (Λ : LevFam E K n SG) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ))) (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) (U : Subgroup (GL (Fin n) (AfE F E))) (k t y x : GL (Fin n) (AfE F E)) (p p' : DecoF E n ST SG Q), k ∈ UAd hc n → (∀ P : Q, rhoP F P.1 k = 1) → t ∈ K1 hc n ST SG → (∀ x ∈ UAd hc n, x ∈ U ↔ k⁻¹ * x * k ∈ levU hc n ST SG Λ.grp) → IsPtOf hc (y * (k * t)) p → IsPtOf hc (y * x * (k * t)) p' → (x ∈ topU U t Θ d ↔ ∃ (h : Λ.grp) (θ : Θ.grp), ((1, h.1, θ.1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p = p') := by
  exact @GlobalTheory.Mem.Col2.TopCh.mem_topU_iff
end

