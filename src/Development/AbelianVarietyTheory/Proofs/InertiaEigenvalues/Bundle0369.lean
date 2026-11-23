module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPeriodMatrixOfFinrank
section
open TensorProduct Module

noncomputable section

namespace GlobalTheory.RegularRing

theorem exists_periodMatrix_of_finrank (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (B : Type) [CommRing B] [IsDomain B] [Algebra F B] [Algebra E B] [IsScalarTower F E B]
    (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n F)
    (hA : ∀ g, (A g).det ≠ 0) (hE : ∀ g (c : E), act g (algebraMap E B c) = algebraMap E B c)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : E, b' = algebraMap E B c * b)
    (hu : ∀ b : B, b ≠ 0 → (∀ g, ∃ x : F, act g b = algebraMap F B x * b) → IsUnit b)
    (W : Submodule F (n → B))
    (hW : ∀ x, x ∈ W ↔ ∀ g, ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i)) = x)
    (hdim : finrank F ↥W = finrank F E * Fintype.card n) :
    ∃ Q : GL n B, ∀ g, (A g).map (algebraMap F B) * (Q : Matrix n n B).map (act g) = Q := by
  classical
  by_cases hn : IsEmpty n
  · refine ⟨1, fun g => ?_⟩
    ext i
    exact isEmptyElim i
  rw [not_isEmpty_iff] at hn
  let WE : Submodule E (n → B) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        intro c x hx
        rw [SetLike.mem_coe, hW] at hx ⊢
        intro g
        have h1 : (fun i => act g ((c • x) i)) = algebraMap E B c • fun i => act g (x i) := by
          funext i
          simp [Algebra.smul_def, hE]
        rw [h1, Matrix.mulVec_smul, hx g]
        funext i
        simp [Algebra.smul_def] }
  have hWE : ∀ x, x ∈ WE ↔ x ∈ W := fun x => Iff.rfl
  have hfr : finrank E ↥WE = Fintype.card n := by
    have h1 := Module.finrank_mul_finrank F E ↥WE
    have h2 : finrank F ↥WE = finrank F ↥W :=
      ((Submodule.restrictScalarsEquiv F E (n → B) WE).restrictScalars F).finrank_eq.symm.trans
        (by congr 1)
    rw [h2, hdim] at h1
    exact Nat.eq_of_mul_eq_mul_left finrank_pos h1
  haveI : Module.Finite E ↥WE := Module.finite_of_finrank_pos (by rw [hfr]; exact Fintype.card_pos)
  let b : Basis n E ↥WE := (Module.finBasisOfFinrankEq E ↥WE hfr).reindex (Fintype.equivFin n).symm
  let v : n → (n → B) := fun j => (b j : n → B)
  have hv : ∀ g j, ((A g).map (algebraMap F B)).mulVec (fun i => act g (v j i)) = v j :=
    fun g j => (hW _).1 ((hWE _).1 (b j).2) g
  let σ : G → (n → B) →+ (n → B) := fun g =>
    { toFun := fun x => ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i))
      map_zero' := by
        simp only [Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      map_add' := by
        intro x y
        simp only [Pi.add_apply, map_add (f := _)]
        exact Matrix.mulVec_add _ _ _ }
  have hσ : ∀ g (c : B) (w : n → B), σ g (c • w) = act g c • σ g w := by
    intro g c w
    change ((A g).map (algebraMap F B)).mulVec (fun i => act g ((c • w) i)) =
      act g c • ((A g).map (algebraMap F B)).mulVec (fun i => act g (w i))
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp
  have hvE : LinearIndependent E v :=
    b.linearIndependent.map' WE.subtype WE.ker_subtype
  have hvB : LinearIndependent B v := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    exact linearIndepOn_of_invariant (fun g c => act g c) σ hσ hreg v hv s (hvE.linearIndepOn _)
  let Q : Matrix n n B := Matrix.of fun i j => v j i
  have hQ : ∀ g, (A g).map (algebraMap F B) * Q.map (act g) = Q := by
    intro g
    ext i j
    have := congrFun (hv g j) i
    rw [Matrix.mul_apply]
    simpa [Q, Matrix.mulVec, dotProduct] using this
  have hdet0 : Q.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hc
    funext j
    refine Fintype.linearIndependent_iff.1 hvB c ?_ j
    funext i
    have := congrFun hc0 i
    simpa [Q, Matrix.mulVec, dotProduct, mul_comm] using this
  have hdetU : IsUnit Q.det := by
    refine hu _ hdet0 fun g => ?_
    have h2 := congrArg Matrix.det (hQ g)
    rw [Matrix.det_mul] at h2
    have h3 : ((A g).map (algebraMap F B)).det = algebraMap F B (A g).det := (RingHom.map_det _ _).symm
    have h4 : (Q.map (act g)).det = act g Q.det := (RingHom.map_det _ _).symm
    rw [h3, h4] at h2
    refine ⟨(A g).det⁻¹, ?_⟩
    conv_rhs => rw [← h2]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (hA g), map_one, one_mul]
  exact ⟨Matrix.GeneralLinearGroup.mk'' Q hdetU, hQ⟩

end GlobalTheory.RegularRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulDescPochhammerEulerEqEisensteinPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem N_sub_smul_mem_A {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K) :
    N K g - c • g ∈ A O K := fun n => by
  rw [map_sub, coeff_N, coeff_smul, smul_eq_mul, ← sub_mul, norm_mul]
  rw [sub_eq_add_neg]
  refine mul_le_one₀ ?_ (norm_nonneg _) (hg n)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg]
  exact
    max_le (IsUltrametricDist.norm_natCast_le_one K n) hc

theorem exists_N_sub_smul_E_pow_mul (l e : ℕ) {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K)
    (j : ℕ) : ∃ g' ∈ A O K,
      N K (E K l e ^ j * g) - c • (E K l e ^ j * g) = E K l e ^ (j - 1) * g' := by
  cases j with
  | zero => exact ⟨_, N_sub_smul_mem_A hc hg, by simp⟩
  | succ j =>
    refine ⟨((j + 1 : ℕ) : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * g + E K l e * (N K g - c • g),
      (A O K).add_mem ((A O K).mul_mem ((A O K).mul_mem (natCast_mem _ _)
        ((A O K).mul_mem (natCast_mem _ _) ((A O K).pow_mem HasU.X_mem e))) hg)
        ((A O K).mul_mem (E_mem l e _) (N_sub_smul_mem_A hc hg)), ?_⟩
    rw [Derivation.leibniz, Derivation.leibniz_pow, N_E, Nat.add_sub_cancel]
    simp only [smul_eq_mul, nsmul_eq_mul, smul_eq_C_mul]
    push_cast
    ring

theorem exists_aeval_comp_E_pow_mul (l e i : ℕ) : ∀ (m : ℕ) {g : K⟦X⟧}, g ∈ A O K →
    ∃ g' ∈ A O K, Polynomial.aeval (N K).toLinearMap
      ((descPochhammer K i).comp (Polynomial.X - 1)) (E K l e ^ m * g) = E K l e ^ (m - i) * g' := by
  induction i with
  | zero => intro m g hg; exact ⟨g, hg, by simp⟩
  | succ i ih =>
    intro m g hg
    obtain ⟨g₁, hg₁, h₁⟩ := exists_N_sub_smul_E_pow_mul (O := O) l e (c := ((i + 1 : ℕ) : K))
      (IsUltrametricDist.norm_natCast_le_one K _) hg m
    obtain ⟨g₂, hg₂, h₂⟩ := ih (m - 1) hg₁
    refine ⟨g₂, hg₂, ?_⟩
    have h₃ : ∀ x : K⟦X⟧, Polynomial.aeval (N K).toLinearMap
        ((Polynomial.X - (i : Polynomial K)).comp (Polynomial.X - 1)) x = N K x - ((i + 1 : ℕ) : K) • x := by
      intro x
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.natCast_comp, map_sub, map_sub,
        Polynomial.aeval_X, map_natCast, map_one, LinearMap.sub_apply, LinearMap.sub_apply,
        Module.End.natCast_apply, Module.End.one_apply, Derivation.coeFn_coe]
      push_cast
      rw [add_smul, one_smul, Nat.cast_smul_eq_nsmul]
      abel
    rw [descPochhammer_succ_right, Polynomial.mul_comp, map_mul (Polynomial.aeval _), Module.End.mul_apply, h₃, h₁, h₂,
      Nat.sub_sub, add_comm 1 i]

theorem exists_l_pow_mul_descN_eq_E_pow_mul : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K →
    (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i →
    ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  intro l e O K _ _ _ _ _ f h k m hh hf i hi
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  obtain ⟨h', hh', h₁⟩ := exists_aeval_comp_E_pow_mul (O := O) l e i m hh
  refine ⟨h', hh', ?_⟩
  have hl : (l : K⟦X⟧) ^ k = C ((l : K) ^ k) := by simp
  rw [Nat.add_sub_add_right, ← h₁, ← hf, descN, descPochhammer_succ_left, mul_comm (Polynomial.X : Polynomial K), map_mul (Polynomial.aeval _),
    Polynomial.aeval_X, Module.End.mul_apply, hl, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  rfl

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesRingHomOfIsAdicComplete
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.PowerSeriesEval

theorem mk_eval₂_trunc_coe {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) {K : ℕ} (hK : v ^ K ∈ I) (p : Polynomial W) :
    Ideal.Quotient.mk I ((PowerSeries.trunc K (p : W⟦X⟧)).eval₂ ω v) =
      Ideal.Quotient.mk I (p.eval₂ ω v) := by
  have hdvd : (Polynomial.X : Polynomial W) ^ K ∣ p - PowerSeries.trunc K (p : W⟦X⟧) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd, Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  generalize PowerSeries.trunc K (p : W⟦X⟧) = t at hq ⊢
  have hp : p = t + Polynomial.X ^ K * q := by
    rw [← hq]; ring
  rw [Ideal.Quotient.eq, hp, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]
  have : t.eval₂ ω v - (t.eval₂ ω v + v ^ K * q.eval₂ ω v) = -(v ^ K * q.eval₂ ω v) := by ring
  rw [this]
  exact I.neg_mem (I.mul_mem_right _ hK)

noncomputable def truncEval {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) (K : ℕ) (hK : v ^ (K + 1) ∈ I) : W⟦X⟧ →+* C ⧸ I where
  toFun f := Ideal.Quotient.mk I ((PowerSeries.trunc (K + 1) f).eval₂ ω v)
  map_one' := by simp
  map_mul' f g := by
    rw [← PowerSeries.trunc_trunc_mul_trunc, ← Polynomial.coe_mul, mk_eval₂_trunc_coe ω v I hK,
      Polynomial.eval₂_mul, map_mul]
  map_zero' := by simp
  map_add' f g := by simp [Polynomial.eval₂_add]

theorem truncEval_apply {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) (K : ℕ) (hK : v ^ (K + 1) ∈ I) (f : W⟦X⟧) :
    truncEval ω v I K hK f = Ideal.Quotient.mk I ((PowerSeries.trunc (K + 1) f).eval₂ ω v) := rfl

end GlobalTheory.PowerSeriesEval

open GlobalTheory.PowerSeriesEval in
theorem GlobalTheory.PowerSeriesEval.exists_ringHom_powerSeries :
    ∀ (W : Type) [CommRing W] (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C →
      ∀ (ω : W →+* C) (v : C) (e : ℕ), v ^ e ∈ J →
        ∃ σ : W⟦X⟧ →+* C, (∀ w, σ (PowerSeries.C w) = ω w) ∧ σ X = v := by
  intro W _ C _ J hJ ω v e he

  have hN : v ^ (e + 1) ∈ J := by rw [pow_succ]; exact J.mul_mem_right _ he
  have hK : ∀ n : ℕ, v ^ ((e + 1) * n + 1) ∈ J ^ n := fun n => by
    rw [pow_succ, pow_mul]
    exact (J ^ n).mul_mem_right _ (Ideal.pow_mem_pow hN n)
  let f : (n : ℕ) → W⟦X⟧ →+* C ⧸ J ^ n := fun n => truncEval ω v (J ^ n) ((e + 1) * n) (hK n)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (f n) = f m := by
    intro m n hle
    ext g
    simp only [f, RingHom.comp_apply, truncEval_apply, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [← mk_eval₂_trunc_coe ω v (J ^ m) (hK m),
      PowerSeries.trunc_trunc_of_le _ (Nat.succ_le_succ (Nat.mul_le_mul_left _ hle))]
  refine ⟨IsAdicComplete.liftRingHom J f hf, fun w => ?_, ?_⟩
  · have := IsHausdorff.funext' (R := Unit) J (f := fun _ => IsAdicComplete.liftRingHom J f hf (PowerSeries.C w))
      (g := fun _ => ω w) (fun n _ => by
        rw [IsAdicComplete.mk_liftRingHom]
        simp [f, truncEval_apply])
    exact congrFun this ()
  · have := IsHausdorff.funext' (R := Unit) J (f := fun _ => IsAdicComplete.liftRingHom J f hf X)
      (g := fun _ => v) (fun n _ => by
        rw [IsAdicComplete.mk_liftRingHom]
        simp only [f, truncEval_apply]
        rcases n with _ | n
        · rw [Ideal.Quotient.eq, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
        · rw [PowerSeries.trunc_X_of (Nat.succ_le_succ (Nat.mul_pos (Nat.succ_pos e) (Nat.succ_pos n))),
            Polynomial.eval₂_X])
    exact congrFun this ()
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingHomExtendIsAdicCompletionMap
section
namespace GlobalTheory.BSP

theorem exists_ringHom_comp_of_isCompl : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C]
    (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsAdicComplete JC C →
    ∀ g : L →+* C, J.map g ≤ JC → ∃ h : Q →+* C, h.comp i = g := by
  intro L _ Q _ C _ i J JC hi hC g hg
  haveI := hC

  let ψ : (n : ℕ) → L →+* Q ⧸ (J ^ n).map i := fun n => (Ideal.Quotient.mk _).comp i
  have hψ : ∀ n, Function.Surjective (ψ n) := by
    intro n y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hi.surj x n
    exact ⟨a, (Ideal.Quotient.eq.mpr ha).symm⟩
  have hker : ∀ n, RingHom.ker (ψ n) ≤ RingHom.ker ((Ideal.Quotient.mk (JC ^ n)).comp g) := by
    intro n a ha
    have h1 : a ∈ J ^ n := hi.ker a n (Ideal.Quotient.eq_zero_iff_mem.mp ha)
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : g a ∈ (J ^ n).map g := Ideal.mem_map_of_mem g h1
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hg n h2
  let F : (n : ℕ) → Q ⧸ (J ^ n).map i →+* C ⧸ JC ^ n := fun n =>
    (Ideal.Quotient.lift (RingHom.ker (ψ n)) ((Ideal.Quotient.mk (JC ^ n)).comp g) (hker n)).comp
      (RingHom.quotientKerEquivOfSurjective (hψ n)).symm.toRingHom
  have hF : ∀ n a, F n (ψ n a) = Ideal.Quotient.mk (JC ^ n) (g a) := by
    intro n a
    have : (RingHom.quotientKerEquivOfSurjective (hψ n)).symm (ψ n a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [F, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this,
      Ideal.Quotient.lift_mk]
    rfl
  let f : (n : ℕ) → Q →+* C ⧸ JC ^ n := fun n => (F n).comp (Ideal.Quotient.mk _)
  have hfa : ∀ n x a, x - i a ∈ (J ^ n).map i → f n x = Ideal.Quotient.mk (JC ^ n) (g a) := by
    intro n x a h
    have : Ideal.Quotient.mk ((J ^ n).map i) x = ψ n a := Ideal.Quotient.eq.mpr h
    simp only [f, RingHom.comp_apply, this, hF]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow JC hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨a, ha⟩ := hi.surj x n
    have ha' : x - i a ∈ (J ^ m).map i := Ideal.map_mono (Ideal.pow_le_pow_right hle) ha
    rw [RingHom.comp_apply, hfa n x a ha, hfa m x a ha']
    rfl
  refine ⟨IsAdicComplete.liftRingHom JC f hf, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero]
  refine IsHausdorff.haus' (I := JC) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom,
    hfa n (i a) a (by simp)]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableSpanningFinsetMatrices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory

theorem exists_stable_spanning_finset : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (Om l)) (L : FinExt l), Continuous ρ → (∀ g i j, (ρ g).val i j ∈ L.1) → ∃ t : Finset (Matrix (Fin a) (Fin a) (Om l)), (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧ (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧ (∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c y) • y = 1) ∧ ∀ g, ∀ x ∈ t, ∃ c : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], (ρ g).val * x = ∑ y ∈ t, zOm l (c y) • y := by
  intro l _ Γ _ _ _ _ a ρ L hρ hL
  classical
  obtain ⟨t₀, ht₀⟩ := zl_span_image_finite l Γ a ρ hρ
  let e : Matrix (Fin a) (Fin a) L.1 →ₗ[ℚ_[l]] Matrix (Fin a) (Fin a) (Om l) :=
    LinearMap.mapMatrix L.1.val.toLinearMap
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let bM := Module.finBasis ℚ_[l] (Matrix (Fin a) (Fin a) L.1)
  let B : Finset (Matrix (Fin a) (Fin a) (Om l)) := insert 1 (Finset.univ.image (fun k => e (bM k)))
  let t₁ : Finset Γ := insert 1 t₀
  let t : Finset (Matrix (Fin a) (Fin a) (Om l)) := (t₁ ×ˢ B).image (fun p => (ρ p.1).val * p.2)
  have hBL : ∀ b ∈ B, ∀ i j, b i j ∈ L.1 := by
    intro b hb i j
    rcases Finset.mem_insert.mp hb with rfl | hb
    · by_cases h : i = j
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hb
      exact (bM k i j).2
  have hmemt : ∀ h ∈ t₁, ∀ b ∈ B, (ρ h).val * b ∈ t := fun h hh b hb =>
    Finset.mem_image.mpr ⟨(h, b), Finset.mem_product.mpr ⟨hh, hb⟩, rfl⟩
  have hBt : ∀ b ∈ B, b ∈ t := fun b hb => by
    have := hmemt 1 (Finset.mem_insert_self _ _) b hb
    simpa using this
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · intro x hx i j
    obtain ⟨⟨h, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    have hb := (Finset.mem_product.mp hp).2
    simp only [Matrix.mul_apply]
    exact L.1.sum_mem fun k _ => L.1.mul_mem (hL h i k) (hBL b hb k j)
  · intro x hx
    have hxe : x = e (fun i j => ⟨x i j, hx i j⟩) := by ext i j; rfl
    have hsp : (fun i j => (⟨x i j, hx i j⟩ : L.1)) ∈ Submodule.span ℚ_[l] (Set.range bM) := by
      rw [bM.span_eq]; trivial
    have h2 : e (fun i j => ⟨x i j, hx i j⟩) ∈ Submodule.span ℚ_[l] (e '' Set.range bM) := by
      rw [Submodule.span_image]; exact Submodule.mem_map_of_mem hsp
    rw [hxe]
    refine Submodule.span_mono ?_ h2
    rintro y ⟨z, ⟨k, rfl⟩, rfl⟩
    exact hBt _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩))
  · refine ⟨fun y => if y = 1 then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (1 : Matrix (Fin a) (Fin a) (Om l))]
    · simp
    · intro y _ hy; simp [hy]
    · intro h1; exact absurd (hBt 1 (Finset.mem_insert_self _ _)) h1
  · intro g x hx
    obtain ⟨⟨h, b⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    have hb := (Finset.mem_product.mp hp).2
    obtain ⟨f', hf'sup, hf'⟩ := ht₀ (Finsupp.single (g * h) 1)
    have hgh : ((ρ (g * h) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
        f'.sum fun k c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) •
          ((ρ k : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
      rw [← hf', Finsupp.sum_single_index (by simp)]
      simp
    refine ⟨fun y => ∑ k ∈ f'.support with (ρ k).val * b = y, f' k, ?_⟩
    have hmaps : ∀ k ∈ f'.support, (ρ k).val * b ∈ t := fun k hk =>
      hmemt k (Finset.mem_insert_of_mem (hf'sup hk)) b hb
    calc (ρ g).val * ((ρ h).val * b) = (ρ (g * h)).val * b := by rw [map_mul, Units.val_mul, Matrix.mul_assoc]
      _ = ∑ k ∈ f'.support, zOm l (f' k) • ((ρ k).val * b) := by
          rw [hgh, Finsupp.sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.smul_mul]; rfl
      _ = ∑ y ∈ t, ∑ k ∈ f'.support with (ρ k).val * b = y, zOm l (f' k) • ((ρ k).val * b) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ = ∑ y ∈ t, zOm l (∑ k ∈ f'.support with (ρ k).val * b = y, f' k) • y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.sum_smul]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [(Finset.mem_filter.mp hk).2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltZerosUntiltFrobeniusDoubleSeries
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSerExist

theorem norm_l_lt_one (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ < 1 := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  have h2 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have h3 : ((l : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by push_cast; rfl
  rw [h3] at h
  rw [h]; exact h2

theorem exists_zeros (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (hh : 2 ≤ h) (hμ : μ ≠ 0) :
    ∃ y : Fin h → ℕ → Fl l, (∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖) ∧
      (∀ a, ∑ i : Fin h, μ i * abelian₂ h i (y a) = 0) ∧
      ∀ c : Fin h → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) →
        c = 0 := by
  have h1 : 1 ≤ h := le_trans (by norm_num) hh
  obtain ⟨τ, hsurj, x, hxS, hxη, hxind⟩ := _root_.GlobalTheory.oneVarCount_onto_independentZeros l h μ h1 hμ
  let η : Fl l → Unit → ℂ_[l] := fun y _ => ∑ i : Fin h, μ i * lam h i y
  let S : Set (Fl l) := {y | ‖sh y‖ ≤ ‖(l : ℂ_[l])‖}
  have hlift := _root_.GlobalTheory.lift_hasSum_zero l (Fl l) Unit η (fun _ => τ) S
    (fun t ht => by
      obtain ⟨y, hy, hyt⟩ := hsurj (t ()) (ht ())
      exact ⟨y, hy, fun i => by cases i; exact hyt⟩)
  have hy : ∀ a : Fin h, ∃ z : ℕ → Fl l, z 0 = x a ∧ (∀ k, z k ∈ S) ∧
      ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (z k) i) 0 :=
    fun a => hlift (x a) (hxS a) (fun _ => hxη a)
  choose y hy0 hyS hysum using hy
  have hr : ‖(l : ℂ_[l])‖ < 1 := norm_l_lt_one l
  have hyS' : ∀ a k, ‖sh (y a k)‖ ≤ ‖(l : ℂ_[l])‖ := fun a k => hyS a k
  refine ⟨y, hyS', ?_, ?_⟩
  · intro a
    have hs : ∀ i : Fin h, HasSum (fun k : ℕ => μ i * ((l : ℂ_[l]) ^ k * lam h i (y a k)))
        (μ i * abelian₂ h i (y a)) := fun i =>
      ((_root_.GlobalTheory.PSer.Lam_main l h i ‖(l : ℂ_[l])‖ (y a) h1 hr (hyS' a)).1).mul_left (μ i)
    have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hs i)
    have hsum' : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y a k) ())
        (∑ i : Fin h, μ i * abelian₂ h i (y a)) := by
      convert hsum using 1
      funext k
      dsimp [η]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    exact hsum'.unique (hysum a ())
  · refine _root_.GlobalTheory.PSer.Lam_indep_of_first_terms l h h ‖(l : ℂ_[l])‖ y hh (norm_nonneg _) hr hyS' ?_
    intro n hn a
    simp only [hy0] at hn
    exact hxind n hn a

end GlobalTheory.PSerExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCoeffOfNotXPowDvdLineStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_coeff_of_not_X_pow_dvd_line : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [Algebra (X.O0 i) K], IsRes i K → ∀ (b : ι → K) (n : ℕ), n ≤ X.l i ^ M → ∀ F G : MvPolynomial ι (X.O0 i), toLam X i M ι F = toLam X i M ι G → ¬ (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) G → ∃ m : ι →₀ ℕ, m.degree < n ∧ IsUnit (F.coeff m) := by
  first | exact @GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line | exact GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line | (intros; apply GlobalTheory.ResSel.exists_unit_coeff_of_not_dvd_line <;> assumption)
end

