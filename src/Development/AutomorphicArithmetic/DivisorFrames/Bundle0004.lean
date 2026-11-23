module

public import Mathlib
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsIrreducibleSubrepHeckeEigenOfInvariantForm
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsAdmissibleEquivariantFormsRep
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

private theorem orbit_finite {H V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ H V) (K : Subgroup H) (hK : IsCompact (K : Set H)) (w : V)
    (hw : IsOpen {k : H | ρ k w = w}) : (Set.range fun k : K => ρ k w).Finite := by
  have h1 : IsLocallyConstant fun k : H => ρ k w := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' {k : H | ρ k w = w}, hw.preimage (by fun_prop), by simp, fun y hy => ?_⟩
    have h2 : ρ (x⁻¹ * y) w = w := hy
    conv_rhs => rw [← h2]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  exact (h1.comp_continuous (continuous_subtype_val (p := fun x => x ∈ K))).range_finite

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S] [Module ℂ S]

private def eqForms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add (f := _)]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

private noncomputable def eqRep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU (E := E) (n := n)) (eqForms ρ) where
  toFun k := (LinearMap.llcomp ℂ _ _ _ (RU E n k)).restrict (p := eqForms ρ) (q := eqForms ρ) fun f h =>
    ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
      change RU E n k (f (ρ x v)) = RU E n x (RU E n k (f v))
      rw [h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩
  map_one' := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g => congrArg (f.1 v) (mul_one g))
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g =>
    congrArg (f.1 v) (mul_assoc g a b).symm)

private theorem eqRep_apply (ρ : Representation ℂ (infU E n) S) (k : finU (E := E) (n := n)) (f : eqForms ρ) (v : S) :
    (eqRep ρ k f).1 v = RU E n k (f.1 v) := rfl

private theorem eqRep_open [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (f : eqForms ρ) :
    IsOpen {k : finU (E := E) (n := n) | eqRep ρ k f = f} := by
  let b := Module.finBasis ℂ S
  convert isOpen_iInter_of_finite fun i => (f.2.1 (b i)).level using 1
  ext k
  rw [Set.mem_iInter]
  exact ⟨fun h i => LinearMap.congr_fun (congrArg Subtype.val h) (b i), fun h => Subtype.ext (b.ext h)⟩

private theorem eqRep_adm [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (f : eqForms ρ) :
    ∃ K : Subgroup (finU (E := E) (n := n)), (∀ k ∈ K, eqRep ρ k f = f) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed (eqRep ρ) K) ∧
      ∀ w, (Set.range fun k : K => eqRep ρ k w).Finite := by
  obtain ⟨K0, hK0o, hK0c⟩ := UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E n
  let St : Subgroup (finU (E := E) (n := n)) :=
    { carrier := {k | eqRep ρ k f = f}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        have ha' : eqRep ρ a f = f := ha
        have hb' : eqRep ρ b f = f := hb
        change eqRep ρ (a * b) f = f
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := fun {a} ha => by
        have ha' : eqRep ρ a f = f := ha
        change eqRep ρ a⁻¹ f = f
        conv_lhs => rw [← ha']
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have ho : IsOpen ((K0 ⊓ St : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n))) := hK0o.inter (eqRep_open ρ f)
  have hc : IsCompact ((K0 ⊓ St : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n))) :=
    hK0c.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun x hx => hx.1
  refine ⟨K0 ⊓ St, fun k hk => hk.2, ?_, fun w => orbit_finite _ _ hc w (eqRep_open ρ w)⟩
  have := UpperTheory.finiteDimensional_automorphicForms_unitary_of_type_level E n S (fun x => ρ x) (K0 ⊓ St) ho
    ((GlobalTheory.PRep.fixed (eqRep ρ) (K0 ⊓ St)).map (eqForms ρ).subtype) (by
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨fun v γ hγ x => (g.2.1 v).left γ hγ x, g.2.2, fun k hk v => ?_⟩
      have h1 : eqRep ρ k g = g := by simpa using hg ⟨k, hk⟩
      exact LinearMap.congr_fun (congrArg Subtype.val h1) v)
  exact (Submodule.equivMapOfInjective _ (eqForms ρ).injective_subtype _).symm.finiteDimensional

end

theorem UpperTheory.exists_admissible_equivariantFormsRep :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S),
        Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → φ ≠ 0 → 0 < (B φ φ).re) →
        (∀ k ∈ finU (E := E) (n := n), ∀ φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n k φ) (RU E n k ψ) = B φ ψ) →
        ∀ f : S →ₗ[ℂ] (UA E n → ℂ), f ≠ 0 → (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) →
        ∃ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π ∧ ∃ f' : S →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ v, f' v ∈ π) ∧
          (∀ (x : infU E n) v, f' (ρ x v) = RU E n x (f' v)) ∧
          ∀ (κ : Type) (s : Finset κ) (y : κ → UA E n) (c : ℂ), (∀ i ∈ s, y i ∈ finU (E := E) (n := n)) →
            (∀ v, ∑ i ∈ s, RU E n (y i) (f v) = c • f v) → ∀ v, ∑ i ∈ s, RU E n (y i) (f' v) = c • f' v := by
  intro E _ _ _ n S _ _ _ ρ hsp B hpos hinv f hf0 hfa hfe
  classical
  let b := Module.finBasis ℂ S
  let ev : S → (eqForms ρ →ₗ[ℂ] (UA E n → ℂ)) := fun v => LinearMap.applyₗ v ∘ₗ (eqForms ρ).subtype
  let B' : eqForms ρ →ₗ⋆[ℂ] eqForms ρ →ₗ[ℂ] ℂ := ∑ i, (B.compl₂ (ev (b i))).comp (ev (b i))
  have hB' : ∀ u v, B' u v = ∑ i, B (u.1 (b i)) (v.1 (b i)) := fun u v => by
    simp only [B', LinearMap.sum_apply]
    rfl
  have hdef : ∀ v, B' v v = 0 → v = 0 := fun v hv => by
    have hnn : ∀ i, 0 ≤ (B (v.1 (b i)) (v.1 (b i))).re := fun i => by
      by_cases h : v.1 (b i) = 0
      · simp [h]
      · exact (hpos _ (v.2.1 _) h).le
    have h1 : ∑ i, (B (v.1 (b i)) (v.1 (b i))).re = 0 := by
      rw [← Complex.re_sum, ← hB', hv, Complex.zero_re]
    refine Subtype.ext (b.ext fun i => ?_)
    by_contra h
    exact (hpos _ (v.2.1 _) h).ne' ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h1 i (Finset.mem_univ i))
  have hinv' : ∀ g u v, B' (eqRep ρ g u) (eqRep ρ g v) = B' u v := fun g u v => by
    rw [hB', hB']
    exact Finset.sum_congr rfl fun i _ => hinv g g.2 _ _ (u.2.1 _) (v.2.1 _)
  obtain ⟨U, hU, hirr, f', hf'U, hf'0, hsum⟩ := UpperTheory.exists_irreducible_subrep_hecke_eigen_of_invariant_form (finU (E := E) (n := n)) (eqForms ρ) (eqRep ρ) B' hdef hinv'
    (eqRep_adm ρ) ⟨f, hfa, hfe⟩ (fun h => hf0 (congrArg Subtype.val h))
  let j : U →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := (eqForms ρ).subtype ∘ₗ U.subtype
  have hj : ∀ (p : U) (x : infU E n) v, j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => p.1.2.2 x v
  have hf1 : f'.1 ≠ 0 := fun h => hf'0 (Subtype.ext h)
  have hmem : ∀ v, f'.1 v ∈ Pairs.img j := fun v => Pairs.apply_mem_img j ⟨f', hf'U⟩ v
  refine ⟨Pairs.img j, ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun h => hf1 (LinearMap.ext fun v => ?_),
    fun N hle hN => ?_⟩, f'.1, hf1, hmem, f'.2.2, fun κ s y c hy h v => ?_⟩
  · have h1 : Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      exact p.1.2.1 v)
    exact h1 hφ
  · refine Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
    · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        change RU E n a.1 _ ∈ Pairs.img j
        rw [← hj]
        exact Pairs.apply_mem_img _ _ _)
      exact fun φ hφ => h1 hφ
    · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact Pairs.apply_mem_img j ⟨eqRep ρ k p.1, hU k _ p.2⟩ v)
      exact fun φ hφ => h1 hφ
  · have := hmem v
    rw [h, Submodule.mem_bot] at this
    exact this
  · refine Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
      (Q := fun k : finU (E := E) (n := n) => (eqRep ρ k).restrict (hU k)) (T := fun k => RU E n k.1) (fun _ _ _ => rfl)
      (fun P hP => ?_) hle (fun x => hN x.1) (fun k => hN k.1)
    rcases hirr (P.map U.subtype) (Submodule.map_subtype_le U P) (by
      rintro g _ ⟨p, hp, rfl⟩
      exact ⟨_, hP g p hp, rfl⟩) with h | h
    · left
      exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_bot _).symm)
    · right
      exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_subtype_top _).symm)
  · let y' : κ → finU (E := E) (n := n) := fun i => if h : y i ∈ finU (E := E) (n := n) then ⟨y i, h⟩ else 1
    have hy' : ∀ (g : eqForms ρ) v, (∑ i ∈ s, eqRep ρ (y' i) g).1 v = ∑ i ∈ s, RU E n (y i) (g.1 v) := fun g v => by
      rw [Submodule.coe_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [eqRep_apply]
      simp only [y', dif_pos (hy i hi)]
    have h2 := hsum κ s y' c (Subtype.ext (LinearMap.ext fun v => (hy' _ v).trans (h v)))
    exact (hy' f' v).symm.trans (LinearMap.congr_fun (congrArg Subtype.val h2) v)
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.GelfandElementMemAdjoinCapelliCoeffs
section
open Matrix Formalism.REAL

private theorem epow_eq_matrix_pow {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (m : ℕ) (a b : Fin n) :
    epow E m a b = (Matrix.of E ^ m) a b := by
  induction m generalizing a b with
  | zero =>
    rw [epow.eq_1, pow_zero, Matrix.one_apply]
  | succ k ih =>
    rw [epow.eq_2, pow_succ, Matrix.mul_apply]
    simp only [ih, Matrix.of_apply]

private theorem exists_coeff_vanishing_mul_left {A : Type} [Ring A] [Algebra ℂ A] (K p : ℕ) (a : A) {f : ℂ → A}
    (hf : ∃ v : ℕ → A, v p = 0 ∧ ∀ u, f u = ∑ l ∈ Finset.range K, u ^ l • v l) :
    ∃ v : ℕ → A, v p = 0 ∧ ∀ u, a * f u = ∑ l ∈ Finset.range K, u ^ l • v l := by
  obtain ⟨v, hv0, hv⟩ := hf
  refine ⟨fun l => a * v l, by simp [hv0], fun u => ?_⟩
  rw [hv u, Finset.mul_sum]
  simp only [mul_smul_comm]

private theorem exists_coeff_vanishing_mul_right {A : Type} [Ring A] [Algebra ℂ A] (K p : ℕ) (a : A) {f : ℂ → A}
    (hf : ∃ v : ℕ → A, v p = 0 ∧ ∀ u, f u = ∑ l ∈ Finset.range K, u ^ l • v l) :
    ∃ v : ℕ → A, v p = 0 ∧ ∀ u, f u * a = ∑ l ∈ Finset.range K, u ^ l • v l := by
  obtain ⟨v, hv0, hv⟩ := hf
  refine ⟨fun l => v l * a, by simp [hv0], fun u => ?_⟩
  rw [hv u, Finset.sum_mul]
  simp only [smul_mul_assoc]

private theorem exists_coeff_vanishing_sum {A : Type} [Ring A] [Algebra ℂ A] (K p : ℕ) {ι : Type} [Fintype ι]
    {f : ι → ℂ → A}
    (hf : ∀ i, ∃ v : ℕ → A, v p = 0 ∧ ∀ u, f i u = ∑ l ∈ Finset.range K, u ^ l • v l) :
    ∃ v : ℕ → A, v p = 0 ∧ ∀ u, ∑ i, f i u = ∑ l ∈ Finset.range K, u ^ l • v l := by
  choose v hv0 hv using hf
  refine ⟨fun l => ∑ i, v i l, by simp [hv0], fun u => ?_⟩
  simp only [hv, Finset.smul_sum]
  exact Finset.sum_comm

private theorem etr_mem_adjoin_range_qdet (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A)
    (hE : GlRel E) (N : ℕ) : etr E N ∈ Algebra.adjoin ℂ (Set.range (qdet E)) := by
  set S := Algebra.adjoin ℂ (Set.range (qdet E)) with hS
  have hq : ∀ u, qdet E u ∈ S := fun u => Algebra.subset_adjoin ⟨u, rfl⟩
  obtain ⟨c, hc1, hc⟩ := _root_.GlobalTheory.qdet_polyMap_monic A (m + 1) E
  have hp : ∀ i j : Fin (m + 1), ∃ v : ℕ → A, v (m + 1) = 0 ∧
      ∀ u : ℂ, qminor E j.succAbove i.succAbove u = ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • v l := by
    intro i j
    obtain ⟨d, hd⟩ := GlobalTheory.qminor_polyMap A (m + 1) m E j.succAbove i.succAbove 0
    refine ⟨fun l => if l < m + 1 then d l else 0, by simp, fun u => ?_⟩
    rw [Finset.sum_range_succ]
    simp only [lt_irrefl, ↓reduceIte, smul_zero, add_zero]
    have e := hd u
    rw [sub_zero] at e
    rw [e]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [if_pos (Finset.mem_range.mp hl)]
  refine Nat.strong_induction_on N ?_
  intro N ih
  have hgS : ∀ u : ℂ, algebraMap ℂ A ((-1) ^ N) *
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
        qminor E j.succAbove i.succAbove u * epow E (N + 1) j i
      - qdet E u * (algebraMap ℂ A ((-1) ^ N) * etr E N) ∈ S := by
    intro u
    have key := _root_.GlobalTheory.TracedComatrix.traced_comatrix A m E hE u N
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_add] at key
    rw [eq_sub_of_add_eq' key, sub_right_comm, add_sub_cancel_right]
    refine S.sub_mem (S.mul_mem (hq u) (S.sum_mem fun k hk => S.mul_mem (S.algebraMap_mem _)
      (ih k (Finset.mem_range.mp hk)))) (S.mul_mem (S.algebraMap_mem _) ?_)
    rw [← _root_.GlobalTheory.qdet_add_one_sub_eq_sum_qminor A m E u]
    exact S.sub_mem (hq _) (hq _)
  have h1 : ∀ i j : Fin (m + 1), ∃ v : ℕ → A, v (m + 1) = 0 ∧ ∀ u : ℂ,
      (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E j.succAbove i.succAbove u * epow E (N + 1) j i
        = ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • v l :=
    fun i j => exists_coeff_vanishing_mul_right _ _ _ (exists_coeff_vanishing_mul_left _ _ _ (hp i j))
  obtain ⟨v, hv0, hv⟩ := exists_coeff_vanishing_mul_left _ _ (algebraMap ℂ A ((-1) ^ N))
    (exists_coeff_vanishing_sum _ _ fun i => exists_coeff_vanishing_sum _ _ (h1 i))
  have hall : ∀ u : ℂ, ∑ l ∈ Finset.range (m + 1 + 1),
      u ^ l • (v l - c l * (algebraMap ℂ A ((-1) ^ N) * etr E N)) ∈ Subalgebra.toSubmodule S := by
    intro u
    have e : ∑ l ∈ Finset.range (m + 1 + 1), u ^ l • (v l - c l * (algebraMap ℂ A ((-1) ^ N) * etr E N))
        = algebraMap ℂ A ((-1) ^ N) *
          ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
            qminor E j.succAbove i.succAbove u * epow E (N + 1) j i
          - qdet E u * (algebraMap ℂ A ((-1) ^ N) * etr E N) := by
      rw [hv u, hc u, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_sub, smul_mul_assoc]
    rw [e]
    exact hgS u
  have hm := _root_.GlobalTheory.coeff_mem_of_poly_values_mem A (Subalgebra.toSubmodule S) (m + 1 + 1) _ hall (m + 1) (by omega)
  simp only [hv0, hc1, zero_sub, one_mul] at hm
  have hm' : algebraMap ℂ A ((-1) ^ N) * etr E N ∈ S := by
    have h := (Subalgebra.toSubmodule S).neg_mem hm
    rw [neg_neg] at h
    exact (Subalgebra.mem_toSubmodule S).1 h
  have h := S.mul_mem (S.algebraMap_mem ((-1 : ℂ) ^ N)) hm'
  rwa [← mul_assoc, ← map_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, map_one, one_mul] at h

/-- Gelfand elements lie in the algebra generated by the Capelli determinant values. -/
theorem UpperTheory.gelfandElement_mem_adjoin_capelliCoeffs :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), GlRel X → ∀ k : ℕ, GlobalTheory.SmoothForms.gelfA X k ∈ Algebra.adjoin ℂ (Set.range (qdet X)) := by
  intro A _ _ n X hX k
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]
  have h : (∑ c, (Matrix.of X ^ (k + 1)) c c) = etr X (k + 1) := by
    simp only [etr, epow_eq_matrix_pow]
  rw [h]
  cases n with
  | zero =>
    have h0 : etr X (k + 1) = 0 := by simp [etr]
    rw [h0]
    exact Subalgebra.zero_mem _
  | succ m => exact etr_mem_adjoin_range_qdet A m X hX (k + 1)
end

