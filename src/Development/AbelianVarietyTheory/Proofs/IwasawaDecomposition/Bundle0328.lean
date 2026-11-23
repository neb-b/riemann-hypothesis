module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Formalism.LocalToGlobal.Columns.ChainTwOk
public import Formalism.LocalToGlobal.Columns.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0319
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjReferenceChartIndex
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

theorem pi_conj {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ Λ' : LevFam X.E X.K n SG) (x : ∀ w : SG, GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))
    (hH : ∀ w hbar, hbar ∈ (Λ w).H ↔ x w * hbar * (x w)⁻¹ ∈ (Λ' w).H)
    (hL : ∀ w (hbar : ↥(Λ w).H) (hbar' : ↥(Λ' w).H), hbar'.1 = x w * hbar.1 * (x w)⁻¹ →
      (Λ w).lam hbar = (Λ' w).lam hbar') :
    (∀ g : GLG (E := X.E) (n := n) (SG := SG), g ∈ Λ.grp ↔ (fun w => x w * g w * (x w)⁻¹) ∈ Λ'.grp) ∧
    ∀ (g : ↥Λ.grp) (g0 : ↥Λ'.grp), (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) → Λ.chr g = Λ'.chr g0 := by
  refine ⟨fun g => ?_, fun g g0 hg => ?_⟩
  · simp only [LevFam.grp, Subgroup.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun w => hH w (g w)
  · rw [LevFam.chr_apply, LevFam.chr_apply]
    exact Finset.prod_congr rfl fun w _ => hL w _ _ (hg w)

section Gen

variable {Xf : Fields} {Pr : Primes Xf} {R : Ranks} {Ch : Chars Xf Pr R.m}
  {sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)} {S : Set ℕ} {mu : Tup Xf.F Xf.E Xf.K S}
  {cst : LocCst Xf (rowSG Pr sel mu)} {L : ChIdx Xf Pr R (QE sel (mu : Chr Xf.F Xf.E Xf.K))} {G : ChGlob Xf R.m} {m2 : ℕ}

theorem cosetOne (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
      SameDC (Pr := Pr) true j P.1 1 (L.h j b P) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _ b P _
    rw [hok.zero_h]
    exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  | succ i ih =>
    intro hj b P hP
    by_cases hi : i < m2
    · obtain ⟨al, hal⟩ := hok.nonvan i hi b P
      have h1 := ih (by omega) al P hP
      have hs1 := hok.stabG i al P hP
      have hs2 := hok.stabG (i + 1) b P hP
      have h2 := (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P hP _ _ hs1 hs2 (by rw [hs]; exact h1)).1 hal
      have h3 := twSurjG G.σ₀ hB hi P hP _ hs2 h2
      rwa [hs] at h3
    · obtain rfl : i = m2 := by omega
      rw [hok.last_h]
      exact ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem idx_nonempty (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) :
    ∀ j, j ≤ m2 + 1 → Nonempty (L.β j) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨b, -⟩ := hok.zero_uniq
    exact ⟨b⟩
  | succ i ih =>
    intro hj
    by_cases hi : i < m2
    · obtain ⟨al⟩ := ih (by omega)
      obtain ⟨b, -⟩ := hok.surj i hi (fun _ => 1) (fun _ _ => one_mem _) (fun P hP => absurd (hQ P) hP)
        (fun P => ⟨al, (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P (hQ P) _ _ (hok.stabG i al P (hQ P))
          (one_mem _) (by rw [hs]; exact cosetOne hX hPr hCh hsel hs hok i (by omega) al P (hQ P))).2
          (twNonVanG G.σ₀ hB hi P (hQ P))⟩)
      exact ⟨b⟩
    · obtain rfl : i = m2 := by omega
      obtain ⟨b, -⟩ := hok.last_uniq
      exact ⟨b⟩

end Gen

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch


open Classical in
theorem idx_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ b : Idx I.sel (I.tup a) (I.idx a) i, ∃ (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i)
      (x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal)),
      (i + 1 = B.R.m → ∀ w, x w = 1) ∧
      (∀ g : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp ↔
        (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp) ∧
      ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp),
        (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
        (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).chr g0 := by
  intro B X I h l a i hi1 hi b
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hoka := h.idx_ok a
  have hok0 := h.idx_ok I.mu0
  generalize B.R.m - 2 = m2 at hoka hok0
  have hm := hoka.hm
  have hQ0 : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P =>
    (Finset.mem_union.1 P.2).resolve_right (by
      have e : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
      rw [e]
      exact Finset.notMem_empty _)
  rcases b with ⟨_ | β, hb⟩
  · exact absurd (hb.2 hi) (by simp)
  have key : ∃ β0 : (I.idx I.mu0).β i, ∀ w : (B.primes X).vGs, ∃ (r κ : AutY B.fields B.R i),
      r ∈ Loc.R1 B.fields.E (B.R.N i) (cOf B.R i) ∧ κ ∈ Jat (Pr := B.primes X) true i w.1 ∧
      (I.idx a).h i β ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * (I.idx I.mu0).h i β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ ∧
      (i + 1 = B.R.m → r = 1) := by
    by_cases hlast : i = m2 + 1
    · subst hlast
      obtain ⟨β0, -⟩ := hok0.last_uniq
      refine ⟨β0, fun w => ⟨1, 1, one_mem _, one_mem _, ?_, fun _ => rfl⟩⟩
      rw [hoka.last_h, hok0.last_h]
      simp
    · obtain ⟨β0⟩ := idx_nonempty hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 hQ0 i (by omega)
      refine ⟨β0, fun w => ?_⟩
      obtain ⟨r1, hr1, κ1, hκ1, e1⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp a) hoka i (by omega) β ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      obtain ⟨r0, hr0, κ0, hκ0, e0⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 i (by omega) β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      refine ⟨r1 * r0⁻¹, κ0⁻¹ * κ1, mul_mem hr1 (inv_mem hr0), mul_mem (inv_mem hκ0) hκ1, ?_, fun e => absurd e (by omega)⟩
      rw [e1, e0]
      group
  obtain ⟨β0, hw⟩ := key
  choose r κ hr hκ he hr1 using hw
  have gc := fun w => GlobalTheory.T.doubleCoset_reps_conjugate_level_groups I.Ch I.sel (I.tup a) (I.tup I.mu0) (I.cst a) (I.cst I.mu0) (I.idx a) (I.idx I.mu0) I.glob m2
    hX l.pr h.ch_ok (h.sharp a) (h.sharp I.mu0) hoka hok0 i (by omega) β β0 w (r w) (κ w) (hr w) (hκ w) (he w)
  choose x hx1 hxH hxL using gc
  refine ⟨⟨some β0, by simp [hi]⟩, x, fun e w => hx1 w (hr1 w e), ?_⟩
  exact pi_conj ((I.idx a).levG i β) ((I.idx I.mu0).levG i β0) x hxH hxL

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinExtConjIntOf
section
open Formalism.BasicNotions

noncomputable section

namespace GlobalTheory.IntegralConjFinExt

open Matrix

theorem norm_sum_le_one (l : ℕ) [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → PadicAlgCl l)
    (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (PadicAlgCl.isNonarchimedean l _ _).trans
      (max_le (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem norm_one_apply_le (l : ℕ) [Fact l.Prime] (a : ℕ) (i j : Fin a) :
    ‖(1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

def intSubgroup (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] {a : ℕ}
    (ρ : Γ →* GL (Fin a) (PadicAlgCl l)) : Subgroup Γ where
  carrier := {g | ∀ i j, ‖(ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1 ∧
    ‖(ρ g⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ ≤ 1}
  one_mem' := fun i j => by
    simp only [inv_one, map_one, Units.val_one]
    exact ⟨norm_one_apply_le l a i j, norm_one_apply_le l a i j⟩
  mul_mem' := fun {g h} hg hh i j => by
    rw [_root_.mul_inv_rev, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply,
      Matrix.mul_apply]
    exact ⟨norm_sum_le_one l _ _ fun k _ => by
        rw [norm_mul]; exact mul_le_one₀ (hg i k).1 (norm_nonneg _) (hh k j).1,
      norm_sum_le_one l _ _ fun k _ => by
        rw [norm_mul]; exact mul_le_one₀ (hh i k).2 (norm_nonneg _) (hg k j).2⟩
  inv_mem' := fun {g} hg i j => ⟨(hg i j).2, by rw [inv_inv]; exact (hg i j).1⟩

theorem isOpen_intSubgroup (l : ℕ) [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) (PadicAlgCl l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)))) :
    IsOpen (intSubgroup l ρ : Set Γ) := by
  let V : Set Γ := ⋂ i, ⋂ j,
    ({g | ‖(ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1} ∩
     {g | ‖(ρ g⁻¹ : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j - (1 : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j‖ < 1})
  have hVo : IsOpen V :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_lt (((hρ.matrix_elem i j).sub continuous_const).norm) continuous_const).inter
        (isOpen_lt ((((hρ.matrix_elem i j).comp continuous_inv).sub continuous_const).norm) continuous_const)
  have hV1 : (1 : Γ) ∈ V := by
    simp only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, inv_one, map_one, Units.val_one,
      sub_self, norm_zero, zero_lt_one, and_self, implies_true]
  have hle : ∀ x y : PadicAlgCl l, ‖x - y‖ < 1 → ‖y‖ ≤ 1 → ‖x‖ ≤ 1 := fun x y hxy hy => by
    have := PadicAlgCl.isNonarchimedean l (x - y) y
    rw [sub_add_cancel] at this
    exact this.trans (max_le hxy.le hy)
  have hVU : V ⊆ (intSubgroup l ρ : Set Γ) := fun g hg i j => by
    simp only [V, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq] at hg
    exact ⟨hle _ _ (hg i j).1 (norm_one_apply_le l a i j), hle _ _ (hg i j).2 (norm_one_apply_le l a i j)⟩
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hVo.mem_nhds hV1) hVU)


set_option maxHeartbeats 1600000 in
theorem exists_finExt_conj_intOf : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) → ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k, ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := by
  intro l _ Γ _ _ _ _ _ a ρ hρ
  letI : DecidableEq Γ := Classical.decEq Γ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l Γ a ρ hρ ⟨⊥, inferInstance⟩
  haveI : FiniteDimensional ℚ_[l] L.1 := L.2
  let U := intSubgroup l ρ
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen _ (isOpen_intSubgroup l ρ hρ)
  haveI : Fintype (Γ ⧸ U) := Fintype.ofFinite _
  let T : Finset Γ := Finset.univ.image (fun q : Γ ⧸ U => q.out)
  have hTU : ∀ x : Γ, ∃ t ∈ T, t⁻¹ * x ∈ U := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U x
    refine ⟨(x : Γ ⧸ U).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [hh, _root_.mul_inv_rev, inv_mul_cancel_right]
    exact U.inv_mem h.2
  obtain ⟨r, hr⟩ := GlobalTheory.StableLattice.lift_of_integral (O := L.1) (K := PadicAlgCl l)
    Subtype.val_injective ρ (fun g i j => ⟨⟨_, hL g i j⟩, rfl⟩)
  have hre : ∀ g i j, (((r g : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j : PadicAlgCl l) =
      ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j := by
    intro g i j
    rw [← hr g, Matrix.GeneralLinearGroup.map_apply]
    rfl
  let e : L.1 ≃ₐ[Loc.OL L] FractionRing (Loc.OL L) :=
    IsLocalization.algEquiv (nonZeroDivisors (Loc.OL L)) L.1 (FractionRing (Loc.OL L))
  let σ : Γ →* GL (Fin a) (FractionRing (Loc.OL L)) :=
    (Matrix.GeneralLinearGroup.map e.toRingEquiv.toRingHom).comp r
  have hσ : ∀ x : Γ, ∃ t ∈ T, ∀ i j, (σ (t⁻¹ * x)).val i j ∈
        (algebraMap (Loc.OL L) (FractionRing (Loc.OL L))).range := by
    intro x
    obtain ⟨t, ht, hu⟩ := hTU x
    refine ⟨t, ht, fun i j => ?_⟩
    have hmem : ((r (t⁻¹ * x) : GL (Fin a) L.1) : Matrix (Fin a) (Fin a) L.1) i j ∈ Loc.OL L := by
      rw [Formalism.BasicNotions.Examples₂.LB.mem_OL, hre]
      exact (hu i j).1
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [σ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply]
    rw [← e.commutes]
    rfl
  obtain ⟨P', hP'⟩ := GlobalTheory.StableLattice.exists_conj_integral σ T hσ
  let φ : FractionRing (Loc.OL L) →+* PadicAlgCl l :=
    (algebraMap L.1 (PadicAlgCl l)).comp e.symm.toRingEquiv.toRingHom
  have hφσ : ∀ g, Matrix.GeneralLinearGroup.map φ (σ g) = ρ g := by
    intro g
    rw [← hr g]
    ext i j
    simp only [σ, φ, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, RingHom.comp_apply]
    congr 1
    exact e.symm_apply_apply _
  refine ⟨L, Matrix.GeneralLinearGroup.map φ P', fun g i k => ?_⟩
  have h1 : (Matrix.GeneralLinearGroup.map φ P')⁻¹ * ρ g * Matrix.GeneralLinearGroup.map φ P' =
      Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P') := by
    rw [MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ), MonoidHom.map_mul (Matrix.GeneralLinearGroup.map φ),
      MonoidHom.map_inv (Matrix.GeneralLinearGroup.map φ), hφσ]
  suffices key : ((Matrix.GeneralLinearGroup.map φ (P'⁻¹ * σ g * P') : GL (Fin a) (PadicAlgCl l)) :
      Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 by
    rw [← h1] at key
    exact key
  obtain ⟨z, hz⟩ := hP' g i k
  rw [Matrix.GeneralLinearGroup.map_apply, ← hz]
  have h2 : φ (algebraMap (Loc.OL L) (FractionRing (Loc.OL L)) z) = (((z : L.1)) : PadicAlgCl l) := by
    simp only [φ, RingHom.comp_apply]
    rw [← e.commutes z]
    show algebraMap L.1 (PadicAlgCl l) (e.symm (e _)) = _
    rw [e.symm_apply_apply]
    rfl
  rw [h2, GlobalTheory.IntOfFinExt.mem_intOf_iff]
  exact ⟨(z : L.1).2, (Formalism.BasicNotions.Examples₂.LB.mem_OL L _).1 z.2⟩

end GlobalTheory.IntegralConjFinExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHermitianDownMoveAtLevelPrimePlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt


set_option maxHeartbeats 4000000 in
theorem dnCl_of_tie {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z))
    (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u))
    (hS : ∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) (hC : CarH H F) (u) (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) (v)
    (c : ((I.rec7 l Z).mem u).C.cls i)
    (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c))
    (γ₀ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi))
    (hAd : AdC (F u) i hi c (((I.rec7 l Z).fm u).dn i v c g) γ₀.1 ((F u).atT.eV v).1)
    (hloc : Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1
        (Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g))) =
      Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (clsCrd (I.rec7 l Z) u i hi c))
    (hfv : ∀ (x : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g))
      (hx : γ₀.1.1 *ᵥ x.1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c),
      ((I.rec7 l Z).fm u).fv i v _ (((F u).lv i hi).pr v _ x) = g (((F u).lv i hi).prk v c ⟨_, hx⟩)) :
    DnCl (F u).atT (F u).lv i v c g (gx i hi γ₀) ∧
      AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) (gx i hi γ₀) v := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, _root_.GlobalTheory.Mem.Col2.HAt.adOf_of_adC I hOk hP l Z H F hS hC u i hi v c _ γ₀ hAd⟩
  · intro q hq hq1 hq2
    haveI := hq.isPrime
    let Q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) :=
      ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField _)⟩
    have hu : Q.under (𝓞 (I.rec7 l Z).host.F) ≠ ((F u).atT.eV v).1 := fun h =>
      (GlobalTheory.T.host_primes_over_level_place I hOk hP l Z H F hS hC u v Q h).elim hq1 hq2
    have h1 := _root_.GlobalTheory.Mem.Col2.SameOff.use₆ I hOk hP l Z H F hS hC u i hi v c _ γ₀.1 hAd Q hu
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    exact h1
  · have e : lc ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (Formalism.L2.Herm.Ld (I.rec7 l Z) u i (((I.rec7 l Z).fm u).dn i v c g)) =
        Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi (((I.rec7 l Z).fm u).dn i v c g) :=
      dual_co (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) ((I.rec7 l Z).clsLat u i _)
    refine Submodule.map_injective_of_injective
      (f := ((crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).V →ₗ[(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E] (Fin ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.N i) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)).restrictScalars (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E)))
      (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi).injective ?_
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap]
    refine Eq.trans ?_ hloc
    exact congrArg (fun L => Formalism.HermitianLatticesTheory.localization₂ ((F u).atT.Pv v) (Formalism.L2.Forms.mulLat γ₀.1.1 L)) e
  · intro z hz
    rw [prH_eq _ _ hi, prkH_eq _ _ hi]
    have hx : γ₀.1.1 *ᵥ (toLd i hi _ z).1 ∈ Formalism.L2.Forms.Lk (F u).atT i hi v c := by
      rw [show (toLd i hi _ z).1 = crdN (I.rec7 l Z) i hi z.1 from rfl, ← crdN_gx]
      exact (mem_Lk (F u).atT i hi v c _).1 hz
    rw [hfv _ hx]
    exact congrArg g (congrArg _ (Subtype.ext (crdN_gx i hi γ₀ z.1).symm))
  · intro v' hv' z hz
    rw [prH_eq _ _ hi, prH_eq _ _ hi]
    exact _root_.GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC I hOk hP l Z H F hS hC u i hi v v' c _ γ₀.1 hAd hv' (toLd i hi c ⟨_, hz⟩) (toLd i hi _ z)
      (crdN_gx i hi γ₀ z.1)

end GlobalTheory.Mem.Col2.HAt


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.HAt.dn_move_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (g : Module.Dual (((I.rec7 l Z).mem u).A.Fv v) (((I.rec7 l Z).fm u).lk i v c)), ∃ γ, i ≤ (I.rec7 l Z).R.m → g ≠ 0 → DnCl (F u).atT (F u).lv i v c g γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).dn i v c g) γ v := by
  intro B X I hOk hP l Z H F hS hC u i v c g
  by_cases hcase : i ≤ (I.rec7 l Z).R.m ∧ g ≠ 0
  · obtain ⟨hi, hg⟩ := hcase
    by_cases hN : i = 0 ∨ i = (I.rec7 l Z).R.m
    · obtain ⟨γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnN i hi hN v c g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun _ => ⟨κ.1, κ.2, η.1, η.2, hη, hy⟩, fun h1 h2 => absurd hN (by omega)⟩ hloc hfv⟩
    · have h1 : 1 ≤ i := by omega
      have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
      obtain ⟨hβ, γ, η, κ, hη, hy, hloc, hfv, -⟩ := (F u).dnC i h1 h2 v (H.chOf u i c) ⟨c, rfl⟩ g hg
      refine ⟨gx i hi γ, fun _ _ => dnCl_of_tie I hOk hP l Z H F hS hC u i hi v c g γ
        ⟨fun h => absurd h hN, fun _ _ => ⟨hβ, κ.1, κ.2, η.1, η.2, hη, hy⟩⟩ hloc ?_⟩
      intro x hx
      rw [← (_root_.GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv I hOk hP l Z H F hS hC u i h1 h2 v (((I.rec7 l Z).fm u).dn i v c g)).1 x x rfl,
        ← (_root_.GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv I hOk hP l Z H F hS hC u i h1 h2 v c).2 ⟨_, hx⟩ ⟨_, hx⟩ rfl]
      exact hfv x hx
  · exact ⟨1, fun hi hg => absurd ⟨hi, hg⟩ hcase⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingAllHeckeEigenvalue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeSplitField

open Module

theorem aeval_baseChange {L K M : Type} [Field L] [Field K] [Algebra L K] [AddCommGroup M] [Module L M]
    (f : Module.End L M) (p : L[X]) :
    aeval (f.baseChange K) (p.map (algebraMap L K)) = (aeval f p).baseChange K := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [Polynomial.map_add (f := _), map_add (f := _), hp, hr, map_add (f := _), LinearMap.baseChange_add]
  | monomial k c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← LinearMap.baseChange_pow]
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x
    simp [Module.algebraMap_end_apply, LinearMap.baseChange_tmul]

theorem iSup_maxGen_baseChange {L K M I : Type} [Field L] [Field K] [Algebra L K] [AddCommGroup M] [Module L M]
    [FiniteDimensional L M] (op : I → Module.End L M) (hc : ∀ x y, Commute (op x) (op y)) {p : L[X]}
    (hp : Formalism.L2.Col.HeckePolyFor op p) (hsp : (p.map (algebraMap L K)).Splits) (x : I) :
    ⨆ μ, Module.End.maxGenEigenspace ((op x).baseChange K) μ = ⊤ := by
  classical
  obtain ⟨hp0, s, hs, hd⟩ := hp
  obtain ⟨c, hcx⟩ := hs x
  have e : (op x).baseChange K = ∑ y ∈ s, algebraMap L K (c y) • (op y).baseChange K := by
    rw [hcx]
    change LinearMap.baseChangeHom L K M M (∑ y ∈ s, c y • op y) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    change (c y • op y).baseChange K = _
    rw [LinearMap.baseChange_smul, algebraMap_smul]
  rw [e]
  refine Formalism.L2.Col.hfs_iSup_maxGen_sum s (fun y => (op y).baseChange K) (fun y => algebraMap L K (c y))
    (fun y _ z _ => ?_) (fun y hy => ?_)
  · change _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, (hc y z).eq]
  · apply Formalism.L2.Col.hfs_iSup_maxGen_of_splits
    refine hsp.of_dvd (Polynomial.map_ne_zero hp0) (minpoly.dvd K _ ?_)
    rw [aeval_baseChange, hd y hy, LinearMap.baseChange_zero]

theorem finiteDimensional_mtL {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) :
    FiniteDimensional what₂.LL (what₂.MtL μ j) := by
  let b := Module.Free.chooseBasis what₂.LL (what₂.MtL μ j)
  haveI : Finite (Module.Free.ChooseBasisIndex what₂.LL (what₂.MtL μ j)) := ((what₂.jMt_basis μ j b).1).finite
  exact Module.Finite.of_basis b

end GlobalTheory.HeckeSplitField

namespace GlobalTheory.HeckeSplitField

open Module

theorem exists_finExt_split : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (E0 : PlEmb D.what₂),
    (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) →
    ∀ (j : ℕ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ X : CoefIn D.what₂, X.E = E0 →
      F0.1 ≤ (X.Kx j w).1 → ∀ v k, GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k →
        ⨆ μ, (hKC (mt0 M) C.Q hR X j w v k).maxGenEigenspace μ = ⊤ := by
  intro D M C hR E0 hcomm j w
  classical
  haveI : FiniteDimensional D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := finiteDimensional_mtL D.what₂ _ j
  let op : HeightOneSpectrum (𝓞 D.host.E) × ℕ → Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) :=
    fun vk => hLC (mt0 M) C.Q hR j w vk.1 vk.2
  obtain ⟨p, hp⟩ := Formalism.L2.Col.hfs_exists_poly op
  let S : Set (PadicAlgCl (D.what₂.places.resChar w)) := ((p.map (E0.emb w)).roots.toFinset : Set _)
  haveI : Finite S := Finset.finite_toSet _
  have hfin : FiniteDimensional ℚ_[D.what₂.places.resChar w] (IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨⟨IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] S, hfin⟩, ?_⟩
  intro X hXE hF v k _
  have hmap : (p.map (ecC X j w)).map (iqC X j w) = p.map (E0.emb w) := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    rw [RingHom.comp_apply, iqC_ec, hXE]
  have hsp : (p.map (algebraMap D.what₂.LL (FractionRing (OcC X j w)))).Splits := by
    refine Polynomial.Splits.of_splits_map (iqC X j w) ?_ fun a ha => ?_
    · change ((p.map (ecC X j w)).map (iqC X j w)).Splits
      rw [hmap]
      exact IsAlgClosed.splits _
    · change a ∈ ((p.map (ecC X j w)).map (iqC X j w)).roots at ha
      rw [hmap] at ha
      have haS : a ∈ S := by
        simp only [S, Finset.coe_sort_coe, Finset.mem_coe, Multiset.mem_toFinset]
        exact ha
      exact iqC_surj X j w a (hF (IntermediateField.subset_adjoin _ _ haS))
  exact iSup_maxGen_baseChange op (fun x y => hcomm j w x.1 x.2 y.1 y.2) hp hsp (v, k)

end GlobalTheory.HeckeSplitField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitePrimitiveRootStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_primitive_root_of_clC_le : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ) (h : clC l (Kt l K₀ L) ≤ clC l (Kt l K₀ L ⊔ muK l k)), letI := (Subring.inclusion h).toAlgebra; Module.Finite ↥(clC l (Kt l K₀ L)) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ ∃ z : (↥(clC l (Kt l K₀ L ⊔ muK l k)))ˣ, IsPrimitiveRoot (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) (l ^ k) ∧ ∀ x : FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), ∃ p : Polynomial ↥(clC l (Kt l K₀ L)), ∃ d : ↥(clC l (Kt l K₀ L)), d ≠ 0 ∧ x * algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (algebraMap _ ↥(clC l (Kt l K₀ L ⊔ muK l k)) d) = algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (Polynomial.aeval (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) p) := by
  first | exact @GlobalTheory.CycLayers.finite_primitive_root | exact GlobalTheory.CycLayers.finite_primitive_root | (intros; apply GlobalTheory.CycLayers.finite_primitive_root <;> assumption)
end

