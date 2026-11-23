module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RdBase
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterExists
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0061
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplaneMid
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrLenEuler
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0037

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RdChain
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

section

variable {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

structure IsChain (n : ℕ) (K : ℕ → Submodule F N) (t : ℕ → N) : Prop where
  mono : Monotone K
  zero : K 0 = ⊥
  top : K n = ⊤
  succ : ∀ i < n, K (i + 1) = K i ⊔ Submodule.span F {t i}
  notMem : ∀ i < n, t i ∉ K i

theorem IsChain.quot {n : ℕ} {K : ℕ → Submodule F N} {t : ℕ → N} (h : IsChain n K t) (j : ℕ) :
    IsChain (n - j) (fun i => (K (j + i)).map (K j).mkQ) (fun i => (K j).mkQ (t (j + i))) := by
  exact {
    mono := fun a b hab => Submodule.map_mono (h.mono (by omega))
    zero := by simp
    top := by
      have : K (j + (n - j)) = ⊤ := top_le_iff.1 (h.top ▸ h.mono (by omega))
      simp only [this, Submodule.map_top, Submodule.range_mkQ]
    succ := fun i hi => by
      simp only [← add_assoc]
      rw [h.succ (j + i) (by omega), Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    notMem := fun i hi hm => by
      apply h.notMem (j + i) (by omega)
      have : t (j + i) ∈ ((K (j + i)).map (K j).mkQ).comap (K j).mkQ := hm
      rwa [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 (h.mono (by omega))] at this
  }

theorem IsChain.mem {n : ℕ} {K : ℕ → Submodule F N} {t : ℕ → N} (h : IsChain n K t) {i j : ℕ}
    (hi : i < min j n) : t i ∈ K j := by
  apply h.mono (show i + 1 ≤ j by omega)
  rw [h.succ i (by omega)]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

open Classical in
theorem IsChain.sub {n : ℕ} {K : ℕ → Submodule F N} {t : ℕ → N} (h : IsChain n K t) (j : ℕ) :
    IsChain (min j n) (fun i => (K i).comap (K j).subtype)
      (fun i => if hi : t i ∈ K j then ⟨t i, hi⟩ else 0) := by
  exact {
    mono := fun a b hab => Submodule.comap_mono (h.mono hab)
    zero := by simp [h.zero]
    top := by
      rw [Submodule.comap_subtype_eq_top]
      rcases le_total j n with h1 | h1
      · rw [min_eq_left h1]
      · rw [min_eq_right h1, h.top]; exact le_top
    succ := fun i hi => by
      apply Submodule.map_injective_of_injective (K j).injective_subtype
      simp only [dite_eq_left (h.mem hi)]
      rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton, Submodule.map_comap_subtype,
        Submodule.map_comap_subtype, inf_eq_right.2 (h.mono (by omega)),
        inf_eq_right.2 (h.mono (by omega)), h.succ i (by omega)]
      rfl
    notMem := fun i hi hm => by
      apply h.notMem i (by omega)
      simp only [dite_eq_left (h.mem hi)] at hm
      exact hm
  }

theorem isChain_flag {n : ℕ} (b : Module.Basis (Fin n) F N) :
    IsChain n (flagSub b) (fun i => if h : i < n then b ⟨i, h⟩ else 0) := by
  exact {
    mono := fun a c hac => Submodule.span_mono (Set.image_mono fun j hj => lt_of_lt_of_le hj hac)
    zero := by simp [flagSub]
    top := by
      have : {j : Fin n | (j : ℕ) < n} = Set.univ := Set.eq_univ_of_forall fun j => j.2
      rw [flagSub, this, Set.image_univ, b.span_eq]
    succ := fun i hi => by
      have : {j : Fin n | (j : ℕ) < i + 1} = {j : Fin n | (j : ℕ) < i} ∪ {⟨i, hi⟩} := by
        ext j
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, Fin.ext_iff]
        omega
      simp only [dite_eq_left hi]
      rw [flagSub, this, Set.image_union, Submodule.span_union, Set.image_singleton]
      rfl
    notMem := fun i hi => by
      simp only [dite_eq_left hi]
      exact b.linearIndependent.notMem_span_image (by simp)
  }

end

section

variable (hex : type_of% @_root_.GlobalTheory.CompanionTheory.Ar.GR.fund_ex_relay) (hsq : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_restriction)
  (hsplit : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_ideal) (hos : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_characters)
  (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
  (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R)
  (hp : v (p : C) < 1) (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ)
  (hF : Fintype.card F = p ^ f)

include hex hsq hsplit hos hv hp hF

theorem chain_le (χ : MulChar F R) (n : ℕ) : ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N]
    [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier →
    ∀ (K : ℕ → Submodule F N) (t : ℕ → N), IsChain n K t → ∀ (s : ℕ → NNReal) (r : NNReal),
    (∀ i < n, HasLen v R (OmType (stepOrder AA.carrier (K i) (t i)) χ) (s i)) →
    HasLen v R (OmType AA.carrier χ) r → ∏ i ∈ Finset.range n, s i ≤ r := by
  classical
  induction n with
  | zero =>
    intro N _ _ _ _ AA hst K t h s r hs hr
    have : Subsingleton N := (Submodule.subsingleton_iff F).1
      (subsingleton_of_bot_eq_top (h.zero.symm.trans h.top))
    rw [hasLen_trivial hv hr]
    simp
  | succ n ih =>
    intro N _ _ _ _ AA hst K t h s r hs hr
    obtain ⟨σ, hσ⟩ := hex p C v R hv hp F f hF
    have : Finite (N ⧸ K 1) := Finite.of_surjective _ (K 1).mkQ_surjective
    let _ : Fintype (N ⧸ K 1) := Fintype.ofFinite _
    let _ : Fintype (K 1) := Fintype.ofFinite _
    obtain ⟨-, ⟨AQ, hQ, hQs⟩, -⟩ := hsq p C v R hv hp F f hF N AA hst (K 1)
    obtain ⟨b, -, hb⟩ := (hsplit p C v R hv hp F f hF _ AQ hQs σ hσ).1 χ
    have h1 := ih _ AQ hQs _ _ (h.quot 1) (fun i => s (1 + i)) b (fun i hi => by
      rw [hQ, quot_step _ (h.mono (by omega))]
      exact hs _ (by omega)) hb
    have ht : t 0 ≠ 0 := fun h0 => h.notMem 0 (by omega) (h0 ▸ Submodule.zero_mem _)
    have h2 := hs 0 (by omega)
    rw [h.zero] at h2
    have h3 := hasLen_line _ ht h2
    have hK : Submodule.span F {t 0} = K 1 := by
      rw [h.succ 0 (by omega), h.zero, bot_sup_eq]
    rw [hK] at h3
    rw [hQ] at hb
    have h4 := hos p C v R hv hp F f hF N AA hst (K 1) χ _ _ _ h3 hb hr
    rw [add_comm n 1, Finset.prod_range_add]
    refine le_trans ?_ h4
    rw [Finset.prod_range_one]
    exact mul_le_mul_right h1 _

theorem chain_partial (hstep : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_translation) (χ : MulChar F R) (n : ℕ) (N : Type)
    [AddCommGroup N] [Module F N] [Fintype N]
    [DecidableEq N] (AA : HopfOrder (C := C) R N) (hst : FStable F AA.carrier)
    (K : ℕ → Submodule F N) (t : ℕ → N) (h : IsChain n K t) (s : ℕ → NNReal)
    (hs : ∀ i < n, HasLen v R (OmType (stepOrder AA.carrier (K i) (t i)) χ) (s i))
    (hr : HasLen v R (OmType AA.carrier χ) (∏ i ∈ Finset.range n, s i)) (j : ℕ) :
    HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K j → N))) χ)
      (∏ i ∈ Finset.range (min j n), s i) := by
  classical
  obtain ⟨σ, hσ⟩ := hex p C v R hv hp F f hF
  have : Finite (N ⧸ K j) := Finite.of_surjective _ (K j).mkQ_surjective
  let _ : Fintype (N ⧸ K j) := Fintype.ofFinite _
  let _ : Fintype (K j) := Fintype.ofFinite _
  obtain ⟨⟨AK, hK, hKs⟩, ⟨AQ, hQ, hQs⟩, -⟩ := hsq p C v R hv hp F f hF N AA hst (K j)
  obtain ⟨a, -, ha⟩ := (hsplit p C v R hv hp F f hF _ AK hKs σ hσ).1 χ
  obtain ⟨b, hb0, hb⟩ := (hsplit p C v R hv hp F f hF _ AQ hQs σ hσ).1 χ
  have h1 := chain_le hex hsq hsplit hos p C v R hv hp F f hF χ _ _ AQ hQs _ _ (h.quot j)
    (fun i => s (j + i)) b (fun i hi => by
      rw [hQ, quot_step _ (h.mono (by omega))]
      exact hs _ (by omega)) hb
  have h2 := chain_le hex hsq hsplit hos p C v R hv hp F f hF χ _ _ AK hKs _ _ (h.sub j)
    s a (fun i hi => by
      rw [(hstep p C v R hv hp F f hF _ AK hKs _ _ ((h.sub j).notMem i hi)).2, hK,
        sub_stepRes _ (h.mono (by omega)), dite_eq_left (h.mem hi),
        ← (hstep p C v R hv hp F f hF _ AA hst _ _ (h.notMem i (by omega))).2]
      exact hs _ (by omega)) ha
  rw [hK] at ha
  rw [hQ] at hb
  have h4 := hos p C v R hv hp F f hF N AA hst (K j) χ _ _ _ ha hb hr
  have h5 : ∏ i ∈ Finset.range n, s i =
      (∏ i ∈ Finset.range (min j n), s i) * ∏ i ∈ Finset.range (n - j), s (j + i) := by
    rcases le_total j n with h6 | h6
    · rw [min_eq_left h6, ← Finset.prod_range_add, Nat.add_sub_cancel' h6]
    · rw [min_eq_right h6, Nat.sub_eq_zero_of_le h6, Finset.prod_range_zero, mul_one]
  rw [h5] at h4
  have h7 : a ≤ ∏ i ∈ Finset.range (min j n), s i :=
    le_of_mul_le_mul_right (h4.trans (mul_le_mul_right h1 _)) (pos_iff_ne_zero.2 hb0)
  rw [← le_antisymm h7 h2]
  exact ha

end

end PositivityTheory.HtPt.Rd
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.SiubOf
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siub

theorem exists_multilinear {M : Type} [AddCommGroup M] {n : ℕ} (g : (Fin n → M) → ℤ)
    (hg : ∀ (v : Fin n → M) (i : Fin n) (x y : M),
      g (Function.update v i (x + y)) = g (Function.update v i x) + g (Function.update v i y)) :
    ∃ f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin n => M) ℤ, ∀ v, f v = g v := by
  refine ⟨⟨g, ?_, ?_⟩, fun _ => rfl⟩
  · intro inst v i x y
    have h := hg v i x y
    convert h
  · intro inst v i c x
    have hi : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst hi
    have h := map_zsmul (AddMonoidHom.mk' (fun z : M => g (Function.update v i z)) (hg v i)) c x
    simp only [AddMonoidHom.mk'_apply] at h
    convert h

theorem siu_base_of (hnum : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e)) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (d : ℕ) (μ : K → ℤ), IsModelWithBase F y k₀ → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a m : ℕ, 1 ≤ a ∧ 1 ≤ m ∧ ∃ σ ∈ secOver F y (a • μ - (m : ℤ) • baseDeg k₀), σ ≠ 0 := by
  intro hK hS F _ K _ _ ι _ Ω _ _ y k₀ d μ hy hd hnef hpos
  have hP := GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.isMultiProjPrime_mIdealOver (S := F) y hy.1
  obtain ⟨f, hf⟩ := exists_multilinear (M := K → ℤ) (n := d + 1)
    (fun v => GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) v)
    (GroundTheory.Heights₂.Heights.FieldNumbers.IntNumAdd.full F K ι (mIdealOver F y) hP.multiHomog hP.relevant
      (d + 1) hd)
  obtain ⟨t, ht, hlt⟩ := hnum (K → ℤ) d f μ (baseDeg k₀) (by rw [hf]; exact hpos)
  obtain ⟨a, m, ha, hm, hva⟩ := hK (d + 1) F K ι Ω y k₀ hy hd μ hnef t ht
  have hmpos : 0 < m := by
    have ha' : (0 : ℚ) < a := by exact_mod_cast ha
    have : (0 : ℚ) < m := by rw [hm]; exact mul_pos ha' ht
    exact_mod_cast this
  obtain ⟨r, rfl⟩ := Int.eq_ofNat_of_zero_le hmpos.le
  have hr : 0 < r := by exact_mod_cast hmpos
  have hlt' := hlt a r ha hm
  rw [hf, hf] at hlt'
  have hq : (2 * (r : ℤ)) • baseDeg k₀ = (2 * r) • baseDeg k₀ := by
    rw [← natCast_zsmul]; push_cast; rfl
  rw [hq] at hlt'
  obtain ⟨C, hC⟩ := hS F K ι Ω y k₀ d (a • μ + (r : ℤ) • baseDeg k₀) (2 * r) hy hd hva (by omega)
  obtain ⟨n, hn, hfin⟩ := GroundTheory.Heights₂.Heights.Kleiman.exists_pos_of_eventually_lower (d := d)
    (sub_pos.mpr hlt') (C := C)
    (f := fun n : ℕ => (Module.finrank F
      (secOver F y (n • (a • μ + (r : ℤ) • baseDeg k₀ - (2 * r) • baseDeg k₀))) : ℝ))
    (Filter.eventually_atTop.mpr ⟨1, fun n hn => by
      have := hC n hn
      rwa [Int.cast_sub, Int.cast_mul, Int.cast_natCast]⟩) 1 one_pos
  rw [one_mul] at hfin
  have e : n • (a • μ + (r : ℤ) • baseDeg k₀ - (2 * r) • baseDeg k₀) =
      (n * a) • μ - ((n * r : ℕ) : ℤ) • baseDeg k₀ := by
    module
  rw [e] at hfin
  refine ⟨n * a, n * r, Nat.mul_pos hn ha, Nat.mul_pos hn hr, ?_⟩
  refine Submodule.exists_mem_ne_zero_of_ne_bot fun h => ?_
  rw [h, finrank_bot] at hfin
  simp at hfin

theorem prod_mem_secOver {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (i : ∀ k, ι k) :
    (∏ k, y ⟨k, i k⟩) ∈ secOver F y (1 : K → ℤ) := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c _
  rw [← Finset.prod_mul_distrib]
  refine Subalgebra.prod_mem _ fun k _ => ?_
  rw [Pi.one_apply, zpow_neg_one, ← div_eq_mul_inv]
  exact Algebra.subset_adjoin ⟨⟨k, i k⟩, rfl⟩

open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization in
theorem siu_segre_of_base (hbase : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (d : ℕ) (μ : K → ℤ), IsModelWithBase F y k₀ → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a m : ℕ, 1 ≤ a ∧ 1 ≤ m ∧ ∃ σ ∈ secOver F y (a • μ - (m : ℤ) • baseDeg k₀), σ ≠ 0) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0 := by
  intro hK hS F _ K _ _ ι _ Ω _ _ y d μ hy hd hnef hpos
  obtain ⟨a, m, ha, hm, σ, hσ, hσ0⟩ := hbase hK hS F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) d
    (pullDeg μ) (SegreBase.proof F K ι Ω y hy).1
    ((SegreDim.proof F K ι Ω y hy).trans hd)
    ((SegreNef.proof SegreDim.proof SegreNum.proof F K ι Ω y hy μ).2 hnef)
    (lt_of_lt_of_eq hpos (SegreNum.proof F K ι Ω y hy (d + 1) (fun _ => μ)).symm)
  have e : a • pullDeg (K₁ := Unit) μ - (m : ℤ) • baseDeg (Sum.inl ()) =
      pullDeg (a • μ) + (-(m : ℤ)) • baseDeg (Sum.inl ()) := by
    rw [neg_smul, ← sub_eq_add_neg]
    congr 1
    funext k
    cases k <;> simp [pullDeg]
  rw [e, SegreTwist.proof F K ι Ω y hy] at hσ
  choose i hi using hy
  have hp := ModelTwistGenerated.pow_mem_secOver y (prod_mem_secOver (F := F) y i) (m - 1)
  have hmul := ModelTwistGenerated.secOver_mul y hσ hp
  have e' : ((a • μ + fun _ => -(m : ℤ)) + ((m - 1 : ℕ) : ℤ) • (1 : K → ℤ)) = a • μ - 1 := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, Nat.cast_sub hm]
    push_cast
    ring
  rw [e'] at hmul
  exact ⟨a, ha, _, hmul, mul_ne_zero hσ0 (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => hi k))⟩

theorem siu_segre_of (hnum : ∀ (M : Type) [AddCommGroup M] (d : ℕ) (f : MultilinearMap (RingHom.id ℤ) (fun _ : Fin (d + 1) => M) ℤ) (μ e : M), 0 < f (fun _ => μ) → ∃ t : ℚ, 0 < t ∧ ∀ (a : ℕ) (m : ℤ), 1 ≤ a → (m : ℚ) = a * t → ((d + 1 : ℕ) : ℤ) * f (Fin.snoc (α := fun _ => M) (fun _ : Fin d => a • μ + m • e) ((2 * m) • e)) < f (fun _ => a • μ + m • e)) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0 :=
  siu_segre_of_base (siu_base_of hnum)

end PositivityTheory.HtPt.Siub
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.SnapperHyperplane
section
namespace PositivityTheory.HtPt.Kra

open GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem snapperHyperplane : SnapperHyperplane.Statement.{u, w} :=
  SnapperHyperplane.proof SnapperQuotAdd.closed SnapperQuotDevissage.closed SnapperHyperplaneMid.proof

theorem mixedTwistShift : MixedTwistShift.Statement.{u, w} :=
  MixedTwistShift.proof snapperHyperplane SnapperSection.full SnapperDiffPoly.proof RestrLenEuler.proof
    SubsetDiffConst.proof

theorem interNumEventual : InterNumEventual.Statement.{u, w} :=
  InterNumEventual.proof snapperHyperplane SnapperSection.full

theorem interNumAdditive : InterNumAdditive.Statement.{u, w} :=
  InterNumAdditive.proof interNumEventual (InterSumTopVanish.proof mixedTwistShift)

end PositivityTheory.HtPt.Kra
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.TrivflagNef
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem trivflag_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : Top.RootModel Ψ N) [CharZero M.Ω] (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o M.Ω] (ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω)), (∀ τ, Num.TrivFlagMod o (p : o) M.y N (fun i => M.xdeg (τ, i))) → ∀ mu : Top.Wt Ψ N, Top.Dominant mu → M.NefAt p mu 0 := by
  intro Ψ _ N M _ p _ o _ _ ho hτ mu hmu
  intro W hW
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have key : ∀ τ : Ψ, 0 ≤ ∑ i : Fin N, mu τ i * (-(geoNum 1 W (fun _ : Fin 1 => M.xdeg (τ, i)) : ℝ)) := by
    intro τ
    obtain ⟨hp, ht⟩ := trivflag_deg M.Ω M.K M.ι M.y p o ho W N (fun i => M.xdeg (τ, i)) h1 h2 h3 h4 (hτ τ)
    apply abel_sum N (mu τ) (fun i => -(geoNum 1 W (fun _ : Fin 1 => M.xdeg (τ, i)) : ℝ))
    · intro a b hab
      exact hmu τ a b hab
    · intro i hi
      have := hp i hi
      simp only [Finset.sum_neg_distrib, neg_nonneg]
      exact_mod_cast this
    · simp only [Finset.sum_neg_distrib, neg_eq_zero]
      exact_mod_cast ht
  unfold Top.RootModel.curveDeg
  rw [Fintype.sum_option]
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, M.x_deg]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_nonneg fun τ _ => ?_
  refine le_of_le_of_eq (key τ) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end PositivityTheory.HtPt.Gf
end

