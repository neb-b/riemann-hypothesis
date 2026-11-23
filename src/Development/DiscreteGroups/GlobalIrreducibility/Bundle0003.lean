module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import GroundTheory.LocalFields.Uniqueness
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKMCore
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0002
public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe

@[expose] public section

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvAltA
section
noncomputable section

open GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

theorem alt_std_eq_zero {A : Type} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] {M : ℕ}
    (hM : Module.finrank ℂ A < M) (b : Fin M → A) :
    ∑ σ : Equiv.Perm (Fin M), ((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun i => b (σ i)).prod = 0 := by
  have hdep : ¬ LinearIndependent ℂ b := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  have h := (MultilinearMap.alternatization (MultilinearMap.mkPiAlgebraFin ℂ M A)).map_linearDependent b hdep
  rw [MultilinearMap.alternatization_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [MultilinearMap.domDomCongr_apply, MultilinearMap.mkPiAlgebraFin_apply, Units.smul_def,
    Int.cast_smul_eq_zsmul]

theorem alt_isOpen_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (h : ∀ u ∈ U, ρ u v = v) : IsOpen {g | ρ g v = v} := by
  let T : Subgroup G :=
    { carrier := {g | ρ g v = v}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact Subgroup.isOpen_mono (H₁ := U) (H₂ := T) (fun u hu => h u hu) hU

theorem alt_star_eq {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖) (g : G) : star (π g) = π g⁻¹ := by
  have hin : ∀ x y, inner ℂ (π g x) (π g y) = inner ℂ x y := fun x y =>
    LinearIsometry.inner_map_map ⟨(π g : H →ₗ[ℂ] H), hπ g⟩ x y
  have h1 : star (π g) * π g = 1 := by
    ext x
    refine ext_inner_left ℂ fun v => ?_
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hin, ContinuousLinearMap.one_apply]
  calc star (π g) = star (π g) * (π g * π g⁻¹) := by rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = π g⁻¹ := by rw [← mul_assoc, h1, one_mul]

theorem alt_avg {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hKc : IsCompact (K : Set G)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : G →* (H →L[ℂ] H)) (e : H →L[ℂ] H) (heK : ∀ κ ∈ K, e * π κ = e)
    (hfix : ∀ x, (∀ κ ∈ K, π κ x = x) → e x = x)
    (Z : Submodule ℂ (H →L[ℂ] H)) (hZ : ∀ κ ∈ K, ∀ z ∈ Z, π κ * z ∈ Z)
    (y : H →L[ℂ] H) (hy : y ∈ Z) (U : Subgroup G) (hUo : IsOpen (U : Set G)) (hU : ∀ u ∈ U, π u * y = y) :
    e * y ∈ Z := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hU'o : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hU'o
  haveI : Fintype (K ⧸ U.subgroupOf K) := Fintype.ofFinite _
  let F : K ⧸ U.subgroupOf K → (H →L[ℂ] H) := fun q => Quotient.liftOn' q (fun κ : K => π κ * y) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ U.subgroupOf K := QuotientGroup.leftRel_apply.mp hab
    have hu : ((a⁻¹ * b : K) : G) ∈ U := Subgroup.mem_subgroupOf.mp hab'
    have hb : (b : G) = (a : G) * ((a⁻¹ * b : K) : G) := by simp
    show π a * y = π b * y
    rw [hb, map_mul, mul_assoc, hU _ hu])
  have hF : ∀ κ : K, F (κ : K ⧸ U.subgroupOf K) = π κ * y := fun κ => rfl
  have hFZ : ∀ q, F q ∈ Z := fun q => QuotientGroup.induction_on q fun κ => by
    rw [hF]; exact hZ κ κ.2 y hy
  have hFe : ∀ q, e * F q = e * y := fun q => QuotientGroup.induction_on q fun κ => by
    rw [hF, ← mul_assoc, heK κ κ.2]
  have hFs : ∀ (κ : K) q, π κ * F q = F (κ • q) := fun κ q => QuotientGroup.induction_on q fun a => by
    rw [MulAction.Quotient.smul_mk, hF, hF, smul_eq_mul, Subgroup.coe_mul, map_mul, mul_assoc]
  have hwK : ∀ κ : K, π κ * ∑ q, F q = ∑ q, F q := by
    intro κ
    rw [Finset.mul_sum]
    simp_rw [hFs κ]
    exact Equiv.sum_comp (MulAction.toPerm κ) F
  have hew : e * ∑ q, F q = ∑ q, F q := by
    ext x
    rw [ContinuousLinearMap.mul_apply]
    exact hfix _ fun κ hκ => congrArg (fun T : H →L[ℂ] H => T x) (hwK ⟨κ, hκ⟩)
  have hcard : e * ∑ q, F q = (Fintype.card (K ⧸ U.subgroupOf K) : ℂ) • (e * y) := by
    rw [Finset.mul_sum]
    simp_rw [hFe]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hn : (Fintype.card (K ⧸ U.subgroupOf K) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : e * y = (Fintype.card (K ⧸ U.subgroupOf K) : ℂ)⁻¹ • ∑ q, F q := by
    rw [← hew, hcard, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [this]
  exact Z.smul_mem _ (Z.sum_mem fun q _ => hFZ q)

end DiscreteGroups.sglob.LConv
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvBigA
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Filter Topology

namespace DiscreteGroups.sglob.LConv

section Matrices

variable {k : Type} [Field k] {m : ℕ}

def tv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) : GL (Fin n) k :=
  ⟨Matrix.transvection i j c, Matrix.transvection i j (-c),
    by rw [Matrix.transvection_mul_transvection_same _ _ h, add_neg_cancel, Matrix.transvection_zero],
    by rw [Matrix.transvection_mul_transvection_same _ _ h, neg_add_cancel, Matrix.transvection_zero]⟩

theorem val_tv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) :
    ((tv i j h c : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j c := rfl

theorem val_tv_inv {n : ℕ} (i j : Fin n) (h : i ≠ j) (c : k) :
    (((tv i j h c)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j (-c) := rfl

theorem tv_zero {n : ℕ} (i j : Fin n) (h : i ≠ j) : tv i j h (0 : k) = 1 :=
  Units.ext (by rw [val_tv, Matrix.transvection_zero, Units.val_one])

theorem continuous_tv [TopologicalSpace k] [IsTopologicalAddGroup k] {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    Continuous fun c : k => tv i j h c := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun c : k => Matrix.transvection i j c
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · show Continuous fun c : k => Matrix.transvection i j (-c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

theorem stdSum_symm_castSucc (i : Fin m) : (stdSum (rfl : m + 1 = m + 1)).symm i.castSucc = Sum.inl i := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp)

theorem stdSum_symm_last : (stdSum (rfl : m + 1 = m + 1)).symm (Fin.last m) = Sum.inr 0 := by
  rw [Equiv.symm_apply_eq]
  exact Fin.ext (by simp)

theorem corner_cs_cs (g : GL (Fin m) k) (i j : Fin m) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i.castSucc j.castSucc = (g : Matrix (Fin m) (Fin m) k) i j := by
  simp [corner, emb₂, leviEmb, leviTwo, two, stdSum_symm_castSucc]

theorem corner_last (g : GL (Fin m) k) (j : Fin (m + 1)) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [corner, emb₂, leviEmb, leviTwo, two, stdSum_symm_last]
  · simp [corner, emb₂, leviEmb, leviTwo, two, Matrix.blockDiagonal', stdSum_symm_castSucc, stdSum_symm_last,
      (Fin.castSucc_lt_last j).ne']

theorem corner_one : corner (1 : GL (Fin m) k) = 1 :=
  map_one (emb₂ k (stdSum (rfl : m + 1 = m + 1)))

theorem longElt_inv (n : ℕ) : (longElt n k)⁻¹ = longElt n k := Units.ext rfl

theorem longElt_last (j : Fin (m + 1)) :
    (longElt (m + 1) k : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = if j = 0 then 1 else 0 := by
  simp [longElt]

end Matrices

section Small

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_small {U : Set k} (hU : U ∈ 𝓝 (0 : k)) (a : k) : ∃ t : k, t ≠ 0 ∧ t ∈ U ∧ a * t ∈ U := by
  let := GroundTheory.LocalField.nontriviallyNormedField k
  have hU' : U ∩ (fun t => a * t) ⁻¹' U ∈ 𝓝 (0 : k) :=
    inter_mem hU ((continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU'
  obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt k hε
  have ht : t ∈ U ∩ (fun t => a * t) ⁻¹' U := hball (by simpa using htε)
  exact ⟨t, norm_pos_iff.1 ht0, ht.1, ht.2⟩

end Small

end DiscreteGroups.sglob.LConv

end

end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvDens
section
open scoped InnerProductSpace

noncomputable section

namespace DiscreteGroups.sglob.LConv

open CompanionTheory.D.gk.admitted

theorem irred_of_scalar {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)) (hπ : ∀ g x, ‖π g x‖ = ‖x‖)
    (hsc : ∀ T : H →L[ℂ] H, (∀ g, T * π g = π g * T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (S : Submodule ℂ H) (hcl : IsClosed (S : Set H)) (hS : ∀ g, ∀ v ∈ S, π g v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have : CompleteSpace S := hcl.completeSpace_coe
  have hcomm : ∀ g, S.starProjection * π g = π g * S.starProjection := by
    intro g
    ext z
    show S.starProjection (π g z) = π g (S.starProjection z)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hS g _ (S.starProjection_apply_mem z)
    · intro w hw
      rw [← map_sub, FinOfPIAux.inner_left π hπ]
      exact S.starProjection_inner_eq_zero z _ (hS _ _ hw)
  obtain ⟨c, hc⟩ := hsc _ hcomm
  have hP : ∀ z, S.starProjection z = c • z := fun z => by rw [hc]; rfl
  by_cases h0 : S = ⊥
  · exact Or.inl h0
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have h1 : c • x = x := by rw [← hP, Submodule.starProjection_eq_self_iff.mpr hx]
    have hc1 : c = 1 := by
      have h2 : (c - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hx0
    rw [eq_top_iff]
    intro z _
    have h3 := S.starProjection_apply_mem z
    rwa [hP, hc1, one_smul] at h3

theorem word_eq_mul_prod {R : Type*} [Ring R] (e : R) (he : e * e = e) (l : List R) :
    word e l = e * (l.map fun a => e * a * e).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [word_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc, he]

theorem finiteOfAlt : FiniteOfAlt := by
  intro G _ H _ _ _ π hπ hsc e he d hd
  have h : ∀ g : Fin d → G, stdPoly e (fun i => π (g i)) = 0 := by
    intro g
    have h0 := congrArg (fun X => e * X) (hd g)
    simp only [mul_zero] at h0
    rw [← h0, stdPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [word_eq_mul_prod e he, List.map_ofFn, mul_smul_comm, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  obtain ⟨hfd, -⟩ := finite_rank_of_irreducible_unitary G H π hπ (irred_of_scalar π hπ hsc) e d h
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional _).mpr hfd
  refine ⟨s, fun x => ?_⟩
  rw [hs]
  exact LinearMap.mem_range_self (e : H →ₗ[ℂ] H) x

end DiscreteGroups.sglob.LConv

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvKM
section
namespace DiscreteGroups.sglob.LConv

theorem extremeExists : ExtremeExists := by
  intro G M _ _ _ ρ hspan B₀ hB₀ f hf
  obtain ⟨B, ⟨hB, hext⟩, hBf⟩ := DiscreteGroups.sglob.LConvKM.extreme_exists_core ρ hspan B₀ hB₀ f hf
  exact ⟨B, ⟨hB, hext⟩, hBf⟩

end DiscreteGroups.sglob.LConv
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvKirA
section
noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] {m : ℕ}

def InH (j : ℕ) (g : GL (Fin (m + 1)) k) : Prop :=
  ∀ p q : Fin (m + 1), ¬ (p.val < j ∧ q.val < j) →
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q

def colM (c : Fin (m + 1)) (x : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  1 + Matrix.of fun p q => if q = c ∧ p < c then x p else 0

theorem colM_zero (c : Fin (m + 1)) : colM c (0 : Fin (m + 1) → k) = 1 := by
  ext p q; simp [colM]

theorem colM_mul (c : Fin (m + 1)) (x y : Fin (m + 1) → k) : colM c x * colM c y = colM c (x + y) := by
  have hAB : (Matrix.of fun p q => if q = c ∧ p < c then x p else 0) *
      (Matrix.of fun p q => if q = c ∧ p < c then y p else (0 : k)) = 0 := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r = c
    · subst hr; simp
    · simp [hr]
  simp only [colM, add_mul, mul_add, one_mul, mul_one, hAB, add_zero]
  ext p q
  simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

def U (c : Fin (m + 1)) (x : Fin (m + 1) → k) : GL (Fin (m + 1)) k :=
  ⟨colM c x, colM c (-x), by rw [colM_mul, add_neg_cancel, colM_zero],
    by rw [colM_mul, neg_add_cancel, colM_zero]⟩

theorem U_add (c : Fin (m + 1)) (x y : Fin (m + 1) → k) : U c (x + y) = U c x * U c y :=
  Units.ext (colM_mul c x y).symm

theorem U_mem (c : Fin (m + 1)) (x : Fin (m + 1) → k) : U c x ∈ unipB k (Fin (m + 1)) := by
  refine (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · show colM c x i j = 0
    simp only [colM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, h⟩; exact absurd (h.trans hji) (lt_irrefl _)
  · show colM c x i i = 1
    simp only [colM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_eq]
    rw [if_neg]
    · simp
    · rintro ⟨rfl, h⟩; exact lt_irrefl _ h

theorem superDiag_U (j : ℕ) (hj : j + 1 < m + 1) (x : Fin (m + 1) → k) :
    superDiag (U ⟨j + 1, hj⟩ x) = x ⟨j, by omega⟩ := by
  unfold superDiag
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (m + 1))]
  · rw [Finset.sum_eq_single (⟨j + 1, hj⟩ : Fin (m + 1))]
    · show colM _ x _ _ = _
      simp [colM, Fin.ext_iff]
    · intro b hb hne
      exact absurd (Fin.ext (by simpa using (Finset.mem_filter.1 hb).2)) hne
    · intro h; exact absurd (by simp) h
  · intro b _ hb
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' : q.val = b.val + 1 := (Finset.mem_filter.1 hq).2
    show colM _ x _ _ = 0
    simp only [colM, Matrix.add_apply, Matrix.of_apply]
    rw [Matrix.one_apply_ne (fun h => by rw [h] at hq'; omega), if_neg, add_zero]
    rintro ⟨rfl, -⟩
    exact hb (Fin.ext (by simp at hq' ⊢; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem InH_zero (g : GL (Fin (m + 1)) k) (hg : InH 0 g) : g = 1 :=
  Units.ext (Matrix.ext fun p q => hg p q (by simp))

end DiscreteGroups.sglob.LConvKir
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvSepI
section
noncomputable section

open MeasureTheory Topology ValuativeRel GlobalTheory.LocLanglands GlobalTheory.LocLanglands.InvInt
open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

namespace DiscreteGroups.sglob.LConv

theorem exists_pos_invariant_form {G : Type} [Group G] {H : Subgroup G} [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (hH : IsClosed (H : Set G))
    (uG : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular G) (uH : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular H) :
    ∃ I : (G → ℂ) →ₗ[ℂ] ℂ,
      ∀ f : G → ℂ, (∀ u ∈ H, ∀ g, f (u * g) = f g) → Continuous f →
        (∃ C : Set G, IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) →
        (∀ x, I (fun g => f (g * x)) = I f) ∧
        I (fun g => (starRingEnd ℂ) (f g)) = (starRingEnd ℂ) (I f) ∧
        ((∀ g, 0 ≤ (f g).re) → 0 ≤ (I f).re ∧ ((I f).re = 0 → ∀ g, (f g).re = 0)) := by
  borelize (G ⧸ H)
  obtain ⟨⟨μ, hμ⟩, -⟩ := GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause G H hH uG uH
  have := hμ.finiteOnCompacts
  have := hμ.invariant
  have := hμ.regular
  have : μ.IsOpenPosMeasure := ⟨fun U hU hne =>
    (measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ.ne_zero hU hne).ne'⟩
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {f | Integrable (descend H f) μ}
      zero_mem' := by simp
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
        exact hf.add hg
      smul_mem' := fun c f hf => by
        simp only [Set.mem_ofPred_eq, map_smul] at *
        exact hf.smul c }
  let J : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ q, descend H f q ∂μ
      map_add' := fun f g => integral_add f.2 g.2
      map_smul' := fun c f => integral_smul c (descend H f) }
  obtain ⟨I, hI⟩ := J.exists_extend
  have hIJ : ∀ f, Integrable (descend H f) μ → I f = ∫ q, descend H f q ∂μ := fun f hf =>
    LinearMap.congr_fun hI ⟨f, hf⟩
  refine ⟨I, fun f hf hc ⟨C, hC, hs⟩ => ?_⟩
  have hcd := continuous_descend hf hc
  have h1 : Integrable (descend H f) μ :=
    hcd.integrable_of_hasCompactSupport (hasCompactSupport_descend hf hC hs)
  refine ⟨fun x => ?_, ?_, fun hpos => ?_⟩
  · have h2 : Integrable (descend H fun g => f (g * x)) μ := by
      rw [descend_mul_right hf]
      exact (measurePreserving_smul x⁻¹ μ).integrable_comp_of_integrable h1
    rw [hIJ _ h1, hIJ _ h2, descend_mul_right hf]
    exact integral_smul_eq_self (descend H f)
  · have h2 : Integrable (descend H fun g => (starRingEnd ℂ) (f g)) μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp h1
    rw [hIJ _ h1, hIJ _ h2, ← integral_conj]
    rfl
  · have hre : (I f).re = ∫ q, (descend H f q).re ∂μ := by
      rw [hIJ _ h1]
      exact (integral_re h1).symm
    have hnn : 0 ≤ fun q => (descend H f q).re := fun q => hpos _
    refine ⟨hre ▸ integral_nonneg hnn, fun h0 g => ?_⟩
    rw [hre] at h0
    have hae := (integral_eq_zero_iff_of_nonneg hnn h1.re).1 h0
    have hz := (Continuous.ae_eq_iff_eq μ (Complex.continuous_re.comp hcd) continuous_zero).1 hae
    have := congrFun hz ((g⁻¹ : G) : G ⧸ H)
    simpa [descend_mk hf] using this

theorem exists_pos_isInvIntegral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) :
    ∃ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I ∧
      (∀ f, IsTestFun f → I (fun g => (starRingEnd ℂ) (f g)) = (starRingEnd ℂ) (I f)) ∧
      ∀ f, IsTestFun f → (∀ g, 0 ≤ (f g).re) → 0 ≤ (I f).re ∧ ((I f).re = 0 → ∀ g, (f g).re = 0) := by
  borelize k
  obtain ⟨I, h⟩ := exists_pos_invariant_form (H := unipB k (Fin m)) isClosed_unipB
    (fun μ _ => inferInstance)
    (fun μ hμ => @UnipHaar.haar_isMulRightInvariant k _ _ _ _ (Fin m) (Fin m) (fun _ => Unit) _ _ _ _ _ _
      (points (Fin m)) (inferInstance : MeasurableSpace (unipB k (Fin m)))
      (inferInstance : BorelSpace (unipB k (Fin m))) μ hμ)
  exact ⟨I, fun f hf => (h f hf.1 hf.2.1.continuous hf.2.2).1,
    fun f hf => (h f hf.1 hf.2.1.continuous hf.2.2).2.1, fun f hf => (h f hf.1 hf.2.1.continuous hf.2.2).2.2⟩

end DiscreteGroups.sglob.LConv

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
section
noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf GlobalTheory.SerSys GlobalTheory.SerSys.Bridge
open scoped Classical

attribute [local instance] GlobalTheory.SerSys.Bridge.factT

theorem labParamLe_of (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) :
    LabParamLe D.R.nV D L rc := fun k v n hn π hπ f hf =>
  ine_eq_of_has_green_le D.R.nV (OfLabel.ofLabel (L k) (five_le D k) hG) (L k) _ _ _ (h1 k v) (h2 k) hG (h3 k v)
    (labelsCusp _ _ _) ⟨n, π⟩ hn hπ.1 hπ.2 f hf

end DiscreteGroups.sglob.DzType.Rt

end
end

