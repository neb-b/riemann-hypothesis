module

public import Mathlib
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionEtaleCoordinatesFiniteZeros

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrrRepHarishChandraDistinctCuspidalLabels
section
noncomputable section
namespace GlobalTheory.HcIrr
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV Polynomial CategoryTheory

theorem isIrrRep_of_equiv {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (A : G → G) (hA : Function.Surjective A)
    (Ψ : V ≃ₗ[ℂ] V') (h : ∀ g v, Ψ (ρ (A g) v) = ρ' g (Ψ v)) (hirr : IsIrrRep ρ') : IsIrrRep ρ := by
  obtain ⟨hn, hW⟩ := hirr
  refine ⟨Ψ.toEquiv.nontrivial, fun W hinv => ?_⟩
  have hinv' : ∀ g, ∀ v ∈ W.map (Ψ : V →ₗ[ℂ] V'), ρ' g v ∈ W.map (Ψ : V →ₗ[ℂ] V') := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨ρ (A g) w, hinv _ _ hw, h g w⟩
  rcases hW _ hinv' with h0 | h1
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hv' : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := ⟨v, hv, rfl⟩
    rw [h0, Submodule.mem_bot] at hv'
    simpa using hv'
  · right
    refine eq_top_iff.2 fun v _ => ?_
    have : Ψ v ∈ W.map (Ψ : V →ₗ[ℂ] V') := h1 ▸ Submodule.mem_top
    obtain ⟨w, hw, hwv⟩ := this
    rwa [← Ψ.injective hwv]

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem isIrrRep_hcRep_of_parInd (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (h : (GlobalTheory.FinGL.parInd (natBlocks b) (leviTensor b lam)).IsIrreducible) : IsIrrRep (hcRep K b lam) := by
  let L : hcSpace K b lam ≃ₗ[ℂ] Representation.coindV (blockTri (κ := K) (natBlocks b)).subtype (leviTensor b lam) :=
    { toFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (blockTri_le_parab b) p) x⟩
      invFun := fun f => ⟨f.1, fun p x => f.2 (Subgroup.inclusion (parab_le_blockTri b) p) x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact isIrrRep_of_equiv (hcRep K b lam) _ id Function.surjective_id L (fun _ _ => rfl)
    (isIrrRep_of_isIrreducible _ h)

theorem exists_sorted {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hb : Function.Surjective b)
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) :
    ∃ (b' : Fin r → Fin s) (lam' : ∀ c : Fin s, FDRep ℂ (GL {i // b' i = c} K)), Function.Surjective b' ∧
      Monotone b' ∧ (∀ c, Simple (lam' c) ∧ IsCuspidal K (lam' c)) ∧ (∀ c, labO O (lam' c) = labO O (lam c)) ∧
      (IsIrrRep (hcRep K b' lam') → IsIrrRep (hcRep K b lam)) := by
  let e : Fin r ≃ Fin r := (Tuple.sort b).symm
  let b' : Fin r → Fin s := b ∘ e.symm
  let ec : ∀ c, {i // b i = c} ≃ {k // b' k = c} := fun c => e.subtypeEquiv (fun i => by simp [b'])
  let lam' : ∀ c : Fin s, FDRep ℂ (GL {k // b' k = c} K) := fun c => transp (ec c) (lam c)
  let A : GL (Fin r) K ≃* GL (Fin r) K := (glEquiv K e).symm
  have hpar : ∀ p : parab K b', A p.1 ∈ parab K b := by
    intro p
    obtain ⟨h1, h2⟩ := p.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e.symm e.symm (p.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h1 _ _ (by simpa [b'] using hij)
    · rw [← map_inv]
      show Matrix.reindex e.symm e.symm ((p.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      exact h2 _ _ (by simpa [b'] using hij)
  have hpar' : ∀ q : parab K b, A.symm q.1 ∈ parab K b' := by
    intro q
    obtain ⟨h1, h2⟩ := q.2
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · show Matrix.reindex e e (q.1 : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h1 _ _ hij
    · rw [← map_inv]
      show Matrix.reindex e e ((q.1⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j = 0
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
      exact h2 _ _ hij
  have hlevi : ∀ (p : parab K b') (c : Fin s),
      levi K b c ⟨A p.1, hpar p⟩ = (glEquiv K (ec c)).symm (levi K b' c p) := by
    intro p c
    apply Units.ext
    ext i j
    rfl
  have hinfl : ∀ p : parab K b', infl K b lam ⟨A p.1, hpar p⟩ = infl K b' lam' p := by
    intro p
    unfold infl
    congr 1
  have hinfl' : ∀ q : parab K b, infl K b lam q = infl K b' lam' ⟨A.symm q.1, hpar' q⟩ := by
    intro q
    rw [← hinfl]
    congr 2
    exact Subtype.ext (A.apply_symm_apply q.1).symm
  let Ψ : hcSpace K b lam ≃ₗ[ℂ] hcSpace K b' lam' :=
    { toFun := fun F => ⟨fun x => F.1 (A x), fun p x => by
        show F.1 (A (p.1 * x)) = infl K b' lam' p (F.1 (A x))
        rw [map_mul, ← hinfl]
        exact F.2 ⟨A p.1, hpar p⟩ (A x)⟩
      invFun := fun F => ⟨fun x => F.1 (A.symm x), fun q x => by
        show F.1 (A.symm (q.1 * x)) = infl K b lam q (F.1 (A.symm x))
        rw [map_mul, hinfl']
        exact F.2 ⟨A.symm q.1, hpar' q⟩ (A.symm x)⟩
      map_add' := fun F G => rfl
      map_smul' := fun a F => rfl
      left_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.apply_symm_apply x))
      right_inv := fun F => Subtype.ext (_root_.funext fun x => congrArg F.1 (A.symm_apply_apply x)) }
  refine ⟨b', lam', hb.comp e.symm.surjective, ?_, fun c => ⟨Formalism.L2.PT.simple_transp _ (hl c).1,
    Formalism.L2.PT.isCuspidal_transp _ (hl c).2⟩, fun c => GlobalTheory.SerOSys.TranspLabel.labO_transp O (ec c) (lam c), ?_⟩
  · exact Tuple.monotone_sort b
  · refine isIrrRep_of_equiv _ _ A A.surjective Ψ fun g F => ?_
    apply Subtype.ext
    funext x
    show F.1 (A x * A g) = F.1 (A (x * g))
    rw [map_mul]

theorem labO_eq_of_readings {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (d : ℕ) (e : α ≃ Fin d) (e' : β ≃ Fin d) (σ : FDRep ℂ (GL α K))
    (σ' : FDRep ℂ (GL β K)) (M : (σ : Type) ≃ₗ[ℂ] (σ' : Type))
    (hM : ∀ g v, M (σ.ρ ((glEquiv K e).symm g) v) = σ'.ρ ((glEquiv K e').symm g) (M v)) :
    labO O σ = labO O σ' := by
  rw [← GlobalTheory.SerOSys.TranspLabel.labO_transp O e σ, ← GlobalTheory.SerOSys.TranspLabel.labO_transp O e' σ']
  unfold labO
  apply O.lab_iso
  exact ⟨GlobalTheory.SerOSys.TranspLabel.repIsoOf _ _ M fun γ v => hM _ v⟩

theorem distinctFactors {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hs : ∀ c, Simple (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) :
    GlobalTheory.IndefiniteRowSideFullHecke.BlockEmbeddingFactors.DistinctFactors (natBlocks b) (leviTensor b lam) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne ⟨d, h, h', W, _, _, ρ, hf, hf'⟩
  obtain ⟨e, L, hL⟩ := _root_.GlobalTheory.HcIrr.Factor.factor_iso K r s b lam hs (b i) d h W ρ hf
  obtain ⟨e', L', hL'⟩ := _root_.GlobalTheory.HcIrr.Factor.factor_iso K r s b lam hs (b j) d h' W ρ hf'
  have hlab : labO O (lam (b i)) = labO O (lam (b j)) := by
    refine labO_eq_of_readings O d e e' _ _ (L.symm.trans L') fun g v => ?_
    obtain ⟨w, rfl⟩ := L.surjective v
    rw [← hL]
    simp [hL']
  exact hne (congrArg (fun c : Fin s => (c : ℕ)) (hinj hlab))

theorem isIrrRep_of_monotone {C : LabelConv K} (O : LabelMap K C) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (hl : ∀ c, Simple (lam c) ∧ IsCuspidal K (lam c))
    (hinj : Function.Injective (fun c => labO O (lam c))) (hm : Monotone b) : IsIrrRep (hcRep K b lam) := by
  have hd : GlobalTheory.FinGL.IsCuspDatum (natBlocks b) (leviTensor b lam) :=
    { mono := fun i j hij => hm hij
      irr := _root_.GlobalTheory.HcIrr.leviTensor_isIrreducible K r s b lam fun c => (hl c).1
      infl := fun p hp => by
        rw [leviTensor_apply]
        have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) = LinearMap.id := by
          intro c
          have h1 : levi K b c (Subgroup.inclusion (blockTri_le_parab b) p) = 1 := by
            apply Units.ext
            ext x y
            have := hp x.1 y.1 (by simp [natBlocks, x.2, y.2])
            show ((p : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 = (1 : Matrix _ _ K) x y
            rw [this]
            simp [Matrix.one_apply, Subtype.ext_iff]
          rw [h1, map_one]
          rfl
        simp only [this]
        exact PiTensorProduct.map_id
      cusp := fun S hS y hy => GlobalTheory.T.cuspidal_piTensor_no_blockUnipotent_fixed K r s b lam (fun c => (hl c).2) S hS y hy }
  exact isIrrRep_hcRep_of_parInd b lam
    ((GlobalTheory.CuspFactor.irrPar_iff_cuspidalProduct.1 GlobalTheory.FinGL.IrrProduct.irrPar).1 K r _ _ _ hd
      (distinctFactors O b lam (fun c => (hl c).1) hinj))

theorem isIrrRep_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → ∀ (C : LabelConv K) (O : LabelMap K C),
    Function.Injective (fun c => labO O (lam c)) → IsIrrRep (hcRep K b lam) := by
  intro K _ _ _ r s b lam hb hl C O hinj
  obtain ⟨b', lam', hb', hm, hl', hlab, hback⟩ := exists_sorted O b lam hb hl
  exact hback (isIrrRep_of_monotone O b' lam' hl'
    (fun c c' h => hinj (by simpa [hlab] using h)) hm)

end GlobalTheory.HcIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUniformiserAtIffAdicCompletionIsUnifAt
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.UnifVal

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isUnit_iff_v_eq_one (a : v.adicCompletionIntegers K) :
    IsUnit a ↔ Valued.v (a : v.adicCompletion K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 := (u : v.adicCompletionIntegers K).2
    have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
      ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2
    have h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
    by_contra hne
    have hlt := lt_of_le_of_ne h1 hne
    have : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
        Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) < 1 :=
      mul_lt_one_of_lt_of_le hlt h2
    rw [h3] at this; exact lt_irrefl _ this
  · intro h
    have ha0 : (a : v.adicCompletion K) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
    have hmem : (a : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
      show Valued.v ((a : v.adicCompletion K)⁻¹) ≤ 1
      rw [map_inv₀, h, inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    show (a : v.adicCompletion K) * (a : v.adicCompletion K)⁻¹ = 1
    exact mul_inv_cancel₀ ha0

theorem isUniformiserAt_iff_isUnifAt (x : (v.adicCompletion K)ˣ) :
    IsUniformiserAt K v (x : v.adicCompletion K) ↔ Formalism.L2.Host.IsUnifAt v x := by
  unfold IsUniformiserAt Formalism.L2.Host.IsUnifAt
  have hx0 : (x : v.adicCompletion K) ≠ 0 := x.ne_zero
  have hv0 : Valued.v (x : v.adicCompletion K) ≠ 0 := by simpa using hx0
  set m := WithZero.log (Valued.v (x : v.adicCompletion K)) with hm
  have hx : Valued.v (x : v.adicCompletion K) = WithZero.exp m := (WithZero.exp_log hv0).symm
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  constructor
  · rintro ⟨hmem, hirr⟩
    have hle : Valued.v (x : v.adicCompletion K) ≤ 1 := hmem
    have hnu : Valued.v (x : v.adicCompletion K) ≠ 1 := fun h =>
      hirr.not_isUnit ((isUnit_iff_v_eq_one v _).2 h)
    rw [hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
    rw [hx, ← WithZero.exp_zero, Ne, WithZero.exp_inj] at hnu
    rw [hx]
    by_contra hne
    rw [WithZero.exp_inj] at hne
    have hm2 : m ≤ -2 := by omega
    have ha : π ∈ v.adicCompletionIntegers K := by
      show Valued.v π ≤ 1
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
    have hbv : Valued.v ((x : v.adicCompletion K) / π) = WithZero.exp (m + 1) := by
      rw [map_div₀, hx, hπ, ← WithZero.exp_sub, sub_neg_eq_add]
    have hb : (x : v.adicCompletion K) / π ∈ v.adicCompletionIntegers K := by
      show Valued.v ((x : v.adicCompletion K) / π) ≤ 1
      rw [hbv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    have hprod : (⟨(x : v.adicCompletion K), hmem⟩ : v.adicCompletionIntegers K) =
        ⟨π, ha⟩ * ⟨(x : v.adicCompletion K) / π, hb⟩ := by
      apply Subtype.ext
      show (x : v.adicCompletion K) = π * ((x : v.adicCompletion K) / π)
      field_simp
    rcases hirr.isUnit_or_isUnit hprod with h | h
    · rw [isUnit_iff_v_eq_one] at h
      change Valued.v π = 1 at h
      rw [hπ, ← WithZero.exp_zero, WithZero.exp_inj] at h
      norm_num at h
    · rw [isUnit_iff_v_eq_one] at h
      change Valued.v ((x : v.adicCompletion K) / π) = 1 at h
      rw [hbv, ← WithZero.exp_zero, WithZero.exp_inj] at h
      omega
  · intro h
    have hmem : (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
      show Valued.v (x : v.adicCompletion K) ≤ 1
      rw [h, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
    refine ⟨hmem, irreducible_iff.2 ⟨?_, ?_⟩⟩
    · intro hu
      rw [isUnit_iff_v_eq_one] at hu
      change Valued.v (x : v.adicCompletion K) = 1 at hu
      rw [h, ← WithZero.exp_zero, WithZero.exp_inj] at hu
      norm_num at hu
    · intro a b hab
      have hv : Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
        have hab' : (x : v.adicCompletion K) = (a : v.adicCompletion K) * (b : v.adicCompletion K) :=
          congrArg Subtype.val hab
        rw [← map_mul, ← hab', h]
      have ha0 : Valued.v (a : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hv; exact WithZero.exp_ne_zero hv.symm
      have hb0 : Valued.v (b : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hv; exact WithZero.exp_ne_zero hv.symm
      have hale : Valued.v (a : v.adicCompletion K) ≤ 1 := a.2
      have hble : Valued.v (b : v.adicCompletion K) ≤ 1 := b.2
      rw [← WithZero.exp_log ha0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hale
      rw [← WithZero.exp_log hb0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hble
      rw [← WithZero.exp_log ha0, ← WithZero.exp_log hb0, ← WithZero.exp_add, WithZero.exp_inj] at hv
      by_cases hi : WithZero.log (Valued.v (a : v.adicCompletion K)) = 0
      · left
        rw [isUnit_iff_v_eq_one, ← WithZero.exp_log ha0, hi, WithZero.exp_zero]
      · right
        have hj : WithZero.log (Valued.v (b : v.adicCompletion K)) = 0 := by omega
        rw [isUnit_iff_v_eq_one, ← WithZero.exp_log hb0, hj, WithZero.exp_zero]

end GlobalTheory.UnifVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetBlockBoundLeExpKernelBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.BlockNumber

theorem factor_eq_exp {a : ℕ} (nu : DomWeight a) (y : ℕ → ℚ) (b : ℕ) (L : ℝ) (h0 : ∀ l, 0 ≤ nu.w l)
    (hy : ∀ l : Fin a, ((nu.w l : ℤ) : ℚ) = y l) :
    (Real.exp L)⁻¹ ^ GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu * Real.exp 1 * (2 * (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) + 2) ^ (2 * (a * b)) *
      Real.exp (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ)) =
    Real.exp (((∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) - ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) * L) +
      (1 + 2 * ((a : ℝ) * b) * Real.log (2 * ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) + 2))) := by
  have hr : ∀ l : Fin a, ((y l : ℚ) : ℝ) = (nu.w l : ℝ) := fun l => by rw [← hy l]; simp
  have hs : ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) = (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) := by
    rw [Finset.sum_range, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]
    have := Int.toNat_of_nonneg (h0 l)
    exact_mod_cast this.symm
  have hp : (∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ) := by
    rw [Finset.sum_range (fun i => Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]; rfl
  rw [hs, hp]
  set s := GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu
  have hpos : (0 : ℝ) < 2 * (s : ℝ) + 2 := by positivity
  have e1 : (Real.exp L)⁻¹ ^ s = Real.exp (-((s : ℝ) * L)) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  have e2 : (2 * (s : ℝ) + 2) ^ (2 * (a * b)) = Real.exp (2 * ((a : ℝ) * b) * Real.log (2 * (s : ℝ) + 2)) := by
    conv_lhs => rw [← Real.exp_log hpos, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [e1, e2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

theorem sq_le_exp (C A g T : ℕ) (G r L : ℝ) (hG : 1 ≤ G) (hT : 1 ≤ T) (hr : 0 ≤ r) (hg : 1 ≤ g) (hA : g ≤ A) :
    (G ^ (C * A) * ((T : ℝ) * G) ^ (2 * (2 * g)) * Real.sqrt (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp (L / 2)) ^ 2 ≤
      Real.exp (L + ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2)) + 2 * (((C : ℝ) + 4) * A * Real.log (G * T)))) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hGT : 1 ≤ G * T := one_le_mul_of_one_le_of_one_le hG hT'
  have hx : (0 : ℝ) < 2 * (g : ℝ) * r + 1 := by positivity
  have h8 : (0 : ℝ) < 8 + 32 * (g : ℝ) * (r / 2) := by positivity
  have e1 : Real.exp ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2))) = 8 ^ g * (2 * (g : ℝ) * r + 1) ^ g := by
    rw [Real.exp_nat_mul, Real.exp_log h8, ← mul_pow]; congr 1; ring
  have e2 : Real.exp (2 * (((C : ℝ) + 4) * A * Real.log (G * T))) = (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) := by
    rw [← pow_add]
    conv_rhs => rw [← Real.exp_log (show (0 : ℝ) < G * T by linarith), ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have e3 : Real.exp (L / 2) ^ 2 = Real.exp L := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.exp_add, Real.exp_add, e1, e2, mul_pow, mul_pow, mul_pow, e3, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_mul]
  have b1 : G ^ (C * A * 2) ≤ (G * T) ^ (2 * (C * A)) := by
    rw [mul_comm (C * A) 2]
    exact pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hT') _
  have b2 : ((T : ℝ) * G) ^ (2 * (2 * g) * 2) ≤ (G * T) ^ (8 * A) := by
    rw [mul_comm (T : ℝ) G]
    exact pow_le_pow_right₀ hGT (by omega)
  have b3 : (3 : ℝ) ≤ 8 ^ g := by
    calc (3 : ℝ) ≤ 8 ^ 1 := by norm_num
      _ ≤ 8 ^ g := pow_le_pow_right₀ (by norm_num) hg
  have hG0 : 0 ≤ G := by linarith
  calc G ^ (C * A * 2) * ((T : ℝ) * G) ^ (2 * (2 * g) * 2) * (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L
      ≤ (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) * (8 ^ g * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L := by gcongr
    _ = _ := by ring

theorem tmax_le_exp_kernelBound : ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : NumDatum) (δ : Code N) (T : ℕ) (i : ℕ) (ι : Type) [Fintype ι] (pl : RPl N.R ≃ ι) (nu : ι → DomWeight (N.R.N i)) (logOm : RPl N.R → ℝ) (logTh : ℝ), i < N.R.m → 2 ≤ T → (∀ τ l, 0 ≤ (nu τ).w l) → (∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((nu (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l) → GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax (N.R.N (i + 1)) nu (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) * ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) ^ (2 * (2 * N.R.f * N.R.N i * N.R.N (i + 1))) * Real.sqrt (3 * (2 * ((N.R.f * N.R.N i * N.R.N (i + 1) : ℕ) : ℝ) * N.rd + 1) ^ (N.R.f * N.R.N i * N.R.N (i + 1))) * Real.exp (logTh / 2)) (fun τ => Real.exp (logOm (pl.symm τ))) ≤ Real.exp (kernelBound_sq N δ T CK (i + 1) logOm logTh 1 1 1 1) := by
  intro C
  refine ⟨(C : ℝ) + 4, by positivity, ?_⟩
  intro N δ T i ι _ pl nu logOm logTh hi hT h0 hy
  have hm := N.R.two_le_m
  have hk := N.R.m_add_three_le_k
  have ha : 1 ≤ N.R.N i := by unfold Ranks.N; omega
  have hb : 1 ≤ N.R.N (i + 1) := by unfold Ranks.N; omega
  have hf : 1 ≤ N.R.f := by
    have : 0 < N.R.ord := N.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have haN : N.R.N i ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have hbN : N.R.N (i + 1) ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  have hg : 1 ≤ N.R.f * N.R.N i * N.R.N (i + 1) := Nat.mul_pos (Nat.mul_pos hf ha) hb
  have hA : N.R.f * N.R.N i * N.R.N (i + 1) ≤ N.R.f * N.R.m ^ 2 * N.Nm ^ 2 := by
    have h1 : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc N.R.f * N.R.N i * N.R.N (i + 1) = N.R.f * 1 * (N.R.N i * N.R.N (i + 1)) := by ring
      _ ≤ N.R.f * N.R.m ^ 2 * (N.Nm * N.Nm) := by gcongr
      _ = _ := by ring
  have hG : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast (N.g_prime 0).one_le) (by exact_mod_cast (N.g_prime 1).one_le)
  have hr : 0 ≤ N.rd := by unfold NumDatum.rd Formalism.HC.HostRaw.rd; positivity
  have key := sq_le_exp C _ _ T _ N.rd logTh hG (by omega) hr hg hA
  have hprod := fun z : RPl N.R => factor_eq_exp (nu (pl z)) (N.nu δ (i + 1) z) (N.R.N (i + 1)) (logOm z) (h0 _) (hy z)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax
  rw [← pl.prod_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.prod_congr rfl fun z _ => hprod z, ← Real.exp_sum]
  have e1 : C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2 = C * (N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by ring
  have e2 : 2 * N.R.f * N.R.N i * N.R.N (i + 1) = 2 * (N.R.f * N.R.N i * N.R.N (i + 1)) := by ring
  have e3 : ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) = (T : ℝ) * ((N.g 0 : ℝ) * N.g 1) := by push_cast; ring
  rw [e1, e2, e3]
  refine (mul_le_mul_of_nonneg_right key (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  unfold kernelBound_sq NumDatum.nuAbs NumDatum.v
  simp only [Nat.add_sub_cancel, Finset.sum_add_distrib, Nat.cast_one, mul_one, Real.log_one]
  push_cast
  simp only [mul_assoc]
  ring

end GlobalTheory.BlockNumber
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetFinsetLinearCombination
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem GlobalTheory.ColNorms.jetC_sum_mul : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → VCx ι a b → ℂ), (∀ x ∈ R, Differentiable ℂ (F x)) → ∀ m, jetC cD (fun z => ∑ x ∈ R, c x * F x z) m = ∑ x ∈ R, c x * jetC cD (F x) m := by
  intro ι _ a b cD α R c F hF m
  have key : ∀ (k : ℕ) (v : Fin k → VCx ι a b),
      iteratedFDeriv ℂ k (fun w => ∑ i ∈ R, c i * F i w) 0 v =
        ∑ i ∈ R, c i * iteratedFDeriv ℂ k (F i) 0 v := by
    intro k v
    have hC : ∀ i ∈ R, ContDiff ℂ k (F i) := fun i hi =>
      GlobalTheory.SCV.contDiff_of_differentiable (hF i hi) _
    have h1 := iteratedFDeriv_sum (𝕜 := ℂ) (f := fun i w => c i * F i w) (u := R) (i := k)
      (fun i hi => contDiff_const.mul (hC i hi))
    rw [h1, Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 := iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c i) (f := F i) (i := k) (x := 0)
      (hC i hi).contDiffAt
    simp only [smul_eq_mul] at h2
    rw [h2]
    simp
  unfold jetC derivAt0
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionLogCanonical
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem l2ExtensionLogCanonical' : GlobalTheory.Published.L2ExtensionLogCanonical := by
  intro n hn Y _ _ _ _ _ _ ι La _ A hH E L s hs hS hjac hle δ hδ hcurv f
  obtain ⟨Λ, τ, z, β, hdata⟩ := _root_.GlobalTheory.exists_etale_frame_of_finite_zeroSet n Y ι La A hn hH E L s hs hS
  exact _root_.GlobalTheory.l2_extension_of_etale_coordinates n Y ι La A hn E L s hs hS hjac hle δ hδ hcurv Λ τ z β hdata f

end GlobalTheory
end

