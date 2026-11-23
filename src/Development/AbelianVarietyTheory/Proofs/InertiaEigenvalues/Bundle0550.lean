module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0529
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0530
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeSpanCorrectionDistinctEigenvalues
section
noncomputable section

namespace GlobalTheory.SpanRing

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices Polynomial

theorem blockPol_map_ringHom {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (e M : Matrix (Fin n) (Fin n) A) : (blockPol e M).map f = blockPol (e.map f) (M.map f) := by
  unfold blockPol
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem map_mem_span_frac {Γ A : Type} [CommRing A] [IsDomain A] {n : ℕ}
    (σ : Γ → Matrix (Fin n) (Fin n) A) {w : Matrix (Fin n) (Fin n) A}
    (hw : w ∈ Submodule.span A (Set.range σ)) :
    w.map (toFr A) ∈ Submodule.span (FractionRing A) (Set.range fun g => (σ g).map (toFr A)) := by
  induction hw using Submodule.span_induction with
  | mem y hy => obtain ⟨h, rfl⟩ := hy; exact Submodule.subset_span ⟨h, rfl⟩
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Matrix.map_add _ (map_add _)]
    exact add_mem hy hz
  | smul c y _ hy =>
    have : (c • y).map (toFr A) = toFr A c • y.map (toFr A) := by
      ext i j; simp
    rw [this]
    exact Submodule.smul_mem _ _ hy

theorem exists_denom_span_frac {Γ A : Type} [CommRing A] [IsDomain A] {n : ℕ}
    (σ : Γ → Matrix (Fin n) (Fin n) A) {m : Matrix (Fin n) (Fin n) (FractionRing A)}
    (hm : m ∈ Submodule.span (FractionRing A) (Set.range fun g => (σ g).map (toFr A))) :
    ∃ d : A, d ≠ 0 ∧ ∃ w ∈ Submodule.span A (Set.range σ), w.map (toFr A) = toFr A d • m := by
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    exact ⟨1, one_ne_zero, σ h, Submodule.subset_span ⟨h, rfl⟩, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, w, hw, e⟩ := hy
    obtain ⟨d', hd', w', hw', e'⟩ := hz
    refine ⟨d * d', mul_ne_zero hd hd', d' • w + d • w',
      add_mem (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hw'), ?_⟩
    ext i j
    have h1 := congrFun (congrFun e i) j
    have h2 := congrFun (congrFun e' i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, map_add (f := _),
      map_mul] at h1 h2 ⊢
    rw [h1, h2]; ring
  | smul c y _ hy =>
    obtain ⟨d, hd, w, hw, e⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap A (FractionRing A) q ≠ 0 := by simpa using hq0
    refine ⟨d * q, mul_ne_zero hd hq0, p • w, Submodule.smul_mem _ _ hw, ?_⟩
    ext i j
    have h1 := congrFun (congrFun e i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h1 ⊢
    rw [h1]
    simp only [toFr]
    field_simp

theorem exists_correction_distinct_eigenvalues {Γ X A : Type} [Group Γ] [Finite X] [CommRing A]
    [IsDomain A] [CharZero A] {n t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A))
    (π : X) (g0 : Γ) (eB : X → Matrix (Fin n) (Fin n) A) (z : A) (hz : z ≠ 0)
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → A) x ≠ (f : X → A) y)
    (hirr : ∀ x, AbsIrrDistinct (overK (rep x))) (hin : InRing T rep eB) (hid : eB * eB = eB)
    (hrk : ∀ x, ((eB x).map (toFr A)).rank = t)
    (hπ : ((blockPol (eB π) (eB π * mat (rep π) g0 * eB π)).map (toFr A)).Separable) :
    ∃ s, InMatrixCongruenceModule T rep π eB s ∧ ∀ x,
      (((blockPol (eB x) (eB x * mat (rep x) g0 * eB x + z • s x)).map (toFr A)).rootSet
        (AlgebraicClosure (FractionRing A))).ncard = t := by
  classical
  have hidx : ∀ x, eB x * eB x = eB x := fun x => congrFun hid x
  have hidK : ∀ x, (eB x).map (toFr A) * (eB x).map (toFr A) = (eB x).map (toFr A) := fun x => by
    rw [← Matrix.map_mul, hidx]
  choose a b hba hab hpol using fun x => GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image ((eB x).map (toFr A)) (hidK x) (hrk x)
  have hbe : ∀ x, b x * (eB x).map (toFr A) = b x := fun x => by
    rw [← hab, ← Matrix.mul_assoc, hba, Matrix.one_mul]
  have hea : ∀ x, (eB x).map (toFr A) * a x = a x := fun x => by
    rw [← hab, Matrix.mul_assoc, hba, Matrix.mul_one]
  have hpolA : ∀ x (M : Matrix (Fin n) (Fin n) A),
      (blockPol (eB x) (eB x * M * eB x)).map (toFr A) = (b x * M.map (toFr A) * a x).charpoly := by
    intro x M
    rw [blockPol_map_ringHom, Matrix.map_mul, Matrix.map_mul, hpol]
  let φ : (X → Matrix (Fin n) (Fin n) A) →ₗ[A] (X → Matrix (Fin t) (Fin t) (FractionRing A)) :=
    { toFun := fun s x => b x * (z • s x).map (toFr A) * a x
      map_add' := fun s s' => by
        funext x
        simp only [Pi.add_apply, smul_add, Matrix.map_add _ (map_add (toFr A)), Matrix.mul_add,
          Matrix.add_mul]
      map_smul' := fun c s => by
        funext x
        have : (z • c • s x).map (toFr A) = c • (z • s x).map (toFr A) := by
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
          rw [Algebra.smul_def, mul_left_comm]
        simp only [this, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, Pi.smul_apply] }
  have hφ : ∀ s x, φ s x = b x * (z • s x).map (toFr A) * a x := fun _ _ => rfl
  obtain ⟨_, ⟨s, hs, rfl⟩, hsx⟩ := GlobalTheory.T.exists_mem_submodule_all_charpoly_separable (O := A) (K := FractionRing A) t
    ((spanRingCornerIdealModule T rep π eB).map φ) (fun x => b x * (mat (rep x) g0).map (toFr A) * a x) (by
      intro x
      by_cases hx : x = π
      · left
        subst hx
        rwa [hpolA] at hπ
      · right
        have hmem : a x * b x ∈ Submodule.span (FractionRing A)
            (Set.range fun g => (mat (rep x) g).map (toFr A)) := by
          rw [hab]
          exact map_mem_span_frac _ (eval_mem_span hin x)
        obtain ⟨m, hm, hms⟩ := GlobalTheory.T.exists_mem_span_corner_charpoly_separable (mapM (toFr A) ((Units.coeHom _).comp (rep x)))
          (a x) (b x) (hirr x) (hba x) hmem
        obtain ⟨d, hd, w, hw, hwm⟩ := exists_denom_span_frac (mat (rep x)) hm
        obtain ⟨w', hw', rfl⟩ := exists_inRing_eval (T := T) x hw
        obtain ⟨f, hf, hfx⟩ := hsep x π hx
        have hj : f - algebraMap A (X → A) (f π) ∈ T := T.sub_mem hf (T.algebraMap_mem _)
        have hjx : f x - f π ≠ 0 := sub_ne_zero.2 hfx
        have hc : toFr A (z * (f x - f π) * d) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2
            (mul_ne_zero (mul_ne_zero hz hjx) hd)
        refine ⟨_, ⟨fun y => (f - algebraMap A (X → A) (f π)) y • (eB y * w' y * eB y),
          Submodule.subset_span ⟨_, hj, by simp, w', hw', rfl⟩, rfl⟩,
          (toFr A (z * (f x - f π) * d))⁻¹, inv_ne_zero hc, ?_⟩
        have h1 : (z • ((f - algebraMap A (X → A) (f π)) x • (eB x * w' x * eB x))).map (toFr A) =
            toFr A (z * (f x - f π) * d) •
              ((eB x).map (toFr A) * m * (eB x).map (toFr A)) := by
          have h2 : ∀ (c : A) (M : Matrix (Fin n) (Fin n) A),
              (c • M).map (toFr A) = toFr A c • M.map (toFr A) := fun c M => by
            ext i j; simp
          rw [h2, h2, Matrix.map_mul, Matrix.map_mul, hwm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul, mul_assoc]
          simp
        rw [hφ, h1, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc, one_smul,
          ← Matrix.mul_assoc, ← Matrix.mul_assoc, hbe, Matrix.mul_assoc _ _ (a x), hea]
        exact hms)
  have hs' := (mem_spanRingCornerIdealModule_iff T rep π eB s).1 hs
  refine ⟨s, hs', fun x => ?_⟩
  have hc := InMatrixCongruenceModule.corner hid hs' x
  have h1 : eB x * mat (rep x) g0 * eB x + z • s x = eB x * (mat (rep x) g0 + z • s x) * eB x := by
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hc.1, hc.2]
  have h2 := hsx x
  rw [hφ, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add (toFr A))] at h2
  rw [h1, hpolA, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree h2 (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

end GlobalTheory.SpanRing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisDeRhamBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.InvBasis

variable {l : ℕ} [Fact l.Prime]

theorem pD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.AinfP l), Formalism.Per.pD l a = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) a) :=
  GlobalTheory.RingIface.pD_eq_alg

theorem zD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) :=
  GlobalTheory.RingIface.zD_eq_alg

theorem isUnit_gen_pt (l : ℕ) [Fact l.Prime] {a : Per.AinfP l} (h : Per.kerP l = Ideal.span {a}) : IsUnit (Per.pD l a) := GlobalTheory.RingIface.isUnit_of_generator l h

theorem padicInt_hom_ext_pt (f g : ℤ_[l] →+* Per.Ainf l) : f = g := by
  ext1 z
  haveI : IsHausdorff (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  rw [← sub_eq_zero]
  refine IsHausdorff.haus this _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h := PadicInt.appr_spec n z
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c := by rw [← hc]; ring
  refine ⟨f c - g c, ?_⟩
  conv_lhs => rw [hz]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

theorem zD_eq_pt (z : ℤ_[l]) :
    algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (algebraMap ℤ_[l] (Ainf l) z)) = Per.zD l z := by
  have h : algebraMap ℤ_[l] (Ainf l) = Per.zA l := padicInt_hom_ext_pt _ _
  rw [h, zD_alg_pt l z, aDp, RingHom.comp_apply]

theorem matrix_map_smul {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (r : R) (M : Matrix (Fin d) (Fin d) R) :
    (r • M).map f = f r • M.map f := by
  ext i j; simp

theorem frob_basis_eq {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) {N d : ℕ}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (hY : Y.map (inclW l) = inclW l τ ^ N • F.T) :
    Y.map WittVector.frobenius = Y * F.A.map bk.ev := by
  have hYij : ∀ i j, inclW l (Y i j) = inclW l τ ^ N * F.T i j := fun i j => by
    simpa using congrFun (congrFun hY i) j
  have hφij : ∀ i j, bk.evW bk.E ^ N * frobW l (F.T i j) = ∑ k, F.T i k * inclW l (bk.ev (F.A k j)) := fun i j => by
    simpa [Matrix.mul_apply, BK.evW] using congrFun (congrFun F.φ i) j
  refine Matrix.ext fun i j => ?_
  apply GlobalTheory.Prism.inclW_injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.map_apply, ← frobW_inclW, hYij, map_mul, map_pow, frobW_inclW, hτ.1, Matrix.mul_apply, map_sum]
  simp_rw [map_mul, hYij]
  calc (inclW l (bk.ev bk.E) * inclW l τ) ^ N * frobW l (F.T i j)
      = inclW l τ ^ N * (bk.evW bk.E ^ N * frobW l (F.T i j)) := by simp only [BK.evW, RingHom.comp_apply]; ring
    _ = _ := by rw [hφij, Finset.mul_sum]; simp only [mul_assoc, Matrix.map_apply]

theorem isUnit_Etau {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E * τ))) := by
  rw [map_mul, map_mul]
  refine IsUnit.mul ?_ ?_
  · have hk : Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)} := by
      rw [GlobalTheory.Per.kerQ_eq_map_ker_theta, ← bk.span_ev, Ideal.map_span, Set.image_singleton]
    have hu := isUnit_gen_pt l hk
    rw [pD_alg_pt] at hu
    rw [aDp, RingHom.comp_apply]
    exact hu
  · have h := _root_.GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero l K bk τ hτ 1
    rw [pow_one] at h
    exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ h).map _

theorem exists_invariant_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∃ (B : Matrix (Fin d) (Fin d) (Per.BdRp l)) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit B ∧ IsUnit Q ∧ (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) ∧ (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l (bk.ev bk.E * τ)) ^ N • Q = ((Y * F.A.map bk.ev).map (aDp l) * B).map (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q := by
  intro l _ K bk τ hτ C N d ρ F Y hDR hY
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.BKLim.exists_beta_limit l K bk N d ρ F hDR
  obtain ⟨k1, β1, hβ1, hB1⟩ := hB 1
  have hBu : IsUnit B := GlobalTheory.T.isUnit_bdRPlus_matrix_of_congr_one l K bk d k1 β1 B hβ1.1 hB1
  have hinv := _root_.GlobalTheory.BKLim.BinfInv.inv l K bk N d ρ F B hB
  have hφY := frob_basis_eq hτ F Y hY
  have hgal := _root_.GlobalTheory.GalPhi.galPhi l K bk τ hτ N d ρ F Y hY
  obtain ⟨v, hv⟩ := isUnit_Etau hτ
  set ι : Per.BdRp l →+* Per.BdR l := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  set j : Ainf l →+* Per.BdR l := ι.comp (aDp l) with hj
  set P : Matrix (Fin d) (Fin d) (Ainf l) := Y.map WittVector.frobenius with hP
  have hjv : j (bk.ev bk.E * τ) = v := hv.symm
  have hM : ((Y * F.A.map bk.ev).map (aDp l) * B).map ι = P.map j * B.map ι := by
    rw [Matrix.map_mul, ← hφY, Matrix.map_map]; rfl
  refine ⟨B, ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N • (((Y * F.A.map bk.ev).map (aDp l) * B).map ι), hBu, ?_,
    fun m => ?_, ?_, ?_⟩
  · obtain ⟨Y₀, Y₀', hY₀, hYY⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N d ρ F.toPre
    have hY0 : Y₀ = Y := Matrix.ext fun i k => GlobalTheory.Prism.inclW_injective (by
      have := congrFun (congrFun (hY₀.trans hY.symm) i) k
      simpa using this)
    rw [hY0] at hYY
    have hPP : P * Y₀'.map WittVector.frobenius = (bk.ev bk.E * τ) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
      rw [hP, ← Matrix.map_mul, hYY, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hτ.1]
    have hPj : P.map j * (Y₀'.map WittVector.frobenius).map j = ((v : Per.BdR l) ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (Per.BdR l)) := by
      rw [← Matrix.map_mul, hPP, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hjv]
    have hPu : IsUnit (P.map j) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      refine Matrix.isUnit_det_of_right_inverse (B := (((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ (2 * N)) • (Y₀'.map WittVector.frobenius).map j) ?_
      rw [Matrix.mul_smul, hPj, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hMu : IsUnit (P.map j * B.map ι) := hPu.mul (hBu.map (ι.mapMatrix (m := Fin d)))
    rw [hM, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
    exact (((v⁻¹).isUnit.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 hMu)
  · obtain ⟨k, β, -, h⟩ := hB m
    exact ⟨k, β, h⟩
  · rw [← hv, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  · intro g
    have hσj : ∀ a : Ainf l, Per.σD (g : GQ l) (j a) = j (Per.σA (g : GQ l) a) := fun a => by
      simp only [hj, RingHom.comp_apply, hι, GlobalTheory.MemLoc.ActLaws.σD_alg, GlobalTheory.MemLoc.ActLaws.σDp_aDp]
    have hσι : ∀ b : Per.BdRp l, Per.σD (g : GQ l) (ι b) = ι (Per.σDp (g : GQ l) b) := fun b =>
      GlobalTheory.MemLoc.ActLaws.σD_alg _ b
    set c : Per.BdR l := ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N with hc
    set R : Matrix (Fin d) (Fin d) (Per.BdR l) := (ρ g).map (Per.zD l) with hR
    set S : Matrix (Fin d) (Fin d) (Per.BdR l) := (P.map (Per.σA (g : GQ l))).map j with hS
    set T' : Matrix (Fin d) (Fin d) (Per.BdR l) := (B.map (Per.σDp (g : GQ l))).map ι with hT'
    set Ej : Matrix (Fin d) (Fin d) (Per.BdR l) := ((F.ε g).map ((aDp l).comp WittVector.frobenius)).map ι with hEj
    have f1 : (v : Per.BdR l) ^ N • (R * S) = Per.σD (g : GQ l) (v : Per.BdR l) ^ N • (P.map j * Ej) := by
      have h1 := congrArg (fun M => M.map j) (hgal g)
      simp only [matrix_map_smul, Matrix.map_mul, map_pow] at h1
      rw [hjv, ← hσj, hjv] at h1
      have eR : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map j = R := Matrix.ext fun a b => zD_eq_pt (ρ g a b)
      have eE : ((F.ε g).map WittVector.frobenius).map j = Ej := Matrix.ext fun _ _ => rfl
      rw [eR, eE] at h1
      exact h1
    have f2 : Ej * T' = B.map ι := by
      have h2 := congrArg (fun M => M.map ι) (hinv g)
      simpa only [Matrix.map_mul] using h2
    have f3 : (c • (P.map j * B.map ι)).map (Per.σD (g : GQ l)) = Per.σD (g : GQ l) c • (S * T') := by
      rw [matrix_map_smul, Matrix.map_mul]
      congr 2
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hS, hσj]
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hT', hσι]
    have hw : Per.σD (g : GQ l) c * Per.σD (g : GQ l) (v : Per.BdR l) ^ N = 1 := by
      rw [hc, map_pow, ← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow]
    have key : (v : Per.BdR l) ^ N • (R * (Per.σD (g : GQ l) c • (S * T'))) = P.map j * B.map ι := by
      rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, f1,
        Matrix.smul_mul, smul_smul, Matrix.mul_assoc, f2, hw, one_smul]
    rw [hM, f3]
    calc R * (Per.σD (g : GQ l) c • (S * T')) = (c * (v : Per.BdR l) ^ N) • (R * (Per.σD (g : GQ l) c • (S * T'))) := by
          rw [hc, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      _ = c • (P.map j * B.map ι) := by rw [mul_smul, key]

end GlobalTheory.BKLim.InvBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPhiContractionDiscStep
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem norm_pow_mul_eq_of_norm_mul_eq {R : Type*} [NormedRing R] (E : R) (q : ℝ)
    (hE : ∀ y, ‖E * y‖ = q * ‖y‖) (h : ℕ) (y : R) : ‖E ^ h * y‖ = q ^ h * ‖y‖ := by
  induction h generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_assoc, ih, hE, pow_succ]; ring

theorem exists_discStep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ (φ : A →+* A), φ (s X) = s X ^ l → ∀ (Φ : Disc l (s X) bk.ρ₀ →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) φ Φ → ∀ (κ : Type) (c : κ → κ → A), (∀ i (n : ℕ), {j | c i j ∉ (bk.J ^ n).map s}.Finite) → ∀ (h : ℕ) (V : κ → Disc l (s X) bk.ρ₀), (∀ j, HasSum (fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j)) (toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j)) → ∀ (ρ ρ' : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ρ' ^ l = ρ → ∀ (R : Disc l (s X) ρ →+* Disc l (s X) bk.ρ₀) (R' : Disc l (s X) ρ' →+* Disc l (s X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R' → ∀ (U : κ → Disc l (s X) ρ) (C : ℝ), 0 ≤ C → Filter.Tendsto U Filter.cofinite (nhds 0) → (∀ j, R (U j) = V j) → (∀ j, ‖U j‖ ≤ C) → ∃ U' : κ → Disc l (s X) ρ', Filter.Tendsto U' Filter.cofinite (nhds 0) ∧ (∀ j, R' (U' j) = V j) ∧ ∀ j, (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ ≤ C := by
  intro l _ K bk A _ s ι tb φ hφ Φ hΦ κ c hc h V hV ρ ρ' hρ₀ hρ1 hρ' R R' hR hR' U C hC hU hRU hUC
  obtain ⟨-, -, ⟨hρ₀pos, hρ₀1, -⟩, -⟩ := _root_.GlobalTheory.BSP.flat_disc l K bk
  have hl1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have hρpos : 0 < ρ := hρ₀pos.trans_le hρ₀
  have hρ'pos : 0 < ρ' := by
    rcases (show (0 : ℝ≥0) ≤ ρ' from zero_le).eq_or_lt with h0 | h0
    · rw [← h0, zero_pow (by omega)] at hρ'
      exact absurd hρ' hρpos.ne
    · exact h0
  have hρ'1 : ρ' < 1 := by
    by_contra hh
    push_neg at hh
    have h2 := one_le_pow₀ hh (n := l)
    rw [hρ'] at h2
    exact absurd hρ1 (not_lt.2 h2)
  have hρρ' : ρ ≤ ρ' := by rw [← hρ']; exact pow_le_of_le_one zero_le hρ'1.le (by omega)

  obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l A A φ (s X) (s X) ρ ρ' l hρ'pos (by rw [hφ]) hρ'.le
  have hc1 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) ρ' bk.ρ₀ φ (RingHom.id A) Φ' R' hΦ' hR'
  have hc2 := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).2.2.2 A A (s X) (s X) bk.ρ₀ bk.ρ₀ (RingHom.id A) φ R Φ hR hΦ
  rw [RingHom.id_comp] at hc1
  rw [RingHom.comp_id] at hc2
  have hcomm : ∀ x, R' (Φ' x) = Φ (R x) := fun x => RingHom.congr_fun (hc1.unique hc2) x
  haveI : IsUltrametricDist (Disc l (s X) ρ') := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ').1
  haveI : NonarchimedeanAddGroup (Disc l (s X) ρ') := IsUltrametricDist.nonarchimedeanAddGroup

  have hUn : Filter.Tendsto (fun i => ‖U i‖) Filter.cofinite (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.1 hU
  have hTle : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ * ‖toDisc l (s X) ρ' (c i j)‖ := fun i j =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hΦ'.norm_le _) (norm_nonneg _))
  have hTle' : ∀ i j, ‖Φ' (U i) * toDisc l (s X) ρ' (c i j)‖ ≤ ‖U i‖ := fun i j =>
    (hTle i j).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_toDisc_le _))
  have hsum : ∀ j, Summable fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j) := fun j =>
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (squeeze_zero_norm (fun i => hTle' i j) hUn)
  set Z : κ → Disc l (s X) ρ' := fun j => ∑' i, Φ' (U i) * toDisc l (s X) ρ' (c i j) with hZdef
  have hZC : ∀ j, ‖Z j‖ ≤ C := fun j =>
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun i => (hTle' i j).trans (hUC i)
  have hR'c : Continuous R' :=
    AddMonoidHomClass.continuous_of_bound R' 1 fun y => (hR'.norm_le y).trans (one_mul _).ge
  have hRZ : ∀ j, R' (Z j) = toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * V j := fun j => by
    have h1 := (hsum j).hasSum.map R' hR'c
    have h2 : (R' ∘ fun i => Φ' (U i) * toDisc l (s X) ρ' (c i j)) =
        fun i => Φ (V i) * toDisc l (s X) bk.ρ₀ (c i j) := by
      funext i
      simp only [Function.comp_apply, map_mul, hcomm, hRU, hR'.ext, RingHom.id_apply]
    rw [h2] at h1
    exact h1.unique (hV j)

  have hsmall : ∀ r : ℝ, 0 < r → {j | r < ‖Z j‖}.Finite := by
    intro r hr
    have hF : {i | r < ‖U i‖}.Finite := by
      have := Filter.eventually_cofinite.1 (hUn.eventually (ge_mem_nhds hr))
      simpa only [not_le] using this
    obtain ⟨n, hn⟩ := _root_.GlobalTheory.BSP.norm_toDisc_J_pow_small l K bk A s ρ' hρ'pos hρ'1 (r / (C + 1)) (by positivity)
    refine (hF.biUnion fun i _ => hc i n).subset ?_
    intro j hj
    by_contra hj'
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hj'
    refine (not_le.2 (show r < ‖Z j‖ from hj)) ?_
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr.le fun i => ?_
    by_cases hi : r < ‖U i‖
    · refine (hTle i j).trans ((mul_le_mul (hUC i) (hn _ (hj' i hi)) (norm_nonneg _) hC).trans ?_)
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
    · exact (hTle' i j).trans (not_lt.1 hi)
  have hZ : Filter.Tendsto Z Filter.cofinite (nhds 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => Filter.eventually_cofinite.2 ((hsmall (ε / 2) (by linarith)).subset ?_)
    intro j hj
    simp only [Set.mem_setOf_eq, dist_zero_right, not_lt] at hj ⊢
    linarith

  obtain ⟨hnorm', hdiv'⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb ρ' (hρ₀.trans hρρ') hρ'1
  obtain ⟨hnorm₀, -⟩ := GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι tb bk.ρ₀ le_rfl hρ₀1
  choose U' hU' using fun j => hdiv' R' hR' h (Z j) ⟨V j, hRZ j⟩
  have hq : (0 : ℝ) < (ρ' : ℝ) ^ (bk.Ep.natDegree * h) := by positivity
  have hnZ : ∀ j, ‖Z j‖ = (ρ' : ℝ) ^ (bk.Ep.natDegree * h) * ‖U' j‖ := fun j => by
    rw [hU' j, norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm' h, pow_mul]
  refine ⟨U', ?_, ?_, fun j => (hnZ j).symm.trans_le (hZC j)⟩
  · have he : ∀ j, ‖U' j‖ = ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹ * ‖Z j‖ := fun j => by
      rw [hnZ j, inv_mul_cancel_left₀ hq.ne']
    refine squeeze_zero_norm (fun j => (he j).le) ?_
    simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hZ).const_mul ((ρ' : ℝ) ^ (bk.Ep.natDegree * h))⁻¹
  · intro j
    have h1 : toDisc l (s X) bk.ρ₀ (s bk.E) ^ h * (R' (U' j) - V j) = 0 := by
      have h2 := hRZ j
      rw [hU' j, map_mul, map_pow, hR'.ext, RingHom.id_apply] at h2
      rw [mul_sub, h2, sub_self]
    have h3 := congrArg norm h1
    rw [norm_pow_mul_eq_of_norm_mul_eq _ _ hnorm₀ h, norm_zero] at h3
    have h4 : (0 : ℝ) < ((bk.ρ₀ : ℝ) ^ bk.Ep.natDegree) ^ h := by positivity
    exact sub_eq_zero.1 (norm_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left h4.ne'))

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableDiscCocycleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semistable_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsUnit Z → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA → ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧ bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) = bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) := by
  first | (exact @GlobalTheory.BKLim.WSeed.exists_disc_cocycle) | (exact GlobalTheory.BKLim.WSeed.exists_disc_cocycle) | (intros; apply GlobalTheory.BKLim.WSeed.exists_disc_cocycle  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachFunctorComparisonOfBhattScholze
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.HWL

theorem exists_hw_fon_cmp_of_integral : GlobalTheory.Published.BhattScholzeIntegral →
    ∀ D : D7, ∃ (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Nonempty (CmpOf D.loc D.locA HW F) := by
  intro hI D
  obtain ⟨H, F, hC, -⟩ := exists_hw_fon_cmp_ties (_root_.GlobalTheory.bhattScholze_coeff hI) D.loc D.locA D.locT
  exact ⟨H, F, hC⟩

end GlobalTheory.HWL
end

