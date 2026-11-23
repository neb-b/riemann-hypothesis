module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValOfPowAssociated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0386

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsOverAcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.CrisPeriods

variable {l : ℕ} [Fact l.Prime]

private theorem padicInt_hom_ext {R : Type} [CommRing R] [IsHausdorff (Ideal.span {(l : R)}) R]
    (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {(l : R)}) inferInstance _ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n z)
  have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * y := by rw [← hy]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨f y - g y, ?_⟩
  have hf := congrArg f hz
  have hg := congrArg g hz
  rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast] at hf hg
  rw [hf, hg]
  ring

private theorem zA_eq_alg (z : ℤ_[l]) : Per.zA l z = algebraMap ℤ_[l] (Ainf l) z :=
  haveI : IsHausdorff (Ideal.span {(l : Ainf l)}) (Ainf l) :=
    (WittVector.isAdicCompleteIdealSpanP (p := l) (k := Per.Fl l)).toIsHausdorff
  padicInt_hom_ext (R := Ainf l) (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) z

private theorem j_alg (C : Core l) (a : Ainf l) : C.j (algebraMap (Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.MemLoc.ULaws.alg_acris, C.j_cris.on0]
  rfl

private theorem alg_alg_eq_aB (C : Core l) (a : Ainf l) :
    algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Ainf l) (Per.Acris l) a) = Per.aB l a := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [C.ι_j, j_alg, GlobalTheory.MemLoc.ULaws.iota_aB]

private theorem aB_zA (C : Core l) (z : ℤ_[l]) : Per.aB l (Per.zA l z) = Per.zB l z := by
  apply GlobalTheory.MemLoc.ULaws.iota_injective C
  rw [← GlobalTheory.MemLoc.ULaws.u_padicInt C, GlobalTheory.MemLoc.ULaws.iota_aB, C.ι_u, ← C.o_sec.z]
  rfl

theorem kap_map (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a))
    (z : ℤ_[l]) (hn : ∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) :
    (GlobalTheory.SstPer.kap C bk k₀ k Mn z).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
      (l : Per.Bcris l) ^ k₀ • ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) *
        (Per.zB l z * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i := by
  have hz : ∀ w : ℤ_[l], algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Ainf l) (Per.Acris l) (Per.zA l w)) =
      Per.zB l w := fun w => (alg_alg_eq_aB C _).trans (aB_zA C w)
  have hM : (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
      (algebraMap (Per.Acris l) (Per.Bcris l)) = Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
    exact alg_alg_eq_aB C _
  have he : ∀ i ∈ Finset.range d, Per.zB l (GlobalTheory.SstPer.ecoef l k₀ k i) =
      (l : Per.Bcris l) ^ k₀ * C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) := by
    intro i hi
    rw [← (GlobalTheory.MemLoc.ULaws.u_laws l C).2.2.1, GlobalTheory.SstPer.ecoef_val (hn i (Finset.mem_range.1 hi))]
    show C.qB _ = _
    rw [GlobalTheory.SstPer.ecoefQ, map_mul, map_pow, map_natCast]
  unfold GlobalTheory.SstPer.kap
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← RingHom.mapMatrix_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [RingHom.mapMatrix_apply, map_smul_ring, ← RingHom.mapMatrix_apply, map_pow, RingHom.mapMatrix_apply, hM,
    smul_smul]
  congr 1
  rw [map_mul, map_pow, map_mul, hz, hz, he i hi, Core.tB]
  ring

end GlobalTheory.CrisPeriods

namespace GlobalTheory.CrisPeriods

theorem periods_over_Acris_sst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∀ (k k₀ : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), (∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l k₀ k i‖ ≤ 1) → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * GlobalTheory.SstPer.kap C bk k₀ k Mn (c g))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  intro l _ K bk P AI T C _hFits d ρ U U' hUU' c₁ F hφ k k₀ Mn c hn hgal
  have hA := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).1
  obtain ⟨_, _, -, -, -, hFilt, -⟩ := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
  obtain ⟨-, hmul, -, hiff, -, -, hinj⟩ := _root_.GlobalTheory.MemLoc.seed_fil l C (xi C.ε) C.ker_theta.symm
  have AL := GlobalTheory.MemLoc.ActLaws.act_laws l
  obtain ⟨N₁, h₁⟩ := exists_lift C hA U
  obtain ⟨N₂, h₂⟩ := exists_lift C hA U'
  refine ⟨max N₁ N₂, fun N hN X X' hX hX' => ?_⟩
  obtain ⟨Z, hZ⟩ := h₁ N (le_of_max_le_left hN)
  obtain ⟨Z', hZ'⟩ := h₂ N (le_of_max_le_right hN)
  have hmi : Function.Injective
      (fun M : Matrix (Fin d) (Fin d) (Per.Acris l) => M.map (algebraMap (Per.Acris l) (Per.Bcris l))) :=
    Matrix.map_injective hinj
  have hXm : ∀ Y : Matrix (Fin d) (Fin d) bk.S,
      ((Y.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))).map C.ι =
        Y.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) := by
    intro Y
    ext i j
    simp only [Matrix.map_apply, RingHom.comp_apply]
    rw [C.ι_j]
    congr 1
    exact j_alg C _
  have htN : C.ι (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ^ N ∈ Per.FilD l N := by
    rw [C.ι_j, ← map_pow, hiff, hFilt]
    exact Ideal.mem_span_singleton_self _
  refine ⟨Z, Z', ?_, ?_, ?_, ?_, ?_⟩
  · apply hmi
    simp only
    rw [Matrix.map_mul, hZ, hZ', map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), smul_mul_smul_comm,
      hUU', map_pow, ← pow_add, two_mul]
  · apply hmi
    simp only
    have hZφ : (Z.map (phiA l)).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.φB l) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.2 (Z i j)).symm
    have hFm : (F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = F.map ((Per.aB l).comp (wA l bk.a).toRingHom) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply, bk.ev_C]
      exact alg_alg_eq_aB C _
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (phiA l C.t) =
        Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.2 C.t).symm
    rw [map_smul_ring, hZφ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hFm, hZ, map_pow, map_pow, ht,
      Matrix.smul_mul, ← hφ]
    simp only [map_mul, map_pow, map_natCast, smul_smul]
    congr 1
    ring
  · intro g
    apply hmi
    simp only
    have hZσ : (Z.map (sigA (g : GQ l))).map (algebraMap (Per.Acris l) (Per.Bcris l)) =
        (Z.map (algebraMap (Per.Acris l) (Per.Bcris l))).map (Per.σB (g : GQ l)) := by
      ext i j
      exact (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ (Z i j)).symm
    have hρ : ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l)))).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) = (ρ g).map (Per.zB l) := by
      ext i j
      simp only [Matrix.map_apply, RingHom.comp_apply]
      rw [alg_alg_eq_aB C, ← zA_eq_alg, aB_zA C]
    have ht : algebraMap (Per.Acris l) (Per.Bcris l) (sigA (g : GQ l) C.t) =
        Per.σB (g : GQ l) (algebraMap (Per.Acris l) (Per.Bcris l) C.t) :=
      (AL.2.2.2.2.2.2.2.2.2.2.2.1 _ C.t).symm
    rw [map_smul_ring, Matrix.map_mul, hρ, hZσ, hZ, map_smul_ring, map_smul_ring, Matrix.map_mul, hZ,
      kap_map C bk k₀ k Mn (c g) hn]
    simp only [map_pow, map_mul, map_natCast, ht]
    rw [Matrix.mul_smul, hgal g, Matrix.smul_mul, Matrix.mul_smul]
    simp only [smul_smul, Core.tB]
    congr 1
    ring
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) =
        ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι ((U * (X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l))) i j) =
        (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX i j)
  · intro i j
    rw [← hiff, ← C.ι_j]
    have e : algebraMap (Per.Acris l) (Per.Bcris l) ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) =
        ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z').map (algebraMap (Per.Acris l) (Per.Bcris l))) i j :=
      rfl
    rw [e, Matrix.map_mul, hZ', Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow]
    have e2 : C.ι (((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map
        (algebraMap (Per.Acris l) (Per.Bcris l)) * U') i j) =
        (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j := by
      rw [← hXm]
      exact congrFun (congrFun (Matrix.map_mul (f := C.ι)) i) j
    rw [e2, show ((2 * N : ℕ) : ℤ) = (N : ℤ) + (N : ℤ) by push_cast; ring]
    exact hmul _ _ _ _ htN (hX' i j)

end GlobalTheory.CrisPeriods
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTopOfResidue
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.Burnside

theorem span_top_of_residue {G O n : Type} [CommRing O] [IsLocalRing O] [Fintype n] [DecidableEq n] (T : G → Matrix n n O)
    (h : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (T g).map (IsLocalRing.residue O)) = ⊤) :
    Submodule.span O (Set.range T) = ⊤ := by
  have hB : ∀ B : Matrix n n (IsLocalRing.ResidueField O), ∃ M ∈ Submodule.span O (Set.range T),
      M.map (IsLocalRing.residue O) = B := fun B => by
    have hM : B ∈ Submodule.span (IsLocalRing.ResidueField O)
        (Set.range fun g => (T g).map (IsLocalRing.residue O)) := h ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨g, rfl⟩ := hB
      exact ⟨T g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, Matrix.map_zero _ (map_zero _)⟩
    | add B B' _ _ h h' =>
      obtain ⟨M, hM, rfl⟩ := h
      obtain ⟨M', hM', rfl⟩ := h'
      exact ⟨M + M', Submodule.add_mem _ hM hM', Matrix.map_add _ (map_add _) _ _⟩
    | smul t B _ h =>
      obtain ⟨M, hM, rfl⟩ := h
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
      exact ⟨t • M, Submodule.smul_mem _ _ hM, by ext p q; simp⟩
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson _) fun M _ => ?_
  obtain ⟨M', hM', e⟩ := hB (M.map (IsLocalRing.residue O))
  have e1 : M = M' + (M - M') := by abel
  rw [e1]
  refine Submodule.add_mem_sup hM' ?_
  rw [Matrix.matrix_eq_sum_single (M - M')]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  have e2 : Matrix.single p q ((M - M') p q) = (M - M') p q • Matrix.single p q (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e2]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [← IsLocalRing.residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun e p) q).symm

theorem eq_top_of_map {G O A n : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype n] [DecidableEq n]
    (T : G → Matrix n n O) (h : Submodule.span O (Set.range T) = ⊤) (S : Submodule A (Matrix n n A))
    (hS : ∀ g, (T g).map (algebraMap O A) ∈ S) : S = ⊤ := by
  have hB : ∀ B : Matrix n n O, B.map (algebraMap O A) ∈ S := fun B => by
    have hM : B ∈ Submodule.span O (Set.range T) := h ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨g, rfl⟩ := hB
      exact hS g
    | zero => rw [Matrix.map_zero _ (map_zero _)]; exact Submodule.zero_mem _
    | add B B' _ _ h h' => rw [Matrix.map_add _ (map_add _)]; exact Submodule.add_mem _ h h'
    | smul t B _ h =>
      have : (t • B).map (algebraMap O A) = algebraMap O A t • B.map (algebraMap O A) := by ext p q; simp
      rw [this]
      exact Submodule.smul_mem _ _ h
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  have : Matrix.single p q (M p q) = M p q • (Matrix.single p q (1 : O)).map (algebraMap O A) := by
    rw [Matrix.map_single, map_one, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (hB _)

theorem span_twist_eq_top : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Submodule.span A (Set.range fun g => ((κ g : Aˣ) : A) • (Tmat i s g).map (algebraMap (X.O0 i) A)) = ⊤ := by
  intro D N X bkP i s A _ _ _ _ κ Q hS
  refine eq_top_of_map (fun g => ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)))
    (span_top_of_residue _ hS.1.2.1.1) _ fun g => ?_
  have : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A) =
      (algebraMap (X.O0 i) A ((chiS i s g : (X.O0 i)ˣ) : X.O0 i) * (((κ g)⁻¹ : Aˣ) : A)) •
        (((κ g : Aˣ) : A) • (Tmat i s g).map (algebraMap (X.O0 i) A)) := by
    rw [smul_smul, Units.inv_mul_cancel_right]
    ext p q
    simp only [Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← map_mul, Units.mul_inv_cancel_left]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end GlobalTheory.NewPrime.Burnside
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaGaloisFixedOfCongrBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem GlobalTheory.BKLim.theta_gal_fixed_of_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Per.BdRp l) (M k : ℕ) (s : bk.S), (l : Per.BdRp l) ^ k * aDp l (bk.ev bk.E) ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l (M + 1) → ∀ g : ↥(GK K), Per.σC (g : GQ l) (Per.θD l x) = Per.θD l x := by
  intro l _ K bk x M k s h g
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  obtain ⟨hfil, -⟩ := GlobalTheory.MemLoc.seed_fil l C (bk.ev bk.E) bk.span_ev
  obtain ⟨-, hker, -, hth, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  haveI : IsDomain (Per.BdRp l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).1
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  set ξ := aDp l (bk.ev bk.E) with hξ

  have hξ0 : ξ ≠ 0 := by
    intro h0
    have h2 : aDp l (bk.ev bk.E) ∈ Per.FilP l 2 := by
      rw [hfil, ← hξ, h0]; exact zero_mem _
    have h3 := ((GlobalTheory.AinfEPow.ePow_facts l K bk 2).2.2.1 _).1 h2
    obtain ⟨c, hc⟩ := h3
    have hE := GlobalTheory.AinfEPow.evE_ne_zero bk
    have h4 : bk.ev bk.E * 1 = bk.ev bk.E * (bk.ev bk.E * c) := by rw [mul_one]; nth_rewrite 1 [hc]; ring
    have h5 := mul_left_cancel₀ hE h4
    have h6 := congrArg (Per.θ l) h5
    have h7 : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [map_one, map_mul, h7, zero_mul] at h6
    exact one_ne_zero h6

  have hsM : aDp l (bk.ev s) ∈ Per.FilP l M := by
    have h1 : (l : Per.BdRp l) ^ k * ξ ^ M * x ∈ Per.FilP l M := by
      rw [hfil, Ideal.mem_span_singleton]; exact ⟨(l : Per.BdRp l) ^ k * x, by ring⟩
    have h2 : (l : Per.BdRp l) ^ k * ξ ^ M * x - aDp l (bk.ev s) ∈ Per.FilP l M := by
      rw [hfil] at h ⊢
      rw [Ideal.mem_span_singleton] at h ⊢
      exact (pow_dvd_pow _ (Nat.le_succ M)).trans h
    have := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_cancel] at this
  obtain ⟨s', hs'⟩ := (GlobalTheory.AinfEPow.ePow_facts l K bk M).2.1 s (((GlobalTheory.AinfEPow.ePow_facts l K bk M).2.2.1 _).1 hsM)

  have hdiff : (l : Per.BdRp l) ^ k * x - aDp l (bk.ev s') ∈ Per.FilP l 1 := by
    rw [hfil, pow_one, Ideal.mem_span_singleton]
    have h' := h
    rw [hfil, Ideal.mem_span_singleton, hs', map_mul, map_mul, map_pow, map_pow, ← hξ] at h'
    obtain ⟨y, hy⟩ := h'
    refine ⟨y, ?_⟩
    have e : ξ ^ M * ((l : Per.BdRp l) ^ k * x - aDp l (bk.ev s')) = ξ ^ M * (ξ * y) := by
      rw [← mul_assoc, ← pow_succ, ← hy]; ring
    exact mul_left_cancel₀ (pow_ne_zero M hξ0) e
  rw [← hker, map_sub, sub_eq_zero, map_mul, map_pow, map_natCast, hth,
    bk.θ_ev (bk.str.symm (Ideal.Quotient.mk _ s')) s' (bk.str.apply_symm_apply _).symm] at hdiff
  have hfix : Per.σC (g : GQ l) ((intToOC K (bk.str.symm (Ideal.Quotient.mk _ s')) : OC l) : ℂ_[l]) =
      ((intToOC K (bk.str.symm (Ideal.Quotient.mk _ s')) : OC l) : ℂ_[l]) := by
    rw [coe_intToOC]
    exact (GlobalTheory.RingBasics.σC_coe (g : GQ l) _).trans (congrArg _
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (_ : ↥K.1).2))
  have hl : ((l : ℂ_[l]) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  apply mul_left_cancel₀ hl
  have e2 := congrArg (Per.σC (g : GQ l)) hdiff
  rw [map_mul, map_pow, map_natCast, hfix, ← hdiff] at e2
  exact e2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceEstimateScaledProductSpanLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

open scoped BigOperators

def trBound {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) : ℝ :=
  ∑ k, ∑ x ∈ t k, ‖x.trace‖

theorem trBound_nonneg {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) :
    0 ≤ trBound t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem le_trBound {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (k : Fin m) {x : Matrix (Fin a) (Fin a) (Om l)} (hx : x ∈ t k) : ‖x.trace‖ ≤ trBound t := by
  unfold trBound
  refine le_trans ?_ (Finset.single_le_sum (f := fun k => ∑ x ∈ t k, ‖x.trace‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  exact Finset.single_le_sum (f := fun x => ‖x.trace‖) (fun _ _ => norm_nonneg _) hx

theorem norm_trace_latL {l : ℕ} [Fact l.Prime] {a m : ℕ} (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l)))
    (M : ℕ) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)) (hy : y ∈ latL t M) (k : Fin m) :
    ‖(y k).trace‖ ≤ ((l : ℝ)⁻¹) ^ M * trBound t := by
  have h0 : 0 ≤ ((l : ℝ)⁻¹) ^ M * trBound t := mul_nonneg (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) (trBound_nonneg t)
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨z, hz, rfl⟩ := hj
    dsimp only
    by_cases hjk : k = j
    · subst hjk
      rw [Pi.single_eq_same, Matrix.trace_smul, smul_eq_mul, norm_mul, norm_pow, norm_l]
      exact mul_le_mul_of_nonneg_left (le_trBound t k hz) (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _)
    · rw [Pi.single_eq_of_ne hjk, Matrix.trace_zero, norm_zero]
      exact h0
  | zero => simpa using h0
  | add x y _ _ hx hy =>
    rw [Pi.add_apply, Matrix.trace_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [Pi.smul_apply, Matrix.trace_smul, ← zOm_smul, smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_zOm_le c)).trans hx

end GlobalTheory.TraceConjugationCover

namespace GlobalTheory

theorem trace_estimate_latL : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))) (c N n : ℕ) (cs : Fin m → Om l), n ≤ N → (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ GlobalTheory.TraceConjugationCover.latL t M → ‖(F.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace - ∑ k, cs k * (((F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y) k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  intro l _ Γ _ a r m ρs t c N n cs hnN hr
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := zero_lt_one.trans hl1
  set C : ℝ := TraceConjugationCover.trBound t * ∑ k, ‖cs k‖ with hC
  have hC0 : 0 ≤ C := mul_nonneg (TraceConjugationCover.trBound_nonneg t) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt C hl1
  refine ⟨n + K, fun M hM F y hy => ?_⟩
  have hinv : ((l : ℝ)⁻¹) ^ n = ((l : ℝ) ^ n)⁻¹ := inv_pow _ _
  have hle1 : (l : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl1.le
  have hinv0 : (0 : ℝ) ≤ (l : ℝ)⁻¹ := inv_nonneg.2 hl0.le

  have hsplit : (F.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace - ∑ k, cs k * (((F.sum fun g c => zOm l c • GlobalTheory.TraceConjugationCover.tup ρs g) + y) k).trace
      = (F.sum fun h c => zOm l c * (trc r h - ∑ k, cs k * trc (ρs k) h)) - ∑ k, cs k * (y k).trace := by
    simp only [Finsupp.sum, Pi.add_apply, Finset.sum_apply, Matrix.trace_add, Matrix.trace_sum, Pi.smul_apply,
      Matrix.trace_smul, smul_eq_mul, TraceConjugationCover.tup, trc, mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, Finset.sum_comm (s := (Finset.univ : Finset (Fin m)))]
    simp only [mul_left_comm (cs _)]
    ring
  rw [hsplit]
  have h1 : ‖F.sum fun h c => zOm l c * (trc r h - ∑ k, cs k * trc (ρs k) h)‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    rw [← hinv]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hinv0 _) fun h _ => ?_
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (TraceConjugationCover.norm_zOm_le _)).trans ((hr h).trans ?_)
    exact pow_le_pow_of_le_one hinv0 hle1 (by omega)
  have h2 : ‖∑ k, cs k * (y k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    calc ‖∑ k, cs k * (y k).trace‖ ≤ ∑ k, ‖cs k‖ * (((l : ℝ)⁻¹) ^ M * TraceConjugationCover.trBound t) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (TraceConjugationCover.norm_trace_latL t M y hy k) (norm_nonneg _)
      _ = ((l : ℝ)⁻¹) ^ M * C := by rw [hC, ← Finset.sum_mul]; ring
      _ ≤ ((l : ℝ)⁻¹) ^ (n + K) * (l : ℝ) ^ K :=
          mul_le_mul (pow_le_pow_of_le_one hinv0 hle1 hM) hK.le hC0 (pow_nonneg hinv0 _)
      _ = ((l : ℝ) ^ n)⁻¹ := by
          rw [pow_add, inv_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl0.ne'), mul_one]
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rwa [norm_neg]

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleDescentToTameSubextension
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem GlobalTheory.NL.p9_statement : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), P9 D HW F := by
  intro D HW F l _ K s LL h T hT hs hl
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hp] at hl ⊢
  obtain ⟨hc, ⟨π', E', hr⟩, h1⟩ := GlobalTheory.DelParam.torsion_parameters D HW l K s LL h hs hl
  have md := GlobalTheory.T.wachLattice_deltaInvariant_basis D HW F l K s LL h T hT hs hl
  have hpos : 0 < ((HW l).W K s LL h).DelF.card :=
    Finset.card_pos.2 ⟨1, (((HW l).W K s LL h).DelF_def 1).2 ⟨1, one_pos, one_pow _⟩⟩
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt (Fact.out : l.Prime).one_lt
  refine ⟨hc, ⟨π', E', hr, md _ _ _ _ (hc ▸ hpos) hr⟩, fun he => ⟨h1 he, md _ _ _ _ hl1 (h1 he)⟩⟩
end

