module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0016
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfD
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)

theorem toLA_tmul' (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (s : ↥S) :
    toLA W T π' c S (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) := by
  simp [toLA, TensorProduct.map_tmul]

theorem smulLA_tmul' (b : LetA O n) (e : W.EE) (y : LcQ W T π' c) :
    smulLA W T π' c b (e ⊗ₜ y) = (algebraMap (LetA O n) W.EE b * e) ⊗ₜ y := by
  simp [smulLA, TensorProduct.map_tmul]

theorem smulLA_mul' (a b : LetA O n) (x : LA W T π' c) :
    smulLA W T π' c (a * b) x = smulLA W T π' c a (smulLA W T π' c b x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp [smulLA_tmul', map_mul, mul_assoc]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem eat_mem (E : ZMod n → Polynomial O) (hπ : π' ∈ W.AΔ) : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ W.AΔ := by
  intro δ hδ
  have h := hπ δ hδ
  funext i
  have hi := congrFun h i
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply] at hi ⊢
  simp only [Formalism.MainNotions.DeltaInvariantLattices.Eat]
  rw [← Polynomial.aeval_algHom_apply, hi]


open PowerSeries in
theorem filtration_value_local (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (Eπ : LetA O n) (h' : ℕ)
    (hEΔ : Eπ ∈ W.AΔ)
    (hlev : ∀ τ ζ, Pt c ζ τ → constantCoeff (W.lev c ζ Eπ) = 0)
    (hval : ∀ τ ζ, Pt c ζ τ → ∀ y ∈ NcS W T (c - 1),
      valAt W T c ζ y ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-(h' : ℤ)))
    (hanti : ∀ (τ : K →ₐ[Qp] LL) (a' a : ℤ), a' ≤ a →
      Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a') :
    (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (Eπ ^ h')) ≤ NL W T Pt π' Eπ h' c := by
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using add_mem hx hy
  | tmul a s =>
    apply Submodule.subset_span
    obtain ⟨⟨y, hy⟩, hys⟩ := Submodule.Quotient.mk_surjective _ (s : LcQ W T π' c)
    have hΛΔ : Eπ ^ h' ∈ W.AΔ := Subalgebra.pow_mem _ hEΔ h'
    let a' : Fin 1 → ↥W.AΔ := fun _ => ⟨Eπ ^ h' * Eπ ^ h' * a, Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ hΛΔ hΛΔ) a.2⟩
    let y' : Fin 1 → W.DD T := fun _ => y
    refine ⟨1, a', y', ⟨fun _ => hy, ?_⟩, ?_⟩
    · rw [Fin.sum_univ_one, toLA_tmul', smulLA_tmul', smulLA_tmul', ← map_mul, ← map_mul]
      have hm : mkL W T π' c (y' 0) hy = (s : LcQ W T π' c) := hys
      rw [hm]
      congr 2
      simp only [a']
      ring
    · intro τ ζ hpt i
      simp only [expS, Fin.sum_univ_one, serC, a', y']
      split_ifs with hi
      · by_cases hlt : i.toNat < 2 * h'
        · have hX : X ^ (2 * h') ∣ W.lev c ζ (Eπ ^ h' * Eπ ^ h' * (a : LetA O n)) := by
            have hXE : X ∣ W.lev c ζ Eπ := PowerSeries.X_dvd_iff.mpr (hlev τ ζ hpt)
            have h2 : W.lev c ζ (Eπ ^ h' * Eπ ^ h' * (a : LetA O n)) =
                W.lev c ζ Eπ ^ (2 * h') * W.lev c ζ (a : LetA O n) := by
              rw [map_mul, map_mul, map_pow, ← pow_add, two_mul]
            rw [h2]
            exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hXE _) _
          have hc : coeff i.toNat (W.lev c ζ (Eπ ^ h' * Eπ ^ h' * (a : LetA O n))) = 0 :=
            (PowerSeries.X_pow_dvd_iff.mp hX) _ hlt
          rw [hc, zero_smul]
          exact Submodule.zero_mem _
        · refine Submodule.smul_mem _ _ ?_
          refine hanti τ _ _ (by omega) (hval τ ζ hpt y hy)
      · exact Submodule.zero_mem _

theorem R_smul' {b : LetA O n} (hb : b ∈ W.AΔ) {r : LA W T π' c}
    (hr : r ∈ LinearMap.range (toLA W T π' c ⊤)) :
    smulLA W T π' c b r ∈ LinearMap.range (toLA W T π' c ⊤) := by
  obtain ⟨t, rfl⟩ := hr
  induction t using TensorProduct.inductionOn with
  | tmul a s =>
    refine ⟨(⟨b, hb⟩ * a) ⊗ₜ s, ?_⟩
    rw [toLA_tmul', toLA_tmul', smulLA_tmul', ← map_mul]
    congr 2
    simp only [Subalgebra.coe_mul]
    ring
  | add x y hx hy => simpa only [map_add] using add_mem hx hy

theorem lattice_contains_power_local (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (Eπ : LetA O n) (h' M : ℕ)
    (hEΔ : Eπ ∈ W.AΔ)
    (h4 : (LinearMap.range (toLA W T π' c ⊤)).map (smulLA W T π' c (Eπ ^ h')) ≤ NL W T Pt π' Eπ h' c) :
    JLA W T π' Eπ h' M c ≤ piNL W T Pt π' Eπ h' c M := by
  rintro _ ⟨r, hr, rfl⟩
  have hr2 := R_smul' W T π' c (Subalgebra.pow_mem _ hEΔ (2 * h')) hr
  refine ⟨smulLA W T π' c (Eπ ^ h') (smulLA W T π' c (Eπ ^ (2 * h')) r), h4 ⟨_, hr2, rfl⟩, ?_⟩
  rw [← smulLA_mul', ← smulLA_mul']
  congr 1
  rw [show 3 * h' = h' + 2 * h' by ring, pow_add]
  ring

end Local


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem val_fil (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ) (h' : ℕ)
    (hJ : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ)
    (y : ((HW l).W K 1 LL hG).DD T) (hy : y ∈ NcS ((HW l).W K 1 LL hG) T (c - 1)) :
    valAt ((HW l).W K 1 LL hG) T c ζ y ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-(h' : ℤ)) := by
  have hyL : (letE (c - 1) : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) • y = y := by
    have := hy.2
    simpa [letS, LinearMap.mem_ker, sub_eq_zero] using this
  have hφ := MLC.φD_letter' ((HW l).W K 1 LL hG) T hyL
  rw [sub_add_cancel] at hφ
  have hp4 := ((h1 l K 1 LL hG).2.2.2.1 T hT).2 c ζ τ hpt
  have key : ∀ (k : ℕ) (hz : ((HW l).W K 1 LL hG).Q ^ k • ((HW l).W K 1 LL hG).φD T y ∈
      ((HW l).W K 1 LL hG).N T),
      ((HW l).W K 1 LL hG).levN T c ζ ⟨_, hz⟩ (k : ℤ) ∈
        Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := (D.loc l).PD K) T τ (-(h' : ℤ)) := by
    intro k hz
    have h3 := hp4.2.1 ⟨_, hz⟩ (k : ℤ)
    have hsub : ((letE c : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) •
        (⟨_, hz⟩ : ↥(((HW l).W K 1 LL hG).N T))) = ⟨_, hz⟩ := by
      apply Subtype.ext
      show (letE c : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) •
          (((HW l).W K 1 LL hG).Q ^ k • ((HW l).W K 1 LL hG).φD T y) = _
      rw [smul_comm, hφ]
    rw [hsub] at h3
    exact MLC.filC_le_bot T τ h' (hJ τ) _ (Submodule.mem_inf.mp h3).2
  unfold valAt
  split_ifs with h
  · exact Submodule.smul_mem _ _ (key _ _)
  · exact Submodule.zero_mem _


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
open PowerSeries in
theorem lev_eat_zero (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) = 0 := by
  have hζ := framepf_pt_prim D HW hG c ζ τ hpt
  have hζ' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [(D.loc l).PD_p K]; exact hζ
  obtain ⟨u, hu, -⟩ := framepf_lev_q_simple ((HW l).W K 1 LL hG) c ζ hζ'
  obtain ⟨w, hw⟩ := hr.2.2.2.2.1
  have h1 := congrArg (fun f => constantCoeff (((HW l).W K 1 LL hG).lev c ζ f)) hw
  simp only [hu, map_mul, constantCoeff_X, zero_mul] at h1
  have hwu : IsUnit (constantCoeff (((HW l).W K 1 LL hG).lev c ζ (w : LetA ↥(OL LL) _))) :=
    (PowerSeries.isUnit_iff_constantCoeff).mp (w.isUnit.map _)
  exact (hwu.mul_right_eq_zero).mp h1.symm


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem model_lattice_filtration (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) (hh' : 1 ≤ h')
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (hJ : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    (LinearMap.range (toLA ((HW l).W K 1 LL hG) T π' c ⊤)).map
        (smulLA ((HW l).W K 1 LL hG) T π' c (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h')) ≤
      NL ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c :=
  filtration_value_local ((HW l).W K 1 LL hG) T π' c (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
    (eat_mem ((HW l).W K 1 LL hG) π' E hr.1)
    (fun τ ζ hpt => lev_eat_zero D HW K LL hG π' E hr c ζ τ hpt)
    (fun τ ζ hpt y hy => val_fil D HW F Cm hA.1 K LL hG T hT h' hJ π' c ζ τ hpt y hy)
    (fun τ a' a h => u3upPf_FilC_anti (PD := (D.loc l).PD K) T τ h)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem model_lattice_power (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) (hh' : 1 ≤ h')
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (hJ : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h'))
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    JLA ((HW l).W K 1 LL hG) T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c ≤
      piNL ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c (MK l K h') :=
  lattice_contains_power_local ((HW l).W K 1 LL hG) T π' c (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')
    (eat_mem ((HW l).W K 1 LL hG) π' E hr.1)
    (model_lattice_filtration D HW F Cm CA CB CK hA l hl K LL hG π' E hr h' hh' T hT hJ c)

end Formalism.MainNotions.N.Ln34.MLD

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfE
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLE

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem exists_fin_sum {O M N' : Type*} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N']
    [Module O N'] (t : M ⊗[O] N') : ∃ (m : ℕ) (a : Fin m → M) (s : Fin m → N'), t = ∑ j, a j ⊗ₜ s j := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a s => exact ⟨1, fun _ => a, fun _ => s, by simp⟩
  | add t t' ht ht' =>
    obtain ⟨m, a, s, rfl⟩ := ht
    obtain ⟨m', a', s', rfl⟩ := ht'
    refine ⟨m + m', Fin.append a a', Fin.append s s', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem toLA_tmul (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (s : ↥S) :
    toLA W T π' c S (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) :=
  rfl

theorem smulLA_tmul (a : LetA O n) (e : W.EE) (s : LcQ W T π' c) :
    smulLA W T π' c a (e ⊗ₜ s) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ s := rfl

theorem smulLA_smulLA (a b : LetA O n) (x : LA W T π' c) :
    smulLA W T π' c a (smulLA W T π' c b x) = smulLA W T π' c (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e s => simp only [smulLA_tmul, map_mul, mul_assoc]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem smul_eq_smulLA (o : O) (x : LA W T π' c) :
    o • x = smulLA W T π' c (algebraMap O (LetA O n) o) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e s =>
    rw [smulLA_tmul, TensorProduct.smul_tmul', Algebra.smul_def,
      IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy]

theorem rep_exists {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨m, a, s, rfl⟩ := exists_fin_sum t
  have hs : ∀ j, ∃ yy : ↥(NcS W T (c - 1)), Submodule.Quotient.mk yy = ((s j : ↥(⊤ : Submodule O _)) :
      LcQ W T π' c) := fun j => Submodule.Quotient.mk_surjective _ _
  choose yy hyy using hs
  refine ⟨m, a, fun j => (yy j : W.DD T), ⟨fun j => (yy j).2, ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← ht, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [toLA_tmul, ← hyy j]
  rfl

theorem rep_append {x x' : LA W T π' c} {m m' : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    {a' : Fin m' → ↥W.AΔ} {y' : Fin m' → W.DD T} (h : IsRepL W T π' Eπ h' c x a y)
    (h₂ : IsRepL W T π' Eπ h' c x' a' y') :
    IsRepL W T π' Eπ h' c (x + x') (Fin.append a a') (Fin.append y y') := by
  obtain ⟨hy, hx⟩ := h
  obtain ⟨hy', hx'⟩ := h₂
  refine ⟨fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact hy j
    · rw [Fin.append_right]; exact hy' j
  · rw [map_add (f := _), hx, hx', Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.append_left]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.append_right]

theorem expS_append (ζ : LL) {m m' : ℕ} (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T)
    (a' : Fin m' → ↥W.AΔ) (y' : Fin m' → W.DD T) :
    expS W T c ζ (fun j => ((Fin.append a a' j : ↥W.AΔ) : LetA O n)) (Fin.append y y') =
      expS W T c ζ (fun j => (a j : LetA O n)) y + expS W T c ζ (fun j => (a' j : LetA O n)) y' := by
  funext i
  simp only [expS, Pi.add_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem rep_smul {x : LA W T π' c} {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    (h : IsRepL W T π' Eπ h' c x a y) {b : LetA O n} (hb : b ∈ W.AΔ) :
    IsRepL W T π' Eπ h' c (smulLA W T π' c b x) (fun j => ⟨b * a j, W.AΔ.mul_mem hb (a j).2⟩) y := by
  obtain ⟨hy, hx⟩ := h
  refine ⟨hy, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [smulLA_smulLA, mul_comm, ← smulLA_smulLA, hx, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smulLA_tmul, ← map_mul]
  congr 2
  ring

end Generic

end Formalism.MainNotions.N.Ln34.MLE

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPf
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

set_option maxHeartbeats 1000000 in
theorem modelqlink_pf : ModelQLinkStep := by
  intro D HW F Cm CA CB CK hA hML l hpf hl K LL hG π' E hR h' hh' T hT hJ c
  have hL := hML l hl K LL hG π' E hR h' hh' T hT hJ c
  obtain ⟨hL1, -, -, hL4, hL5, -, -⟩ := hL
  have h1 : adm1 D HW F Cm := hA.1
  have hs : 1 ≤ sK l K := by
    have := frobpin_sK_pos hl K LL hG
    omega
  obtain ⟨-, -, -, -, -, -, -, -, hπu, hπΔ, -⟩ := gradNPf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT hs
  obtain ⟨w₁, hw₁⟩ := hR.2.2.1
  obtain ⟨w₂, hw₂⟩ := hR.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨hcard, -, -⟩ := h9W T hT hs1 hp
  obtain ⟨-, ⟨π'₀, E₀, -, hm₀⟩, -⟩ := h9W T hT hs1 hp
  obtain ⟨r, b, hbΔ, hbu, hbe⟩ := hm₀.1
  haveI hdvr : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  obtain ⟨bL⟩ := MQ.basis_L ((HW l).W K 1 LL hG) T π' (sK l K) hs w₁ hw₁ hR.2.1 b hbΔ hbu hbe c
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hcpos : 0 < ((HW l).W K 1 LL hG).DelF.card := by
    refine Finset.card_pos.2 ⟨1, ((HW l).W K 1 LL hG).DelF_def 1 |>.2 ⟨1, one_pos, one_pow _⟩⟩
  have hclt : ((HW l).W K 1 LL hG).DelF.card < l := by
    rw [hcard, hpl]
    have := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hΔu : IsUnit ((((HW l).W K 1 LL hG).DelF.card : ℕ) : ↥(OL LL)) :=
    gradNPf_unit_nat ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hpf.out hlv _
      (Nat.not_dvd_of_pos_of_lt hcpos hclt)
  have hpP : ((D.loc l).PD K).p.Prime := by rw [hpl]; exact hpf.out
  haveI hcompl : IsAdicComplete (Ideal.span {(((D.loc l).PD K).p : ↥(OL LL))}) ↥(OL LL) := by
    rw [hpl]; exact FrobeniusSpanLemma.phib_OL_complete LL
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    show ∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π'
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply,
      show ((HW l).W K 1 LL hG).γ₀ δ (π' i) = π' i from congrFun (hπΔ δ hδ) i]
  have hEe : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' = ((w₂⁻¹ : (LetA ↥(OL LL) _)ˣ) : LetA ↥(OL LL) _) * ((HW l).W K 1 LL hG).q := by
    rw [hw₂, ← mul_assoc, Units.inv_mul, one_mul]
  have hEu : IsUnit (algebraMap _ ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
    rw [hEe, map_mul]
    exact ((w₂⁻¹).isUnit.map _).mul (MQ.q_unit ((HW l).W K 1 LL hG) hpP)
  obtain ⟨D', S, hdiv⟩ := MQ.div_at ((HW l).W K 1 LL hG) hpP (sK l K) h' π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') w₁ w₂ hw₁ hw₂
    hΔu.unit hΔu.unit_spec hR.1 hEΔ c
  have hp0 : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := by
    intro h0
    have : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (((D.loc l).PD K).p : ↥(OL LL))) = 1 := by
      rw [map_natCast, hpl]; exact hlv
    rw [h0, map_zero, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  have hpu : ¬ IsUnit (((D.loc l).PD K).p : ↥(OL LL)) := by
    intro hU
    obtain ⟨bb, hbb⟩ := hU.exists_right_inv
    have e := congrArg (fun z => (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 z)) hbb
    simp only [map_mul, map_one, AddValuation.map_mul, AddValuation.map_one] at e
    rw [map_natCast, hpl, hlv] at e
    have hb0 : 0 ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 bb) := (hRv _).2 ⟨bb, rfl⟩
    revert e hb0
    generalize (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 bb) = z
    intro e hb0
    induction z using WithTop.recTopCoe with
    | top => simp at e
    | coe q =>
      have e' : (1 + q : ℚ) = 0 := by exact_mod_cast e
      have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hb0
      linarith
  refine ⟨MQ.finite_of (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c hEu hL4
    (MQ.finite_L ((HW l).W K 1 LL hG) T π' (sK l K) hs w₁ hw₁ hR.2.1 b hbΔ hbu hbe c) D' S hdiv, ?_⟩
  exact MQ.tf_of (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' c hπu hL1 hL5
    (MQ.sat_of π' c bL (MQ.hlet_of ((HW l).W K 1 LL hG) (sK l K) hs π' w₁ hw₁ hR.1 hπu c))
    (MQ.dvd_pow_of_dvr _ hp0 hpu)

end Formalism.MainNotions.N.Ln34
end
end

