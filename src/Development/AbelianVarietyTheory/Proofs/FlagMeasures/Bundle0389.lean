module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemGenusIffMaximalIntegralHermitianLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalPairingClassStableUnitriangularChange
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ClsStable

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E]

theorem h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (y : V) : H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := H.h_smul_left 0 0 y
    simpa using this
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H.h_add_left, ih]

theorem h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (x : V) : H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← H.h_herm]

theorem zhat_chg {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ)
    (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hg : GlobalTheory.LocOver.Chg f A g) (hg' : GlobalTheory.LocOver.Chg f' A' g') :
    H.Zhat g g' = A.transpose.map M.L.cj * H.Zhat f f' * A' := by
  ext a b
  simp only [Loc.HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [hg a, hg' b, h_sum_left]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [H.h_smul_left, h_sum_right, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h_smul_right]
  ring

theorem intUni_mul {M : Loc.Model F E} {r : ℕ} {B A : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hB : IntUni M B) (hA : IntUni M A) : IntUni M (B * A) := by
  refine ⟨fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hB.1 a c h, zero_mul]
    · rw [hA.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hB.2.1, hA.2.1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hB.1 a c h, zero_mul]
      · rw [hA.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (hB.2.2 a c) (hA.2.2 c b)

theorem span_mul_mem {M : Loc.Model F E} {t x o : E} (hx : x ∈ Submodule.span M.L.O {t}) (ho : o ∈ M.L.O) :
    x * o ∈ Submodule.span M.L.O {t} ∧ o * x ∈ Submodule.span M.L.O {t} := by
  have h1 : (⟨o, ho⟩ : M.L.O) • x ∈ Submodule.span M.L.O {t} := Submodule.smul_mem _ _ hx
  have h2 : (⟨o, ho⟩ : M.L.O) • x = o * x := rfl
  rw [h2] at h1
  exact ⟨by rw [mul_comm]; exact h1, h1⟩

theorem zhat_mem_clsLoc_of_chg : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) → Chg f A g → Chg f' A' g' → H.Zhat f f' ∈ clsLoc M Y0 → H.Zhat g g' ∈ clsLoc M Y0 := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Y0 f f' g g' A A' hA hA' hint hg hg' hY
  obtain ⟨B, B', hB, hB', hBB, hZ⟩ := hY
  have hIA : IntUni M A := ⟨hA.1, hA.2, fun a b => (hint a b).1⟩
  have hIA' : IntUni M A' := ⟨hA'.1, hA'.2, fun a b => (hint a b).2.1⟩
  refine ⟨B * A, B' * A', intUni_mul hB hIA, intUni_mul hB' hIA', fun a b => ?_, ?_⟩
  · have e : (B * A) a b - (B' * A') a b =
        ∑ c, (B a c - B' a c) * A c b + ∑ c, B' a c * (A c b - A' c b) := by
      simp only [Matrix.mul_apply, ← Finset.sum_add_distrib]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_) (Submodule.sum_mem _ fun c _ => ?_)
    · exact (span_mul_mem (hBB a c) (hIA.2.2 c b)).1
    · exact (span_mul_mem (hint c b).2.2 (hB'.2.2 a c)).2
  · rw [zhat_chg H r f f' g g' A A' hg hg', hZ, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ClsStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusCyclicDiscriminantSplitPrime
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.CyclicDisc

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem nondeg_of_pd (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra hne
    have := hp τ x hne
    rw [hx x] at this
    simp at this
  · by_contra hne
    have := hp τ x hne
    rw [hx x] at this
    simp at this

omit [IsScalarTower (𝓞 K) K V] in
theorem pd_of_ortho (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (I : Submodule (𝓞 K) V) (n : ℕ)
    (hI : IsOrthoLattice h I n) : PD h := by
  obtain ⟨e, -, hsp, -, he⟩ := hI
  intro τ x hx
  have hx' : x ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx'
  have hc : ∃ i, c i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (by simp [hn])
  have e1 : h (∑ i, c i • e i) (∑ i, c i • e i) = ∑ i, star (c i) * c i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, he,
      smul_eq_mul, RingHom.id_apply, starRingEnd_apply]
    simp [mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum, Complex.re_sum]
  have e2 : ∀ i, (τ (star (c i) * c i)).re = Complex.normSq (τ (c i)) := fun i => by
    rw [map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  simp only [e2]
  obtain ⟨i, hi⟩ := hc
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 ((map_ne_zero τ).2 hi)⟩

omit [NumberField K] in
theorem star_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := by
  have : IsIntegral ℤ (starRingEnd K (algebraMap (𝓞 K) K r)) :=
    map_isIntegral_int _ (RingOfIntegers.isIntegral_coe r)
  exact ⟨⟨_, this⟩, rfl⟩

def Over (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L M : Submodule (𝓞 K) V) : Prop :=
  Submodule.IsLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧
    Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓))

omit [NumberField K] in
theorem over_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L M : Submodule (𝓞 K) V)
    (H : Over h 𝔓 L M) : Over h 𝔓 (g • L) (g • M) := by
  obtain ⟨h1, h2, h3, ⟨e⟩⟩ := H
  have A := final_isomAct (𝓞 K) K V h g.1 g.2 M
  refine ⟨A.2.2.2.2.2 h1, A.2.2.2.1.2 h2, Submodule.map_mono h3, ⟨?_⟩⟩
  let g' : V ≃ₗ[𝓞 K] V := (g : V ≃ₗ[K] V).restrictScalars (𝓞 K)
  let f : M ≃ₗ[𝓞 K] ↥(g • M) := g'.submoduleMap M
  refine (Submodule.Quotient.equiv _ _ f ?_).symm.trans e
  ext ⟨x, hx⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y.1, hy, congrArg Subtype.val hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, h3 hy⟩, hy, Subtype.ext hxy⟩


noncomputable def up (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L : Submodule (𝓞 K) V) :
    Submodule (𝓞 K) V := sSup {M | Over h 𝔓 L M}

omit [NumberField K] in
theorem up_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (g : isom h) (L : Submodule (𝓞 K) V) :
    up h 𝔓 (g • L) = g • up h 𝔓 L := by
  have key : ∀ (g : isom h) (L : Submodule (𝓞 K) V), g • up h 𝔓 L ≤ up h 𝔓 (g • L) := by
    intro g L
    change Submodule.map _ _ ≤ _
    rw [Submodule.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Submodule.map_le_iff_le_comap]
    exact le_sSup (over_smul h 𝔓 g L M hM)
  refine le_antisymm ?_ (key g L)
  have h1 := key g⁻¹ (g • L)
  rw [inv_smul_smul] at h1
  have h2 : g • g⁻¹ • up h 𝔓 (g • L) ≤ g • up h 𝔓 L := Submodule.map_mono h1
  rwa [smul_inv_smul] at h2

omit [NumberField K] in
theorem up_eq (h : V →ₗ⋆[K] V →ₗ[K] K) (𝔓 : Ideal (𝓞 K)) (L M : Submodule (𝓞 K) V)
    (hu : ∃! M, Over h 𝔓 L M) (hM : Over h 𝔓 L M) : up h 𝔓 L = M := by
  have : {M | Over h 𝔓 L M} = {M} := by
    ext N
    exact ⟨fun hN => hu.unique hN hM, fun hN => by rw [Set.mem_singleton_iff.1 hN]; exact hM⟩
  rw [up, this, sSup_singleton]

end

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ T : ℕ, T.Prime → (∀ P : Ideal (𝓞 K), P.IsMaximal → (T : 𝓞 K) ∈ P → Ideal.absNorm P = T ∧ (T : 𝓞 K) ∉ P ^ 2) → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ Ideal.span {(T : 𝓞 K)})) → mass h L = mass h' I * (((T : ℝ) ^ Module.finrank K V - 1) / ((T : ℝ) - 1)) ^ fDeg K := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hn V' _ _ _ _ _ h' hs' I hI T hT hsp L hL hLq
  have hnd := nondeg_of_pd h hp
  have hp' := pd_of_ortho hK h' I _ hI
  have hnd' := nondeg_of_pd h' hp'
  obtain ⟨⟨s, hcard, hsP, hcop, hprod⟩, hgen⟩ := GlobalTheory.T.cyclicDiscriminant_lattices_form_one_genus K V h hK hs hnd T hT hsp
  have hT0 : (T : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hP0 : (∏ P ∈ s, P) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hprod
    exact hT0 hprod
  obtain ⟨o1, o2⟩ := GlobalTheory.T.exists_unimodular_overlattice_cyclic_split_discriminant K V h hK hs hnd _ hP0 hcop
  rw [hprod] at o1 o2
  have hex : ∀ N ∈ genus h L, ∃! M, Over h (∏ P ∈ s, P) N M := by
    intro N hN
    obtain ⟨M, hM, hu⟩ := o1 N ((hgen L N hL hLq).1 hN).1 ((hgen L N hL hLq).1 hN).2
    refine ⟨M, ⟨hM.1.toIsLattice, hM.2⟩, ?_⟩
    intro M' hM'
    letI := hN.1
    letI := hM'.1
    exact hu M' ⟨Submodule.IsFullLattice.of_le K hM'.2.2.1, hM'.2⟩
  obtain ⟨M0, hM0, -⟩ := o1 L hL hLq
  have hM0full : Submodule.IsFullLattice K M0 := by
    letI := hL.1
    letI := hM0.1
    exact Submodule.IsFullLattice.of_le K hM0.2.2.1
  obtain ⟨-, m2, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨-, m2', m3'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨c, hc⟩ := hMM K hK _ hn
  obtain ⟨iL, iU, iR⟩ := m3' I _ hI
  have iLfull : Submodule.IsFullLattice K I := by
    obtain ⟨e, -, he, hIeq, -⟩ := hI
    refine { toIsLattice := iL, span_eq_top := ?_ }
    rw [hIeq, Submodule.span_span_of_tower (𝓞 K), he]
  have e0 : mass h M0 = mass h' I := by
    rw [hc V h hs hp rfl M0 (m2 M0 hM0.1 hM0.2.1).1, (m2 M0 hM0.1 hM0.2.1).2.2,
      hc V' h' hs' hp' iR I (m2' I iLfull iU).1, (m2' I iLfull iU).2.2]
  obtain ⟨b1, b2, b3, b4, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp L hL.1
  obtain ⟨a1, a2, a3, -, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M0 hM0full
  have hmaps : Set.MapsTo (up h (∏ P ∈ s, P)) (genus h L) (genus h M0) := by
    intro N hN
    obtain ⟨M, hM, -⟩ := hex N hN
    rw [up_eq h _ N M (hex N hN) hM]
    exact (_root_.GlobalTheory.Mass.MaxGenus.main K V h hK hs hp M0 M (m2 M0 hM0.1 hM0.2.1).1).2 (m2 M (by
      letI := hN.1
      letI := hM.1
      exact Submodule.IsFullLattice.of_le K hM.2.2.1) hM.2.1).1
  have hfib := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ (genus h L) (genus h M0) (up h (∏ P ∈ s, P))
    (up_smul h _) b3 a3 hmaps (fun y hy => b4 y hy.1)
  set B : ℕ := (∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card with hB
  have hconst : ∀ M ∈ genus h M0,
      ((((genus h L) ∩ (up h (∏ P ∈ s, P)) ⁻¹' {M}).encard : ℕ∞) : ℝ≥0∞) = (B : ℝ≥0∞) := by
    intro M hM
    have hU : IsUnimodular h M :=
      (((final_genusBasic (𝓞 K) K V h hs star_mem_range).2.2 M0 M hM0.1.fg hM.1.fg hM.2).1).1 hM0.2.1
    have hset : (genus h L) ∩ (up h (∏ P ∈ s, P)) ⁻¹' {M} = {N : Submodule (𝓞 K) V | N ≤ M ∧
        Nonempty ((↥M ⧸ N.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))} := by
      ext N
      constructor
      · rintro ⟨hN, hNM⟩
        obtain ⟨M1, hM1, -⟩ := hex N hN
        have : M1 = M := (up_eq h _ N M1 (hex N hN) hM1).symm.trans hNM
        subst this
        exact hM1.2.2
      · rintro ⟨h1, h2⟩
        have hN : N ∈ genus h L := (hgen L N hL hLq).2 (o2 M N hM.1 hU h1 h2)
        exact ⟨hN, up_eq h _ N M (hex N hN) ⟨hM.1.toIsLattice, hU, h1, h2⟩⟩
    rw [hset, GlobalTheory.T.card_sublattices_quotient_prod_degree_one_primes K V M hM.1 T s hT hsP]
    exact ENat.toENNReal_coe _
  obtain ⟨p1, p2, -⟩ := _root_.GlobalTheory.Mass.OrbMono.main (isom h) (Submodule (𝓞 K) V)
  have hsum : orbMass (isom h) (genus h L) = (B : ℝ≥0∞) * orbMass (isom h) (genus h M0) := by
    rw [hfib, ← p2]
    exact le_antisymm (p1 _ _ _ _ subset_rfl fun x hx => (hconst x hx).le)
      (p1 _ _ _ _ subset_rfl fun x hx => (hconst x hx).ge)
  rw [← b1, ← a1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff b2.le (by positivity)] at hsum
  have hT1 : (T : ℝ) ≠ 1 := by exact_mod_cast hT.one_lt.ne'
  rw [hsum, e0, hB, hcard, mul_comm, ← geom_sum_eq hT1]
  push_cast
  rfl

end GlobalTheory.Mass.CyclicDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassIntegralLatticesDiscriminantOrderLe
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.SpaceMass

theorem nondeg_of_PD {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this
  · by_contra h0
    have := hp τ x h0
    rw [hx x] at this
    simp at this

theorem PD_of_ortho {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (I : Submodule (𝓞 K) V) (n : ℕ)
    (hI : IsOrthoLattice h I n) : PD h := by
  obtain ⟨e, -, hsp, -, hort⟩ := hI
  intro τ x hx
  have hx' : x ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx'
  have e1 : h (∑ i, a i • e i) (∑ i, a i • e i) = ∑ i, star (a i) * a i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      hort, smul_eq_mul, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  have e2 : (τ (∑ i, star (a i) * a i)).re = ∑ i, Complex.normSq (τ (a i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hK.2.1, Complex.normSq_eq_conj_mul_self.symm]
    simp
  rw [e1, e2]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx (by simp [hc])
  refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
  exact Complex.normSq_pos.2 ((map_ne_zero τ).2 hi)

theorem mem_genus_self {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V)
    (hM : Submodule.IsFullLattice K M) : M ∈ genus h M := by
  refine ⟨hM, fun p _ => ⟨1, (isom h).one_mem, ?_⟩⟩
  exact one_smul (isom h) (loc (K := K) p M)

theorem real_bound (n' i : ℕ) (j l c m : ℝ) (hn : 1 ≤ n') (hl : 0 ≤ l) (hc : 0 ≤ c)
    (hm : m ≤ c * (n' : ℝ) ^ (j / 2)) :
    (i : ℝ) ^ (j + l) * m ≤ c * ((n' * i ^ 2 : ℕ) : ℝ) ^ ((j + l) / 2) := by
  have h1 : (n' : ℝ) ^ (j / 2) ≤ (n' : ℝ) ^ ((j + l) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  have h2 : ((n' * i ^ 2 : ℕ) : ℝ) ^ ((j + l) / 2) = (n' : ℝ) ^ ((j + l) / 2) * (i : ℝ) ^ (j + l) := by
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 2
    push_cast
    ring
  have h3 : (0 : ℝ) ≤ (i : ℝ) ^ (j + l) := by positivity
  rw [h2]
  calc (i : ℝ) ^ (j + l) * m ≤ (i : ℝ) ^ (j + l) * (c * (n' : ℝ) ^ ((j + l) / 2)) :=
        mul_le_mul_of_nonneg_left (hm.trans (mul_le_mul_of_nonneg_left h1 hc)) h3
    _ = _ := by ring

theorem main : MaxMass → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → 1 ≤ Module.finrank K V → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → ∀ I : Submodule (𝓞 K) V', IsOrthoLattice h' I (Module.finrank K V) → ∀ n : ℕ, 1 ≤ n → orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ ENNReal.ofReal (mass h' I * (n : ℝ) ^ (((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K)) / 2)) := by
  intro hMM K V _ _ _ _ _ _ _ _ h hK hs hp hj V' _ _ _ _ _ h' hs' I hI n hn
  have hnd := nondeg_of_PD h hp
  have hp' := PD_of_ortho h' hK I _ hI
  have hnd' := nondeg_of_PD h' hp'
  rcases (latsDisc (R := 𝓞 K) h n).eq_empty_or_nonempty with hE | ⟨M₁, hM₁⟩
  · rw [hE]
    unfold orbMass orbSum
    refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun q => q.2.elim) zero_le
  obtain ⟨hex, -, -⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V h hK hs hnd
  obtain ⟨M₀, hM₀, hle₀⟩ := hex M₁ hM₁.1

  obtain ⟨c, hc⟩ := hMM K hK _ hj
  obtain ⟨-, hu', ho'⟩ := GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal K V' h' hK hs' hnd'
  obtain ⟨hIl, hIu, hIr⟩ := ho' I _ hI
  have hIfull : Submodule.IsFullLattice K I := by
    refine { toIsLattice := hIl, span_eq_top := ?_ }
    obtain ⟨e, -, hspan, rfl, -⟩ := hI
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨hImax, -, hIlam⟩ := hu' I hIfull hIu
  have hcI : mass h' I = c := by rw [hc V' h' hs' hp' hIr I hImax, hIlam, mul_one]
  have hcpos : 0 < c := hcI ▸ (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V' h' hK hs' hp' I hIfull).2.1
  have hdisc := GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs hnd
  obtain ⟨hmass, hmpos, hYst, hfin, -⟩ := GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M₀ hM₀.1.1
  obtain ⟨hi0, hn₀⟩ := (hdisc M₁ hM₁.1).2.2.1 M₀ hM₀.1 hle₀
  have hn'0 := (hdisc M₀ hM₀.1).1
  set n' := discN h M₀ with hn'
  set i := idxN M₀ M₁ with hi
  have hnn : n = n' * i ^ 2 := hM₁.2 ▸ hn₀
  have hm₀ : mass h M₀ ≤ c * (n' : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
    rw [hc V h hs hp rfl M₀ hM₀]
    exact mul_le_mul_of_nonneg_left (_root_.GlobalTheory.MaxLatLam.main K V h hK hs hnd hj M₀ hM₀).2 hcpos.le
  have hDst : Stable (isom h) (latsDisc (R := 𝓞 K) h n) := by
    intro g M hM
    have h1 := (GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass K V h hK hs hp M hM.1.1).2.2.1 g M (mem_genus_self h M hM.1.1)
    have h2 := (hdisc M hM.1).2.2.2.1 _ h1
    exact ⟨h2.1, h2.2.trans hM.2⟩
  let X : Set (Submodule (𝓞 K) V × Submodule (𝓞 K) V) :=
    {p | p.1 ∈ latsDisc (R := 𝓞 K) h n ∧ p.2 ∈ genus h M₀ ∧ p.1 ≤ p.2}
  have hXst : Stable (isom h) X := by
    rintro g p ⟨h1, h2, h3⟩
    exact ⟨hDst g _ h1, hYst g _ h2, Submodule.map_mono h3⟩
  have f1 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (latsDisc (R := 𝓞 K) h n) Prod.fst (fun _ _ => rfl) hXst hDst
    (fun p hp => hp.1) (fun y hy => hfin y hy.1.1)
  have f2 := GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres (isom h) _ _ X (genus h M₀) Prod.snd (fun _ _ => rfl) hXst hYst
    (fun p hp => hp.2.1) (fun y hy => hfin y hy.1)
  obtain ⟨mono, hconst, -⟩ := _root_.GlobalTheory.Mass.OrbMono.main (isom h) (Submodule (𝓞 K) V)
  have s1 : orbMass (isom h) (latsDisc (R := 𝓞 K) h n) ≤ orbMass (isom h) X := by
    rw [f1]
    refine mono _ _ _ _ subset_rfl fun M hM => ?_
    obtain ⟨M', hM', hle⟩ := hex M hM.1
    have hne : (X ∩ Prod.fst ⁻¹' {M}).Nonempty :=
      ⟨(M, M'), ⟨hM, (_root_.GlobalTheory.Mass.MaxGenus.main K V h hK hs hp M₀ M' hM₀).2 hM', hle⟩, rfl⟩
    have := Set.one_le_encard_iff_nonempty.2 hne
    exact_mod_cast this
  have s2 : orbMass (isom h) X ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) +
      Real.logb 2 (Module.finrank ℚ K))) * orbMass (isom h) (genus h M₀) := by
    rw [f2, ← hconst]
    refine mono _ _ _ _ subset_rfl fun M' hM' => ?_
    refine le_trans ?_ (_root_.GlobalTheory.Mass.sublattice_count K V h hK hs hnd M' hM'.1.toIsLattice i (Nat.one_le_iff_ne_zero.2 hi0))
    have hM'' := (hdisc M₀ hM₀.1).2.2.2.1 M' hM'
    have : (X ∩ Prod.snd ⁻¹' {M'}).encard ≤
        {N : Submodule (𝓞 K) V | N ≤ M' ∧ idxN M' N = i}.encard := by
      refine Set.encard_le_encard_of_injOn (f := Prod.fst) ?_ ?_
      · rintro ⟨N, N'⟩ ⟨⟨h1, -, h3⟩, h4⟩
        obtain rfl : N' = M' := h4
        refine ⟨h3, ?_⟩
        have h5 := ((hdisc N h1.1).2.2.1 N' hM''.1 h3).2
        rw [h1.2, hM''.2, hnn] at h5
        have h6 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn'0) h5
        exact ((Nat.pow_left_injective (by norm_num)) h6).symm
      · rintro ⟨N, N'⟩ ⟨-, h4⟩ ⟨P, P'⟩ ⟨-, h5⟩ h6
        obtain rfl : N' = M' := h4
        obtain rfl : P' = N' := h5
        obtain rfl : N = P := h6
        rfl
    exact_mod_cast this
  refine s1.trans (s2.trans ?_)
  rw [← hmass, ← ENNReal.ofReal_mul (by positivity), hcI, hnn]
  refine ENNReal.ofReal_le_ofReal (real_bound n' i _ _ c _ (Nat.one_le_iff_ne_zero.2 hn'0) ?_ hcpos.le hm₀)
  refine Real.logb_nonneg (by norm_num) ?_
  exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)

end GlobalTheory.Mass.SpaceMass
end

