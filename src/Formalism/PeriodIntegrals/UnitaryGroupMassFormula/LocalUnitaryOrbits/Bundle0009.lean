module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0008

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight
section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem b_fg : (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)).FG := by
  let b := RingOfIntegers.basis E
  have h : Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) =
      Submodule.span (v.adicCompletionIntegers F)
        (Set.range fun i => inclR (F := F) (Fv F v) ((b i : 𝓞 E) : E)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      have hx : ((x : 𝓞 E) : E) = ∑ i, (b.repr x i) • ((b i : 𝓞 E) : E) := by
        have := congrArg (fun y : 𝓞 E => (y : E)) (b.sum_repr x)
        simpa using this.symm
      simp only
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨_, Set.mem_univ _, rfl⟩
  rw [h]
  exact Submodule.fg_span (Set.finite_range _)

def bAlg : Subalgebra (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.toSubalgebra (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)) (b_one_mem (E := E) v)
    (fun _ _ hx hy => b_mul_mem v hx hy)

theorem b_int_of_sc {a : Fv F v} (ha : sc (E := E) v a ∈ OEv (E := E) v) : a ∈ v.adicCompletionIntegers F := by
  have hfg : (Subalgebra.toSubmodule (bAlg (E := E) v)).FG := b_fg v
  have hi : IsIntegral (v.adicCompletionIntegers F) (sc (E := E) v a) :=
    IsIntegral.of_mem_of_fg (bAlg (E := E) v) hfg _ ha
  let f : Fv F v →ₐ[v.adicCompletionIntegers F] Fv F v ⊗[F] E :=
    (Algebra.ofId (Fv F v) (Fv F v ⊗[F] E)).restrictScalars (v.adicCompletionIntegers F)
  have hfa : f a = sc (E := E) v a := by rw [b_sc_eq]; rfl
  rw [← hfa] at hi
  have hi' := (isIntegral_algHom_iff f (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 hi
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi'
  rw [← hy]
  exact y.2

theorem b_sigR_mem (σ : E →ₐ[F] E) {z : Fv F v ⊗[F] E} (hz : z ∈ OEv (E := E) v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z ∈ OEv (E := E) v := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, -, rfl⟩ := hx
    have hb : IsIntegral ℤ (σ (b : E)) := by
      simpa using (b.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (inclR (F := F) (Fv F v) (b : E)) =
        inclR (F := F) (Fv F v) ((⟨σ (b : E), hb⟩ : 𝓞 E) : E) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]
    rw [e]
    exact b_inclR_mem (F := F) (E := E) v ⟨σ (b : E), hb⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    have h1 : r • x = algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * x := by
      rw [← Algebra.smul_def]; rfl
    have h2 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x =
        r • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x := by
      rw [← Algebra.smul_def]; rfl
    have h3 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]
    rw [h1, map_mul, h3, h2]
    exact Submodule.smul_mem _ r hx

theorem b_tr_sc (s : Fv F v) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sc (E := E) v s * w) =
      s * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  rw [b_sc_eq, ← Algebra.smul_def, map_smul, smul_eq_mul]

end Int

section DualW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem b_hR_smul_right (x y : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem b_hR_smul_left (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem b_hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

theorem b_smulF (s : Fv F v) (y : Fin n → Fv F v ⊗[F] E) : s • y = sc (E := E) v s • y := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def]
  rfl

theorem b_BR_smul_right {a : ℕ} (s : Fv F v) (X Y : TupV (E := E) v n a) :
    BR (Fv F v) σ J X (s • Y) = s * BR (Fv F v) σ J X Y := by
  simp only [BR, Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [b_smulF v s (Y i), b_hR_smul_right, b_tr_sc]

theorem b_BR_single {a : ℕ} (i : Fin a) (u : Fin n → Fv F v ⊗[F] E) (Y : TupV (E := E) v n a) :
    BR (Fv F v) σ J (Pi.single i u) Y =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J u (Y i)) := by
  classical
  rw [BR, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, b_hR_zero_left, map_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
theorem dualW_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : DualW σ J ψ v Λ a := by
  classical
  rintro hS ⟨L, hLat, rfl⟩ hSD hU
  have hd0 := dV_ne_zero v
  have hinv : ∀ y, σ (σ y) = y := b_sig_sig σ hS.1
  ext Y
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]
  constructor
  · intro h
    refine ⟨dV v • Y, fun i => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩
    refine (hSD _).2 fun x hx => hP hS hU _ fun c hc => ?_
    have hcx : Pi.single i (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c • x) ∈ LamT v (L : Set (Fin n → E)) a := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same]
        exact b_lat_smul v L (b_sigR_mem v σ hc) hx
      · rw [Pi.single_eq_of_ne hj]
        exact Submodule.zero_mem _
    have h1 := h _ hcx
    rw [b_BR_single, b_hR_smul_left, sigR_sigR v σ hinv] at h1
    rw [Pi.smul_apply, b_smulF v, b_hR_smul_right, mul_left_comm, b_tr_sc]
    exact h1
  · rintro ⟨X', hX', rfl⟩ X hX
    rw [b_BR_smul_right, ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    exact sum_mem fun i _ => b_trace_mem v ((hSD _).1 (hX' i) _ (hX i))

end DualW

end PI.OmLocU.SdB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.LatBasOHolds
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem exists_basO (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsFullLattice E L) :
    ∃ (m : ℕ) (b : Fin m → Fin n → Fv F v ⊗[F] E), LinearIndependent (Fv F v) b ∧
      (∀ x, x ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        ∃ c : Fin m → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i) ∧
      ⊤ ≤ Submodule.span (Fv F v) (Set.range b) := by
  classical
  set M := latLoc (E := E) v (L : Set (Fin n → E)) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (basLat_fg v L hLat.toIsLattice)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fin n → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  refine ⟨_, b0, hli, hmem, ?_⟩
  rw [← basSpan_top v L hLat, Submodule.span_le]
  intro x hx
  obtain ⟨c, rfl⟩ := (hmem x).1 hx
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem latBasO_holds
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (a : ℕ) (Y : TupV (E := E) v n a) : LatBasO σ J ψ v Λ a Y := by
  classical
  rintro ⟨⟨hCM, -⟩, -, -⟩
  obtain ⟨L, hLat, rfl⟩ := hFull
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hCM.2.2.1
  obtain ⟨m, b, hli, hmem, hsp⟩ := exists_basO v L hLat
  have hm : m = 2 * n := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  subst hm
  exact ⟨b, hli, hmem⟩

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NearTIff
section
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem nearT_iff (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} {K : Type} [CommRing K] {τ : K →+* K} {π : OR (E := E) v →+* K} (hπ : IsRes σ v ϖ τ π)
    {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : ∀ i j, T i j ∈ OR (E := E) v) (X : lamA v Λ a) :
    (X : TupV (E := E) v n a) ∈ NearT v σ J ϖ T ↔
      ffGram τ 1 (phi σ J v Λ hSD he π a X) = fun i j => π ⟨T i j, hT i j⟩ := by
  have hg : ∀ i j, gramR (Fv F v) σ J (X : TupV (E := E) v n a) i j ∈ OR (E := E) v := fun i j =>
    (hSD _).1 (memA v Λ X j) _ (memA v Λ X i)
  have hconj : ∀ i p, π ⟨hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) (e p),
      (hSD _).1 (bas_mem v Λ he p) _ (memA v Λ X i)⟩ = τ (π (cf σ J v Λ hSD he X i p)) := fun i p =>
    hπ.2.2 _ _ (by rw [cf_coe, Orb.hR_conj σ J v hcm hJ])
  have hG : ∀ i j, π ⟨_, hg i j⟩ = ffGram τ 1 (phi σ J v Λ hSD he π a X) i j := by
    intro i j
    rw [ffGram_one]
    have e1 : (⟨_, hg i j⟩ : OR (E := E) v) = ∑ p, (⟨hR (Fv F v) σ J ((X : TupV (E := E) v n a) i) (e p),
        (hSD _).1 (bas_mem v Λ he p) _ (memA v Λ X i)⟩ : OR (E := E) v) * cf σ J v Λ hSD he X j p := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul]
      rw [gram_coord σ J v Λ hcm hJ hSD he he1]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [cf_coe, Orb.hR_conj σ J v hcm hJ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, hconj, phi_apply, phi_apply]
  constructor
  · intro hN
    funext i j
    rw [← hG]
    have h0 := (hπ.2.1 (⟨_, hg i j⟩ - ⟨T i j, hT i j⟩)).2 (hN i j)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · intro hE i j
    have h1 := congrFun (congrFun hE i) j
    rw [← hG] at h1
    have h0 : π (⟨_, hg i j⟩ - ⟨T i j, hT i j⟩) = 0 := by rw [map_sub, h1, sub_self]
    exact (hπ.2.1 _).1 h0

theorem card_cls (hcm : IsCMExt F E σ) (hJ : ∀ i j, σ (J j i) = J i j) (hSD : IsSDLoc σ J v Λ)
    {e : Fin n → Fin n → Fv F v ⊗[F] E} (he : Orb.IsOBas v Λ e) (he1 : gramR (Fv F v) σ J e = 1)
    {ϖ : Fv F v} {K : Type} [CommRing K] (τ : K →+* K) (π : OR (E := E) v →+* K) (hπ : IsRes σ v ϖ τ π)
    {a : ℕ} (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : ∀ i j, T i j ∈ OR (E := E) v) :
    Nat.card (clsU σ J v Λ a ϖ T) =
      Nat.card {X : Fin a → Fin n → K // ffGram τ 1 X = fun i j => π ⟨T i j, hT i j⟩} := by
  set Φ := phi σ J v Λ hSD he π a with hΦ
  let eq : (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) ≃+ (Fin a → Fin n → K) :=
    (QuotientAddGroup.quotientAddEquivOfEq (phi_ker σ J v Λ hSD he he1 hπ a)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ (phi_surj σ J v Λ hSD he he1 hπ a))
  have heq : ∀ x : lamA v Λ a, eq (QuotientAddGroup.mk x) = Φ x := fun x => rfl
  set P : (Fin a → Fin n → K) → Prop := fun M => ffGram τ 1 M = fun i j => π ⟨T i j, hT i j⟩ with hP
  have hset : clsU σ J v Λ a ϖ T = {q | P (eq q)} := by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      constructor
      · rintro ⟨y, hy, hyx⟩
        show P (eq (QuotientAddGroup.mk x))
        rw [← hyx, heq]
        exact (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT y).1 hy
      · intro hx
        refine ⟨x, (nearT_iff σ J v Λ hcm hJ hSD he he1 hπ T hT x).2 ?_, rfl⟩
        have : P (eq (QuotientAddGroup.mk x)) := hx
        rw [heq] at this
        exact this
  rw [hset]
  exact Nat.card_congr (Equiv.subtypeEquiv (p := fun q => q ∈ {q | P (eq q)}) eq.toEquiv (fun q => Iff.rfl))

end PI.OmLocU.Red
end
end

