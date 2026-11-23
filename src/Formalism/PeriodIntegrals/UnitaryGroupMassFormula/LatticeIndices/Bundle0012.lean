module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0010
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0007

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FrameMemSG
section
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3

variable {K : Type} [Field K] {r k : ℕ}

theorem frame_mem_sG (g1 Q : GL (Idx r k) K) (g2 J1 : Matrix (Idx r k) (Idx r k) K) (hJ : IsUnit J1.det)
    (hU : g2ᵀ * J1 * (g1 : Matrix (Idx r k) (Idx r k) K) = J1)
    (y1 y2 : Fin (r + 1) → Idx r k → K) (l : Fin (r + 1) → K) (hl : ∀ b, l b ≠ 0)
    (hy1 : ∀ b, ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) *ᵥ y1 b = Pi.single (pe b) 1)
    (hy2 : ∀ b, (Q : Matrix (Idx r k) (Idx r k) K)ᵀ *ᵥ (J1ᵀ *ᵥ y2 b) = l b • Pi.single (pf b) 1) :
    (FlagC (g1 : Matrix (Idx r k) (Idx r k) K) y1 ∧ FlagC g2 y2) ↔ Q⁻¹ * g1 * Q ∈ sG K r k := by
  set G1 : Matrix (Idx r k) (Idx r k) K := (g1 : Matrix (Idx r k) (Idx r k) K) with hG1
  set G1i : Matrix (Idx r k) (Idx r k) K := ((g1⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hG1i
  set Qm : Matrix (Idx r k) (Idx r k) K := (Q : Matrix (Idx r k) (Idx r k) K) with hQm
  set Qi : Matrix (Idx r k) (Idx r k) K := ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hQi
  have e1 : G1 * G1i = 1 := by rw [hG1, hG1i, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1' : G1i * G1 = 1 := by rw [hG1, hG1i, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have eQ : Qm * Qi = 1 := by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have eQ' : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJt : IsUnit J1ᵀ.det := by rw [Matrix.det_transpose]; exact hJ
  have eJ : J1ᵀ⁻¹ * J1ᵀ = 1 := Matrix.nonsing_inv_mul _ hJt
  have eJ' : J1ᵀ * J1ᵀ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJt
  have hS : ((Q⁻¹ * g1 * Q : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1 * Qm := by
    simp [hQi, hG1, hQm, Units.val_mul]
  have hSi : (((Q⁻¹ * g1 * Q)⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1i * Qm := by
    have : (Q⁻¹ * g1 * Q)⁻¹ = Q⁻¹ * g1⁻¹ * Q := by group
    rw [this]
    simp [hQi, hG1i, hQm, Units.val_mul]

  have hT : J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ := by
    have hUt : G1ᵀ * J1ᵀ * g2 = J1ᵀ := by
      have := congrArg Matrix.transpose hU
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    have hit : G1iᵀ * G1ᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    calc J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ * (G1ᵀ * J1ᵀ * g2) * J1ᵀ⁻¹ := by
          rw [← Matrix.mul_assoc G1iᵀ, ← Matrix.mul_assoc G1iᵀ, hit, Matrix.one_mul]
      _ = G1iᵀ := by rw [hUt, Matrix.mul_assoc, eJ', Matrix.mul_one]
  rw [mem_sG_iff_flagC, hS, hSi]
  refine and_congr ?_ ?_
  · rw [← flagC_conj Qi Qm G1 eQ eQ' y1]
    exact Iff.of_eq (congrArg _ (funext hy1))
  · rw [← flagC_conj J1ᵀ J1ᵀ⁻¹ g2 eJ eJ' y2, hT]
    have eQt : Qiᵀ * Qmᵀ = 1 := by rw [← Matrix.transpose_mul, eQ, Matrix.transpose_one]
    have eQt' : Qmᵀ * Qiᵀ = 1 := by rw [← Matrix.transpose_mul, eQ', Matrix.transpose_one]
    rw [← flagC_conj Qmᵀ Qiᵀ G1iᵀ eQt eQt' _]
    have hv : (fun b => Qmᵀ *ᵥ (J1ᵀ *ᵥ y2 b)) = fun b => l b • Pi.single (pf (k := k) b) (1 : K) := funext hy2
    rw [hv, flagC_smul _ l hl]
    have hm : Qmᵀ * G1iᵀ * Qiᵀ = (Qi * G1i * Qm)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hm]

end MassDataIdxStIm
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAPsiVScPSame
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def scP (p : TypX X) (c : Fv X.B.I.F p.1) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  eOf X.B.I (singleV X.B.I.F p.1 c)

theorem imA_psiV_eOf (v : HeightOneSpectrum (𝓞 X.B.I.F)) (a : Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.psiV X.B.I v (eOf X.B.I a) = algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (a v) := by
  simp [PI.FinKW.psiV, eOf]
  rfl

theorem component_scalarAt_same (p : TypX X) (c : Fv X.B.I.F p.1) :
    PI.FinKW.psiV X.B.I p.1 (scP X p c) = algebraMap (Fv X.B.I.F p.1) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) c := by
  rw [scP, imA_psiV_eOf, Comp_single_same]

theorem component_scalarAt_of_ne (p : TypX X) (v : HeightOneSpectrum (𝓞 X.B.I.F)) (h : v ≠ p.1)
    (c : Fv X.B.I.F p.1) : PI.FinKW.psiV X.B.I v (scP X p c) = 0 := by
  rw [scP, imA_psiV_eOf, Comp_single_ne X.B.I p.1 v h, map_zero]

theorem scalarAt_mem_integralAdeles (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F) :
    scP X p (c : Fv X.B.I.F p.1) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := by
  apply LocB_eOf_mem
  intro v
  by_cases h : v = p.1
  · subst h; show singleV X.B.I.F _ _ _ ∈ _; rw [Comp_single_same]; exact c.2
  · show singleV X.B.I.F p.1 _ v ∈ _; rw [Comp_single_ne X.B.I p.1 v h]; exact zero_mem _

theorem imA_smul_alg (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F)
    (u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    c • u = algebraMap (Fv X.B.I.F p.1) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) (c : Fv X.B.I.F p.1) • u := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Algebra.smul_def]
  rfl

theorem imA_vecV_sub (v : HeightOneSpectrum (𝓞 X.B.I.F)) (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a - b) = PI.FinKW.vecV X.B.I v a - PI.FinKW.vecV X.B.I v b := by
  funext i; simp [PI.FinKW.vecV]

theorem imA_vecV_smul' (v : HeightOneSpectrum (𝓞 X.B.I.F)) (t : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (t • w) = PI.FinKW.psiV X.B.I v t • PI.FinKW.vecV X.B.I v w := by
  funext i; simp [PI.FinKW.vecV, map_mul]

theorem imA_vec_ext (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (h : ∀ v, PI.FinKW.vecV X.B.I v w = 0) : w = 0 := by
  funext i
  exact PI.FinKW.local_vector_injective X.B.I (w i) fun v => congrFun (h v) i

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport
section
noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain Ideal

private theorem comap_ringEquiv_ne_bot {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B)
    (I : Ideal B) (hI : I ≠ ⊥) : I.comap (f : A →+* B) ≠ ⊥ := by
  intro h
  apply hI
  ext y
  constructor
  · intro hy
    have h1 : f.symm y ∈ I.comap (f : A →+* B) := by
      rw [Ideal.mem_comap]
      simpa using hy
    rw [h, Ideal.mem_bot] at h1
    simpa using h1
  · intro hy
    rw [Ideal.mem_bot] at hy
    rw [hy]
    exact I.zero_mem

theorem split_transport {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
    (l : ℕ) (h : {w : HeightOneSpectrum (𝓞 L) | ((l : ℕ) : 𝓞 L) ∈ w.asIdeal}.ncard = Module.finrank ℚ L) :
    {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K := by
  classical
  have hrk : Module.finrank ℚ K = Module.finrank ℚ L :=
    (e.toRatAlgEquiv.toLinearEquiv).finrank_eq
  rw [hrk, ← h]
  let g : 𝓞 K ≃+* 𝓞 L := NumberField.RingOfIntegers.mapRingEquiv e
  refine Set.ncard_congr
    (fun w _ => (⟨w.asIdeal.comap (g.symm : 𝓞 L →+* 𝓞 K),
      (by haveI := w.isPrime; infer_instance),
      comap_ringEquiv_ne_bot g.symm w.asIdeal w.ne_bot⟩ : HeightOneSpectrum (𝓞 L))) ?_ ?_ ?_
  · intro w hw
    simp only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢
    simpa using hw
  · intro a b _ _ hab
    have h1 := congrArg HeightOneSpectrum.asIdeal hab
    apply HeightOneSpectrum.ext
    ext x
    have h2 := SetLike.ext_iff.mp h1 (g x)
    simpa [Ideal.mem_comap] using h2
  · intro w hw
    refine ⟨⟨w.asIdeal.comap (g : 𝓞 K →+* 𝓞 L), (by haveI := w.isPrime; infer_instance),
      comap_ringEquiv_ne_bot g w.asIdeal w.ne_bot⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢
      simpa using hw
    · apply HeightOneSpectrum.ext
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap]
      simp

end MassDataIdxRes

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

theorem resArith_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : ResArith X p := by
  have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
      (D.host.g_prime 1).ne_zero p.1).1 p.2
    unfold gOf
    split_ifs with h
    · exact h
    · exact hty.resolve_left h
  have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
      ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
    unfold gOf
    split_ifs
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
  obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
  obtain ⟨hc, hn⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
  exact ⟨hc, hmem, hn⟩

theorem stResZ_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : StResZ X p :=
  stResZ_of X p (resArith_holds X p)

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StKHolds
section
noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem stK_gen (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) (g : ℕ) (hg : g ≠ 0) :
    ∃ K : Subgroup (HA (Fv F v) σ J),
      (K : Set (HA (Fv F v) σ J)) = Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v ∧
      IsOpen (K : Set (HA (Fv F v) σ J)) ∧ IsCompact (K : Set (HA (Fv F v) σ J)) ∧
      IsOpen (Formalism.L2.SG.TypedSets.Kgv σ J (L : Set (Fin n → E)) g v) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  obtain ⟨hKo, hKc⟩ := kloc_open_compact v L hL hfg
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hHc := isClosed_HR v σ J
  let K : Subgroup (HA (Fv F v) σ J) :=
    (Kloc (E := E) v (L : Set (Fin n → E))).comap (HR (Fv F v) σ J).subtype
  have hKset : (K : Set (HA (Fv F v) σ J)) = Formalism.L2.SG.TypedSets.Kv σ J (L : Set (Fin n → E)) v := rfl
  have hKo' : IsOpen (K : Set (HA (Fv F v) σ J)) := hKo.preimage continuous_subtype_val
  refine ⟨K, hKset, hKo', hHc.isClosedEmbedding_subtypeVal.isCompact_preimage hKc, ?_⟩
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  set U : Set (Fin n → Fv F v ⊗[F] E) := {w | ∃ z ∈ Λ, w = (g : v.adicCompletionIntegers F) • z} with hUdef
  have hc : ((g : v.adicCompletionIntegers F) : Fv F v) ≠ 0 := by
    have : ((g : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) g := by simp
    rw [this]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hg)
  have hU : IsOpen U := by
    have : U = (fun z => ((g : v.adicCompletionIntegers F) : Fv F v) • z) '' Λ := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    rw [this]
    exact isOpenMap_smul₀ hc _ hΛo
  have hS : IsOpen {h : GL (Fin n) (Fv F v ⊗[F] E) |
      ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) ∈
        {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U}} :=
    (isOpen_forall_mulVec v hΛc hU).preimage (Units.continuous_val.sub continuous_const)
  have heq : Formalism.L2.SG.TypedSets.Kgv σ J (L : Set (Fin n → E)) g v =
      (K : Set (HA (Fv F v) σ J)) ∩ (Subtype.val ⁻¹' {h : GL (Fin n) (Fv F v ⊗[F] E) |
        ((h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) - 1) ∈
          {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U}}) :=
    Set.ext fun x => Iff.rfl
  rw [heq]
  exact hKo'.inter (hS.preimage continuous_subtype_val)

end MassDataIdxK

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

theorem stK_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : StK X p :=
  MassDataIdxK.stK_gen p.1 X.B.I.cm.sig X.B.I.J X.B.I.L X.B.I.L_span X.B.I.L_fg (gOf p) (gOf_prime X p).ne_zero

end MassDataIdxSteps
end
end

