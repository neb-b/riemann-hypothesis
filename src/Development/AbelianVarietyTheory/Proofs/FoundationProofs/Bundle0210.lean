module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.Columns.PolyFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankIntertwiningMapDirectSum
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.IntertwinerSum

open Representation

variable {k G ι U W : Type} [Field k] [Group G] [Fintype ι] {V : ι → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [AddCommGroup U] [Module k U]
  [AddCommGroup W] [Module k W]

theorem finite_intertwiningMap [FiniteDimensional k U] [FiniteDimensional k W]
    (τ : Representation k G U) (σ : Representation k G W) :
    FiniteDimensional k (τ.IntertwiningMap σ) :=
  FiniteDimensional.of_injective
    ({ toFun := fun f => f.toLinearMap
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : τ.IntertwiningMap σ →ₗ[k] (U →ₗ[k] W))
    (IntertwiningMap.toLinearMap_injective τ σ)

theorem equivs_of_biproduct (ρ : ∀ i, Representation k G (V i)) (τ : Representation k G U)
    (σ : Representation k G W) (p : ∀ i, σ.IntertwiningMap (ρ i))
    (j : ∀ i, (ρ i).IntertwiningMap σ) (hsum : ∀ w, ∑ i, j i (p i w) = w)
    (hdiag : ∀ i x, p i (j i x) = x) (hoff : ∀ i i', i' ≠ i → ∀ x, p i (j i' x) = 0) :
    Nonempty (τ.IntertwiningMap σ ≃ₗ[k] ∀ i, τ.IntertwiningMap (ρ i)) ∧
      Nonempty (σ.IntertwiningMap τ ≃ₗ[k] ∀ i, (ρ i).IntertwiningMap τ) := by
  classical
  refine ⟨⟨{ toFun := fun f i => (p i).comp f
             map_add' := fun f g => ?_
             map_smul' := fun c f => ?_
             invFun := fun f => ∑ i, (j i).comp (f i)
             left_inv := fun f => ?_
             right_inv := fun f => ?_ }⟩,
          ⟨{ toFun := fun f i => f.comp (j i)
             map_add' := fun f g => rfl
             map_smul' := fun c f => rfl
             invFun := fun f => ∑ i, (f i).comp (p i)
             left_inv := fun f => ?_
             right_inv := fun f => ?_ }⟩⟩
  · funext i
    exact DFunLike.ext _ _ fun u => map_add (p i) (f u) (g u)
  · funext i
    exact DFunLike.ext _ _ fun u => map_smul (p i) c (f u)
  · refine DFunLike.ext _ _ fun u => ?_
    rw [IntertwiningMap.sum_apply]
    exact hsum (f u)
  · funext i
    refine DFunLike.ext _ _ fun u => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [IntertwiningMap.comp_apply, IntertwiningMap.sum_apply, map_sum]
    simp only [IntertwiningMap.comp_apply]
    rw [Finset.sum_eq_single i (fun i' _ h => hoff i i' h _) (by simp)]
    exact hdiag i _
  · refine DFunLike.ext _ _ fun w => ?_
    rw [IntertwiningMap.sum_apply]
    simp only [IntertwiningMap.comp_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hsum]
  · funext i
    refine DFunLike.ext _ _ fun x => ?_
    rw [IntertwiningMap.comp_apply, IntertwiningMap.sum_apply]
    simp only [IntertwiningMap.comp_apply]
    rw [Finset.sum_eq_single i (fun i' _ h => by rw [hoff i' i h.symm, map_zero]) (by simp), hdiag]

theorem finrank_intertwiningMap_directSum :
    ∀ (k G ι U W : Type) [Field k] [Group G] [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] [AddCommGroup U] [Module k U] [FiniteDimensional k U] [AddCommGroup W] [Module k W] (ρ : ∀ i, Representation k G (V i)) (τ : Representation k G U) (σ : Representation k G W), Nonempty ((Representation.directSum ρ).Equiv σ) → Module.finrank k (τ.IntertwiningMap σ) = ∑ i, Module.finrank k (τ.IntertwiningMap (ρ i)) ∧ Module.finrank k (σ.IntertwiningMap τ) = ∑ i, Module.finrank k ((ρ i).IntertwiningMap τ) := by
  intro k G ι U W _ _ _ V _ _ _ _ _ _ _ _ ρ τ σ ⟨e⟩
  classical
  let p₀ : ∀ i, (Representation.directSum ρ).IntertwiningMap (ρ i) := fun i =>
    { toLinearMap := DirectSum.component k ι V i
      isIntertwining' := fun g => by
        refine LinearMap.ext fun x => ?_
        rfl }
  let j₀ : ∀ i, (ρ i).IntertwiningMap (Representation.directSum ρ) := fun i =>
    { toLinearMap := DirectSum.lof k ι V i
      isIntertwining' := fun g => by
        refine LinearMap.ext fun x => ?_
        simp [Representation.directSum] }
  have hse : ∀ x, e.symm.toIntertwiningMap (e.toIntertwiningMap x) = x :=
    fun x => e.toLinearEquiv.symm_apply_apply x
  have hes : ∀ x, e.toIntertwiningMap (e.symm.toIntertwiningMap x) = x :=
    fun x => e.toLinearEquiv.apply_symm_apply x
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := equivs_of_biproduct ρ τ σ
    (fun i => (p₀ i).comp e.symm.toIntertwiningMap) (fun i => e.toIntertwiningMap.comp (j₀ i))
    (fun w => by
      simp only [IntertwiningMap.comp_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum]
      have : ∀ x : ⨁ i, V i, ∑ i, j₀ i (p₀ i x) = x := fun x => DirectSum.sum_univ_of x
      rw [this, hes])
    (fun i x => by
      simp only [IntertwiningMap.comp_apply]
      rw [hse]
      exact DirectSum.component.lof_self k i x)
    (fun i i' h x => by
      simp only [IntertwiningMap.comp_apply]
      rw [hse]
      exact DirectSum.of_eq_of_ne i' i x h.symm)
  have := fun i => finite_intertwiningMap τ (ρ i)
  have := fun i => finite_intertwiningMap (ρ i) τ
  exact ⟨a.finrank_eq.trans (Module.finrank_pi_fintype k), b.finrank_eq.trans (Module.finrank_pi_fintype k)⟩

end GlobalTheory.IntertwinerSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisSlTwoActionModularFunctionRingOfCongr
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gal_sl_io_of_cong :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  intro Ω _ _ _ ε T a N w hN hLv s d hs γ γ' hC
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.FN.exists_ringEquiv_extend_of_embedding Ω ε s.toRingEquiv
  have hg' : ∀ x, g (ε x) = ε (s x) := hg
  obtain ⟨u, hu, hZ⟩ := (_root_.GlobalTheory.ZetaExp.main Ω ε s N hN).2 d hs
  have hE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨s y, (hg' y).symm⟩
  obtain ⟨f', hf'L, hf'C⟩ := _root_.GlobalTheory.FN.lv_galois_conj g ε.range N u w (a : ℍ → ℂ) hE (hZ g hg') hLv
  let a' : GlobalTheory.FN.ring ε.range := ⟨f', mem_ring_of_inR ⟨N, w, hN, hf'L⟩⟩
  obtain ⟨hext, hcmp, hexpinj, -⟩ := _root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T
  obtain ⟨-, -, hSL, -⟩ := _root_.GlobalTheory.FN.cmp_props

  have key : ∀ γ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u →
      T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.io a') := by
    intro γ γ' hM
    obtain ⟨b, hb, hbio⟩ := hcmp (ofSL γ) a
    obtain ⟨b', hb', hb'io⟩ := hcmp (ofSL γ') a'
    rw [hbio, hb'io]
    apply hexpinj
    ext r
    rw [T.gal_exp]
    have hb1 : (b : ℍ → ℂ) = fun τ => (a : ℍ → ℂ) (γ • τ) := by rw [hb, hSL]
    have hb2 : (b' : ℍ → ℂ) = fun τ => f' (γ' • τ) := by rw [hb', hSL]
    refine Eq.symm ?_
    refine _root_.GlobalTheory.FN.exp_conj Ω ε s.toRingEquiv.toRingHom g N w b b' _ _ hg' hN ?_ ?_ (T.exp_io b) (T.exp_io b') r
    · rw [hb1]; exact hLv.2 γ
    · rw [hb1, hb2]; exact hf'C γ γ' hM
  have h1 : T.gal s (T.io a) = T.io a' := by
    have hM1 : dg u * redGL N 1 = redGL N 1 * dg u := by simp [redGL]
    have := key 1 1 hM1
    obtain ⟨c, hc, hcio⟩ := hcmp (ofSL 1) a
    obtain ⟨c', hc', hc'io⟩ := hcmp (ofSL 1) a'
    have e1 : c = a := Subtype.ext (by rw [hc, hSL]; funext τ; simp)
    have e2 : c' = a' := Subtype.ext (by rw [hc', hSL]; funext τ; simp [a'])
    rw [hcio, hc'io, e1, e2] at this
    exact this
  rw [h1]
  exact key γ γ' ((_root_.GlobalTheory.FNCong.cong_iff_dg N d u hu γ γ').mp hC)

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenericDetPowMulHw
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowAct_genericDet (R : Type) [CommRing R] (n : ℕ) (g : Matrix (Fin n) (Fin n) R) :
    rowAct R (n := n) g (lpMinor R n le_rfl le_rfl) = C g.det * lpMinor R n le_rfl le_rfl := by
  unfold lpMinor
  rw [AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext1 p q
  simp [rowAct, Matrix.mul_apply]

theorem genericDet_pow_mem (R : Type) [CommRing R] (n c : ℕ) :
    lpMinor R n le_rfl le_rfl ^ c ∈ dualWeyl R n n (fun _ => c) := by
  have h := bidetMem R n n c (fun _ => n) (fun _ => le_rfl) (fun _ => Fin.castLE le_rfl)
  have e : shapeDeg (n := n) (fun _ : Fin c => n) = fun _ => c := by
    funext t
    simp [shapeDeg]
  rw [e] at h
  simpa [bideterminant, initMinor, lpMinor] using h

theorem genericDet_pow_mul_hw (R : Type) [CommRing R] (n c : ℕ) (ν : Fin n → ℕ) :
    lpMinor R n le_rfl le_rfl ^ c * hw R le_rfl ν = hw R (le_refl n) (fun i => ν i + c) := by
  cases n with
  | zero => simp [hw, lpMinor]
  | succ m =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_left_comm]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      congr 1
      have hs : (Fin.castSucc s).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_pos hs]
      omega
    · have hs : ¬ (Fin.last m).val + 1 < m + 1 := by simp
      simp only [nuNext, dif_neg hs, Nat.sub_zero]
      rw [pow_add, mul_comm]
      rfl

theorem genericDet_pow_mul :
    ∀ (n c : ℕ) (ν : Fin n → ℕ), (∀ f ∈ dualWeyl ℂ n n ν, lpMinor ℂ n le_rfl le_rfl ^ c * f ∈ dualWeyl ℂ n n (fun i => ν i + c)) ∧ (∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ), rowAct ℂ g (lpMinor ℂ n le_rfl le_rfl ^ c * f) = g.det ^ c • (lpMinor ℂ n le_rfl le_rfl ^ c * rowAct ℂ g f)) ∧ (Antitone ν → lpMinor ℂ n le_rfl le_rfl ^ c * hw ℂ le_rfl ν = hw ℂ (le_refl n) (fun i => ν i + c)) := by
  intro n c ν
  refine ⟨fun f hf => ?_, fun g f => ?_, fun _ => genericDet_pow_mul_hw ℂ n c ν⟩
  · rw [mul_comm]
    exact (dualWeylMul ℂ n n ν (fun _ => c) f _).1 hf (genericDet_pow_mem ℂ n c)
  · rw [map_mul, map_pow, rowAct_genericDet, mul_pow, smul_eq_C_mul, map_pow, mul_assoc]

end GlobalTheory.Branching
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
section
noncomputable section

namespace GlobalTheory.ColClassCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

section Descent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p : ℕ}

theorem unram_card_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (v : Ideal (𝓞 F)) [hv : v.IsPrime] (hpv : (p : 𝓞 F) ∈ v) :
    (p : 𝓞 F) ∉ v ^ 2 ∧ Nat.card (𝓞 F ⧸ v) = p := by
  obtain ⟨P, hP, hPl⟩ := (inferInstance : Nonempty (v.primesOver (𝓞 E)))
  have hgP : (p : 𝓞 E) ∈ P := by
    simpa using (Ideal.mem_of_liesOver P v (p : 𝓞 F)).1 hpv
  obtain ⟨hP2, hP3⟩ := GlobalTheory.LocSplit.split_prime hp h P hgP
  refine ⟨fun h2 => hP2 ?_, ?_⟩
  · have := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hPl.over.le) 2 this
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : Nontrivial (𝓞 F ⧸ v) := Ideal.Quotient.nontrivial_iff.2 hv.ne_top
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v), Ideal.Quotient.eq_zero_iff_mem]
      exact hpv
    haveI : CharP (𝓞 F ⧸ v) p := (CharP.charP_iff_prime_eq_zero hp).2 h0
    have hb : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 F ⧸ v)) := by
      refine ⟨RingHom.injective _, fun x => ?_⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨m, hm⟩ := hP3 (algebraMap (𝓞 F) (𝓞 E) x)
      refine ⟨(m : ZMod p), ?_⟩
      rw [map_intCast, ← map_intCast (Ideal.Quotient.mk v), eq_comm, Ideal.Quotient.eq,
        Ideal.mem_of_liesOver P v]
      simpa using hm
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_zmod]

theorem ncard_primesOver_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)).ncard = Module.finrank ℚ F := by
  classical
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp'.ne_zero).mpr hp'
  have hne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have hs := Ideal.sum_ramification_inertia (𝓞 F) ℚ F (p := Ideal.span {(p : ℤ)}) hne
  rw [← hs, ← IsDedekindDomain.coe_primesOverFinset hne, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hne] at hq
  haveI := hq.1
  haveI := hq.2
  have hpq : (p : 𝓞 F) ∈ q := by
    simpa using (Ideal.mem_of_liesOver q (Ideal.span {(p : ℤ)}) (p : ℤ)).1 (Ideal.mem_span_singleton_self _)
  obtain ⟨h2, hc⟩ := unram_card_of_split (E := E) hp h q hpq
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' q = 1 := by
    by_contra hne1
    refine h2 ?_
    have := (Ideal.ramificationIdx'_ne_one_iff (by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using hpq)).1 hne1
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem] at this
    simpa using this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' q = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' q hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hc] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end Descent

theorem finrank_F (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  letI := D.host.cmStar
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [D.sp.cm.deg2, finrank_host D] at h1
  omega

theorem splitsF_of_splitsCompletely (D : D7) {p : ℕ} (h : SplitsCompletely D.host.E p) : SplitsF D p := by
  obtain ⟨hp, h⟩ := h
  rw [GlobalTheory.HostSplit.ncard_placesOver _ hp] at h
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 := ncard_primesOver_of_split (F := D.host.F) hp h
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp, finrank_F] at h1
    rw [← h1, ← Nat.card_coe_set_eq]
    rfl
  · haveI := v.isPrime
    exact (unram_card_of_split hp h v.asIdeal hv).2

theorem levelPrime_mod (D : D7) (u : D.what₂.Word) :
    (D.mem u).A.T % (D.host.QS * D.host.q * D.host.d) = 1 := by
  obtain ⟨π, -, hn, hm⟩ := D.T_norm u
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hm
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hn0 : 1 ≤ D.host.QS := D.host.QS_pos
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = D.host.QS * D.host.q * D.host.d := ⟨_, rfl⟩
  have hM1 : 1 < M := by
    have h1 : 1 * 3 * 7 ≤ D.host.QS * D.host.q * D.host.d :=
      Nat.mul_le_mul (Nat.mul_le_mul hn0 (by omega)) (by omega)
    omega
  rw [← hM] at ha ⊢
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (D.host.g 0 * D.host.g 1) ^ 2 := ⟨_, rfl⟩
  rw [← hG] at ha
  set y : D.host.E := (a : D.host.E) * G with hy
  have hyi : IsIntegral ℤ y := (RingOfIntegers.isIntegral_coe a).mul (isIntegral_natCast G)
  have hπ : (π : D.host.E) = 1 + M * y := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    rw [hy]
    push_cast at this ⊢
    linear_combination -this
  have hci : IsIntegral ℤ (D.conjF y) := hyi.map (D.conjF.toRingHom.toIntAlgHom)
  rw [← D.conjF_eq, hπ, map_add (f := _), map_mul, map_one, map_natCast] at hn
  set z : D.host.E := y + D.conjF y + M * (y * D.conjF y) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := D.host.E) M).mul (hyi.mul hci))
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have h4 : z = algebraMap ℚ D.host.E ((((D.mem u).A.T : ℚ) - 1) / M) := by
    have hM0' : (M : D.host.E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff ] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((D.mem u).A.T : ℤ) : ℚ) = ((1 + M * n : ℤ) : ℚ) := by
    have : (n : ℚ) = (((D.mem u).A.T : ℚ) - 1) / M := by simpa using hn'
    push_cast
    rw [this]
    field_simp
    ring
  have h6 : ((D.mem u).A.T : ℤ) = 1 + M * n := by exact_mod_cast h5
  have h7 : (((D.mem u).A.T % M : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, h6, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hM1)
  exact_mod_cast h7

theorem levelPrime_splitsCompletely_in_cmField (D : D7) (u : D.what₂.Word) : SplitsCompletely D.host.E (D.mem u).A.T :=
  ⟨(D.mem u).A.T_prime,
    (GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (levelPrime_mod D u)).1⟩

theorem split_g_iff (D : D7) (i : Fin 2) :
    SplitsF D (D.host.g i) ↔ SplitsCompletely D.host.E (D.host.g i) :=
  ⟨fun _ => splitsCompletely_g D i, splitsF_of_splitsCompletely D⟩

end GlobalTheory.ColClassCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RowActCoefPolyAndUnitaryDense
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem exists_poly_rowAct_coef (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ)
    (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P := by
  induction f using MvPolynomial.induction_on generalizing l with
  | C a => exact ⟨C (l (C a)), fun g => by simp [rowAct]⟩
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp l
    obtain ⟨Q, hQ⟩ := hq l
    exact ⟨P + Q, fun g => by simp only [map_add (f := _), hP, hQ]⟩
  | mul_X p v hp =>
    choose P hP using fun b : Fin n => hp (l ∘ₗ LinearMap.mulRight ℂ (X (b, v.2)))
    refine ⟨∑ b, X (v.1, b) * P b, fun g => ?_⟩
    have e : rowAct ℂ g (X v) = ∑ b, g v.1 b • X (b, v.2) := by
      simp [rowAct, smul_eq_C_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, e, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]
    rfl

theorem eq_zero_of_vanish_unitaryGroup (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (h : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) : P = 0 := by
  have hinj : Function.Injective (fun x : Fin n × Fin n => ((), x) : Fin n × Fin n → Unit × Fin n × Fin n) :=
    fun x y e => congrArg Prod.snd e
  apply rename_injective _ hinj
  rw [map_zero]
  refine Formalism.L2.Col.eq_zero_of_forall_unitary (ι := Unit) (fun _ => 1) (fun _ => by simp) _ fun u hu => ?_
  rw [eval_rename]
  have := h (u ()) (Matrix.mem_unitaryGroup_iff'.2 (hu ()))
  simpa [Function.comp_def] using this

theorem rowAct_coef_poly_and_unitary_dense :
    (∀ (n k : ℕ) (f : MvPolynomial (Fin n × Fin k) ℂ) (l : Module.Dual ℂ (MvPolynomial (Fin n × Fin k) ℂ)),
      ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : Matrix (Fin n) (Fin n) ℂ,
        l (rowAct ℂ g f) = eval (fun x => g x.1 x.2) P) ∧
    ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
      (∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun x => u x.1 x.2) P = 0) → P = 0 :=
  ⟨exists_poly_rowAct_coef, eq_zero_of_vanish_unitaryGroup⟩

end GlobalTheory.Branching
end

