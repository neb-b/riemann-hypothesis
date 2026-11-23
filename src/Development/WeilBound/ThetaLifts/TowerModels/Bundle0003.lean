module

public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0060

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.DetHerm
section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem det_ne_zero_of_hasSig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  subst hrs
  intro hM
  have key := congrArg Matrix.det hA
  rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
    Fintype.card_fin] at key
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  have hsub : (Aᵀ * M * A.map star).submatrix e.symm e.symm =
      (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star := by
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply]
  have h2 := congrArg Matrix.det hsub
  rw [Matrix.det_submatrix_equiv_self, key, Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul] at h2
  exact pow_ne_zero _ (by norm_num) h2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}

theorem det_herm {n : ℕ} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  exact fun h0 => h (by rw [h0, map_zero])

end PositivityTheory.ThKG.Tow

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneBas
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {v : Pl F} (τ : E →ₐ[F] Fv F v)

theorem map_mem_splitLat {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {z : Fin n → E} (hz : z ∈ L) :
    (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, AddSubgroup.subset_closure ⟨1, one_mem _, z, hz, rfl⟩,
    funext fun i => by simp [splitVec, splitProj_tmul]⟩

theorem splitLat_le {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    (N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v)) (hN : ∀ z ∈ L, (fun i => τ (z i)) ∈ N) :
    splitLat τ L ≤ N := by
  rintro _ ⟨y, hy, rfl⟩
  refine latLoc_induction (p := fun y => splitVec τ y ∈ N) (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_)
    (fun y hy => ?_) hy
  · have := N.smul_mem ⟨a, ha⟩ (hN x hx)
    convert this using 1
    rfl
  · have : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun _ => map_zero _
    rw [this]; exact zero_mem _
  · rw [splitVec_add]; exact add_mem hy hz
  · have : splitVec τ (-y) = -splitVec τ y := funext fun _ => map_neg _ _
    rw [this]; exact neg_mem hy

theorem map_mem_of_unit {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} {c : E} (hc : c • x ∈ L)
    (hv : Valued.v (τ c) = 1) {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) :
    (a • fun i => τ (x i)) ∈ splitLat τ L := by
  have h0 : τ c ≠ 0 := fun e => by simp [e] at hv
  have h1 : a * (τ c)⁻¹ ∈ v.adicCompletionIntegers F :=
    mul_mem ha (by rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one])
  have := (splitLat τ L).smul_mem ⟨_, h1⟩ (map_mem_splitLat τ hc)
  convert this using 1
  funext i
  change a * τ (x i) = a * (τ c)⁻¹ * τ (c * x i)
  rw [map_mul]
  field_simp

theorem exists_basis (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E)
    (β₁ : GL (Fin n₁) (Fv F v)) (i₀ i₁ : ℕ) (hn : n = n₁ + 2) (h01 : i₀ < i₁) (h1n : i₁ < n) (hlat : L.IsFullLattice E)
    (hsplit : ∀ z ∈ L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ L ∧ t • y ∈ L ∧ ι *ᵥ u ∈ L ∧ z = s • x + ι *ᵥ u + t • y)
    (hx : (∀ c : E, c • x ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • x ∈ L ∧ Valued.v (τ c) = 1)
    (hy : (∀ c : E, c • y ∈ L → Valued.v (τ c) ≤ 1) ∧ ∃ c : E, c • y ∈ L ∧ Valued.v (τ c) = 1)
    (hβ₁ : IsSplitBasis τ (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) β₁) :
    ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = τ (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = τ (y r)) ∧ ∀ j : Fin n₁, i.1 = skip i₀ i₁ j → ∀ r, β.1 r i = (ι.map τ * β₁.1) r j) ∧
      IsSplitBasis τ L β := by
  classical
  have hsk : ∀ j : Fin n₁, skip i₀ i₁ j < n := fun j => by
    have := j.2
    unfold skip; split_ifs <;> omega
  let f : Fin n₁ ⊕ Bool → Fin n := Sum.elim (fun j => ⟨skip i₀ i₁ j, hsk j⟩)
    fun b => cond b ⟨i₁, h1n⟩ ⟨i₀, h01.trans h1n⟩
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [hn]⟩
    rintro (a | _ | _) (b | _ | _) e <;>
      simp only [f, Sum.elim_inl, Sum.elim_inr, cond, Fin.mk.injEq, skip, Sum.inl.injEq, Fin.ext_iff] at e ⊢ <;>
      first | omega | (split_ifs at e <;> omega)
  let e := Equiv.ofBijective f hf
  let c : Fin n₁ ⊕ Bool → Fin n → Fv F v := Sum.elim (fun j r => (ι.map τ * β₁.1) r j)
    fun b => cond b (fun r => τ (y r)) fun r => τ (x r)
  let b : Matrix (Fin n) (Fin n) (Fv F v) := Matrix.of fun r i => c (e.symm i) r
  have hb : ∀ u : Fin n → Fv F v, b *ᵥ u = (u (e (.inr false)) • fun r => τ (x r)) +
      ι.map τ *ᵥ β₁.1 *ᵥ (fun j => u (e (.inl j))) + u (e (.inr true)) • fun r => τ (y r) := fun u => by
    funext r
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, b, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← e.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_bool, c, Sum.elim_inl, Sum.elim_inr, cond]
    ring
  have hmv : ∀ u : Fin n₁ → E, (fun i => τ ((ι *ᵥ u) i)) = ι.map τ *ᵥ fun j => τ (u j) := fun u =>
    funext fun i => RingHom.map_mulVec (τ : E →+* Fv F v) ι u i
  have hsurj : ∀ w ∈ splitLat τ L, ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w := by
    let N : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v) :=
      { carrier := {w | ∃ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ∧ b *ᵥ u = w}
        zero_mem' := ⟨0, fun _ => zero_mem _, Matrix.mulVec_zero _⟩
        add_mem' := by
          rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
          exact ⟨u + u', fun i => add_mem (hu i) (hu' i), Matrix.mulVec_add _ _ _⟩
        smul_mem' := by
          rintro a _ ⟨u, hu, rfl⟩
          exact ⟨(a : Fv F v) • u, fun i => mul_mem a.2 (hu i), Matrix.mulVec_smul _ _ _⟩ }
    refine fun w hw => splitLat_le τ N (fun z hz => ?_) hw
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hsplit z hz
    have hu' := hβ₁.mem_iff.1 (map_mem_splitLat τ (L := L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))) hu)
    refine ⟨fun i => Sum.elim ((β₁⁻¹).1 *ᵥ fun j => τ (u j)) (fun b => cond b (τ t) (τ s)) (e.symm i), fun i => ?_, ?_⟩
    · beta_reduce
      rcases e.symm i with j | _ | _
      · exact hu' j
      · exact hx.1 s hs
      · exact hy.1 t ht
    · rw [hb]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, cond]
      rw [Matrix.mulVec_mulVec _ β₁.1, Units.mul_inv, Matrix.one_mulVec, ← hmv]
      funext r
      simp
  have hunit : IsUnit b := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    have h1 : ∀ z : Fin n → E, (fun i => τ (z i)) ∈ LinearMap.range b.mulVecLin := fun z => by
      have hz : z ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hlat.span_eq_top]; trivial
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨u, -, hu⟩ := hsurj _ (map_mem_splitLat τ hz); exact ⟨u, hu⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add a a' _ _ ha ha' => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem ha ha'
      | smul a z _ hz => simp only [Pi.smul_apply, smul_eq_mul, map_mul]; exact Submodule.smul_mem _ (τ a) hz
    intro w
    have : w = ∑ i, w i • fun k => τ ((Pi.single i 1 : Fin n → E) k) := by
      funext k
      simp [Pi.single_apply, apply_ite]
    rw [this]
    exact (Submodule.sum_mem (LinearMap.range b.mulVecLin) fun i _ => Submodule.smul_mem _ _ (h1 _))
  obtain ⟨β, hβ⟩ := hunit
  have col : ∀ k r, β.1 r (e k) = c k r := fun k r => by rw [hβ]; simp [b]
  refine ⟨β, fun i => ⟨fun hi r => ?_, fun hi r => ?_, fun j hi r => ?_⟩, fun u => ⟨fun hu => ?_, fun hu => ?_⟩⟩
  · rw [show i = e (.inr false) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inr true) from Fin.ext hi, col]; rfl
  · rw [show i = e (.inl j) from Fin.ext hi, col]; rfl
  · rw [hβ, hb]
    obtain ⟨s, hs, hs'⟩ := hx.2
    obtain ⟨t, ht, ht'⟩ := hy.2
    refine add_mem (add_mem (map_mem_of_unit τ hs hs' (hu _)) ?_) (map_mem_of_unit τ ht ht' (hu _))
    refine splitLat_le τ ((splitLat τ L).comap ((ι.map τ).mulVecLin.restrictScalars (v.adicCompletionIntegers F)))
      (fun z hz => ?_) ((hβ₁ _).1 fun j => hu _)
    change ι.map τ *ᵥ (fun j => τ (z j)) ∈ splitLat τ L
    rw [← hmv]
    exact map_mem_splitLat τ hz
  · obtain ⟨u', hu', e'⟩ := hsurj _ hu
    rw [← hβ] at e'
    rw [← Matrix.mulVec_injective_iff_isUnit.2 β.isUnit e']
    exact hu'

end PositivityTheory.ThKG.Tow.Pln

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneCodiff
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem trace_mixedEmbedding (y : F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (mixedEmbedding F y) = (Algebra.trace ℚ F y : ℝ) :=
  _root_.UpperTheory.Reformulated.B.DYhb7.main y

theorem psi_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  have hat : At (evI F) (pairA F (algebraMap F (Ainf F) (-x)) 0) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  rw [e, AddChar.map_add_eq_mul, hψ.2.1, one_mul, hψ.2.2 _ hat]
  have h2 : evI F (pairA F (algebraMap F (Ainf F) (-x)) 0) = mixedEmbedding F (-x) := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) (-x)) = _
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rw [h2, trace_mixedEmbedding, map_neg]
  congr 1
  push_cast
  ring

theorem psi_int {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (t : F)
    (ht : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * t) = k) (α : Af F) (hα : ∀ v, α v ∈ v.adicCompletionIntegers F) :
    ψ (pairA F 0 (α * algebraMap F (Af F) t)) = 1 := by
  refine GlobalTheory.IntDense.addChar_eq_one_of_integral F ψ hψ.1 t (fun a => ?_) α hα
  obtain ⟨k, hk⟩ := ht a
  rw [psi_fin_rat hψ, hk, Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

theorem trace_cm (h : IsCMExt F E σ) (x : E) : algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  have h1 := trace_eq_sum_embeddings (K := F) (L := E) (AlgebraicClosure E) (x := x)
  let τ : E →ₐ[F] AlgebraicClosure E := IsScalarTower.toAlgHom F E _
  have h2 : (Finset.univ : Finset (E →ₐ[F] AlgebraicClosure E)) = {τ, τ.comp σ} := by
    ext τ'
    simpa using eq_or_eq_comp_conj h τ τ'
  rw [h2, Finset.sum_pair (comp_conj_ne h τ).symm] at h1
  apply (algebraMap E (AlgebraicClosure E)).injective
  rw [← IsScalarTower.algebraMap_apply, h1, map_add (f := _)]
  rfl

theorem val_le_one_of_codiff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hv : PsiUnr ψ v) (a : F)
    (ha : ∀ o : 𝓞 F, IsIntegral ℤ (Algebra.trace ℚ F (o * a))) : Valued.v (algebraMap F (Fv F v) a) ≤ 1 := by
  have h2 := psi_int hψ a fun o => by
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 (ha o)
    exact ⟨k, hk.symm⟩
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((hv _).1 fun y hy => ?_)
  have h3 := h2 (singleFin v y) fun w => by
    by_cases hw : w = v
    · subst hw
      change evalV _ w (singleFin w y) ∈ _
      rw [evalV_singleFin_self]
      exact hy
    · change evalV _ w (singleFin v y) ∈ _
      rw [evalV_singleFin_ne hw]
      exact zero_mem _
  have e : singleFin v y * algebraMap F (Af F) a = singleFin v (algebraMap F (Fv F v) a * y) := by
    apply af_ext
    intro u
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, mul_comm]
      rfl
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]
  rw [e] at h3
  exact h3


variable (E) in
def codE : Submodule (𝓞 E) E where
  carrier := {c | ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * c))}
  zero_mem' o := by simpa using isIntegral_zero
  add_mem' ha hb o := by rw [mul_add, map_add (f := _)]; exact (ha o).add (hb o)
  smul_mem' a c hc o := by
    have := hc (o * a)
    change IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (a : E) * c)) at this
    rwa [mul_assoc] at this

theorem one_mem_codE : (1 : E) ∈ codE E := fun o => by
  rw [mul_one]; exact Algebra.isIntegral_trace o.isIntegral_coe


variable (E) in
def intE : Submodule (𝓞 E) E where
  carrier := {c | IsIntegral ℤ c}
  zero_mem' := isIntegral_zero
  add_mem' ha hb := ha.add hb
  smul_mem' a _ hc := a.isIntegral_coe.mul hc

theorem val_le_one_of_intE {v : Pl F} (τ : E →ₐ[F] Fv F v) (c : E) (hc : c ∈ intE E) : Valued.v (τ c) ≤ 1 :=
  apply_coe_mem τ (⟨c, hc⟩ : 𝓞 E)

theorem val_le_one_of_codE (h : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {v : Pl F} (hv : PsiUnr ψ v)
    (τ : E →ₐ[F] Fv F v) (c : E) (hc : c ∈ codE E) : Valued.v (τ c) ≤ 1 := by
  have h1 : ∀ o : 𝓞 E, Valued.v (τ (o * c) + τ (σ (o * c))) ≤ 1 := fun o => by
    rw [← map_add (f := _), ← trace_cm h, AlgHom.commutes]
    refine val_le_one_of_codiff hψ hv _ fun a => ?_
    have := hc (algebraMap (𝓞 F) (𝓞 E) a * o)
    rw [← Algebra.trace_trace (S := F)] at this
    convert this using 2
    rw [← smul_eq_mul, ← map_smul, Algebra.smul_def, ← mul_assoc]
    rfl
  have hne : ¬ (splitPrime (τ.comp σ)).asIdeal ≤ (splitPrime τ).asIdeal := fun hle =>
    splitPrime_comp_ne h τ (HeightOneSpectrum.ext
      ((splitPrime (τ.comp σ)).isMaximal.eq_of_le (splitPrime τ).isPrime.ne_top hle))
  obtain ⟨p, hp, hp'⟩ := Set.not_subset.1 hne
  have a1 : Valued.v (τ (σ p)) < 1 := (mem_splitPrime (τ.comp σ) p).1 hp
  have a2 : Valued.v (τ p) = 1 := le_antisymm (apply_coe_mem τ p) (not_lt.1 fun e => hp' ((mem_splitPrime τ p).2 e))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Valued.v (τ (σ p)) ^ k * Valued.v (τ (σ c)) ≤ 1 := by
    by_cases h0 : Valued.v (τ (σ c)) = 0
    · exact ⟨0, by simp [h0]⟩
    · obtain ⟨k, hk⟩ := exists_pow_lt₀ a1 (Units.mk0 _ h0)⁻¹
      refine ⟨k, ?_⟩
      rw [Units.val_inv_eq_inv_val, Units.val_mk0] at hk
      calc _ ≤ (Valued.v (τ (σ c)))⁻¹ * Valued.v (τ (σ c)) := by gcongr
        _ = 1 := inv_mul_cancel₀ h0
  have b1 := h1 (p ^ k)
  have b2 : Valued.v (τ (σ (((p ^ k : 𝓞 E) : E) * c))) ≤ 1 := by
    push_cast
    simpa only [map_mul, map_pow] using hk
  have b3 := Valuation.map_sub_le _ b1 b2
  rw [add_sub_cancel_right] at b3
  push_cast at b3
  simpa only [map_mul, map_pow, a2, one_pow, one_mul] using b3

end PositivityTheory.ThKG.Tow.Pln

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneComp
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_compl (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (hn : n = n₁ + 2)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1) (hyx : form σ J y x ≠ 0) :
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  let f : (Fin n → E) →ₗ[E] E × E := (formL (σ := σ) J x).prod (formL (σ := σ) J y)
  have hf : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    refine ⟨(a / form σ J y x) • y + b • x, Prod.ext ?_ ?_⟩
    · change form σ J _ x = a
      rw [form_add_left, form_smul_left, form_smul_left, hxx, div_mul_cancel₀ _ hyx, mul_zero, add_zero]
    · change form σ J _ y = b
      rw [form_add_left, form_smul_left, form_smul_left, hyy, hxy, mul_zero, mul_one, zero_add]
  have hk : Module.finrank E (LinearMap.ker f) = n₁ := by
    have := f.finrank_range_add_finrank_ker
    rw [hf, finrank_top] at this
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker f) hk
  let g : (Fin n₁ → E) →ₗ[E] (Fin n → E) := (LinearMap.ker f).subtype ∘ₗ b.equivFun.symm.toLinearMap
  obtain ⟨p, hp⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2
    ((LinearMap.ker f).injective_subtype.comp b.equivFun.symm.injective))
  refine ⟨LinearMap.toMatrix' g, LinearMap.toMatrix' p, by rw [← LinearMap.toMatrix'_comp, hp, LinearMap.toMatrix'_id],
    fun u => ?_, fun z h1 h2 => ?_⟩
  · rw [LinearMap.toMatrix'_mulVec]
    have := (b.equivFun.symm u).2
    exact Prod.mk_eq_zero.1 this
  · refine ⟨b.equivFun ⟨z, Prod.mk_eq_zero.2 ⟨h1, h2⟩⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    change z = (b.equivFun.symm (b.equivFun _) : LinearMap.ker f)
    rw [LinearEquiv.symm_apply_apply]

theorem fg_comap {V W : Type} [AddCommGroup V] [Module (𝓞 E) V] [AddCommGroup W] [Module (𝓞 E) W]
    (f : V →ₗ[𝓞 E] W) (hf : Function.Injective f) (L : Submodule (𝓞 E) W) (hL : L.FG) : (L.comap f).FG :=
  Submodule.fg_of_fg_map_injective f hf (hL.of_le (Submodule.map_comap_le f L))

theorem isLattice_comap (n n₁ : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E) (hP : P * ι = 1) (hL : L.IsFullLattice E) :
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E :=
  Submodule.IsLattice.of_fg E (fg_comap _ (fun u u' e => by
    have := congrArg (P *ᵥ ·) (show ι *ᵥ u = ι *ᵥ u' from e)
    simpa [Matrix.mulVec_mulVec, hP] using this) L hL.fg)

theorem exists_ideal (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsLattice E) (x : Fin n → E) (hx : x ≠ 0) :
    ∃ 𝔟 : FractionalIdeal (𝓞 E)⁰ E, ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ L :=
  ⟨⟨L.comap ((LinearMap.toSpanSingleton E _ x).restrictScalars (𝓞 E)), FractionalIdeal.isFractional_of_fg
    (fg_comap _ (smul_left_injective E hx) L hL.fg)⟩, fun _ => Iff.rfl⟩

end PositivityTheory.ThKG.Tow.Pln

end
end

