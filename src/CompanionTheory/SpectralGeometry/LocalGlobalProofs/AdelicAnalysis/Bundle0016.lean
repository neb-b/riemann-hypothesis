module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramMatrixLocalGlobal
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GramLocal

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

abbrev bcE (E : Type) [Field E] [Algebra F E] (f : R →ₐ[F] S) : R ⊗[F] E →ₐ[F] S ⊗[F] E :=
  Algebra.TensorProduct.map f (AlgHom.id F E)

theorem bcE_inclR (f : R →ₐ[F] S) (e : E) : bcE E f (inclR R e) = inclR S e := by
  simp [inclR, bcE]

theorem bcE_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    bcE E f (sigR R σ z) = sigR S σ (bcE E f z) := by
  induction z with
  | tmul r e => simp [sigR, bcE]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem bcE_hR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x y : Fin M → R ⊗[F] E) :
    bcE E f (hR R σ J x y) = hR S σ J (fun i => bcE E f (x i)) (fun i => bcE E f (y i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, map_mul, bcE_sigR, JR, Matrix.map_apply, bcE_inclR]

theorem bcE_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR S σ J (fun a i => bcE E f (X a i)) = fun a b => bcE E f (gramR R σ J X a b) := by
  funext a b
  simp only [gramR, bcE_hR]

theorem repr_bcE {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E) (f : R →ₐ[F] S)
    (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr (bcE E f z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z with
  | tmul r e => simp [bcE, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem gramR_ratTup (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin n → Fin M → E) :
    gramR R σ J (ratTup R Y) = (gramE σ J Y).map (inclR R) := by
  funext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [gramR, gramE, hR, hE, hform, ratTup, JR, sigR, inclR, map_sum, map_mul]

end Ring

section Adelic

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]

theorem adele_ext (x y : AF F) (h1 : fstA F x = fstA F y)
    (h2 : ∀ v, evalV F v (sndA F x) = evalV F v (sndA F y)) : x = y := by
  refine Prod.ext h1 ?_
  exact Subtype.ext (funext h2)

theorem tensor_ext [Module.Finite F E] (z w : AF F ⊗[F] E)
    (h1 : bcE E (fstA F) z = bcE E (fstA F) w)
    (h2 : ∀ v, bcE E (evalV F v) (bcE E (sndA F) z) = bcE E (evalV F v) (bcE E (sndA F) w)) :
    z = w := by
  classical
  let b := Module.finBasis F E
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext k
  apply adele_ext
  · rw [← repr_bcE, ← repr_bcE, h1]
  · intro v
    rw [← repr_bcE, ← repr_bcE, ← repr_bcE, ← repr_bcE, h2 v]

end Adelic

theorem gram_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : (Fin n → Fin M → AF F ⊗[F] E)) (T : Matrix (Fin n) (Fin n) E), (gramR (AF F) σ J X = T.map (inclR (AF F)) ↔ gramR (Ainf F) σ J (projInf X) = T.map (inclR (Ainf F)) ∧ ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) = T.map (inclR (Fv F v))) ∧ ∀ Y : Fin n → Fin M → E, gramR (AF F) σ J (ratTup (AF F) Y) = (gramE σ J Y).map (inclR (AF F)) := by
  intro F E _ _ _ _ _ σ hCM M J _ n X T
  have hfin : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hInf : gramR (Ainf F) σ J (projInf X) =
      fun a b => bcE E (fstA F) (gramR (AF F) σ J X a b) := bcE_gramR (fstA F) σ J X
  have hFin : gramR (Af F) σ J (projFin X) =
      fun a b => bcE E (sndA F) (gramR (AF F) σ J X a b) := bcE_gramR (sndA F) σ J X
  have hV : ∀ v, gramR (Fv F v) σ J (projV v (projFin X)) =
      fun a b => bcE E (evalV F v) (bcE E (sndA F) (gramR (AF F) σ J X a b)) := by
    intro v
    have := bcE_gramR (evalV F v) σ J (projFin X : Fin n → Fin M → Af F ⊗[F] E)
    rw [hFin] at this
    exact this
  refine ⟨⟨fun h => ⟨?_, fun v => ?_⟩, fun h => ?_⟩, fun Y => gramR_ratTup σ J Y⟩
  · rw [hInf, h]
    funext a b
    simp only [Matrix.map_apply, bcE_inclR]
  · rw [hV v, h]
    funext a b
    simp only [Matrix.map_apply, bcE_inclR]
  · funext a b
    apply tensor_ext
    · have := congrFun (congrFun (hInf.symm.trans h.1) a) b
      simpa only [Matrix.map_apply, bcE_inclR] using this
    · intro v
      have := congrFun (congrFun ((hV v).symm.trans (h.2 v)) a) b
      simpa only [Matrix.map_apply, bcE_inclR] using this

end GlobalTheory.CompanionTheory.SW.GramLocal
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramAlg

section Gen

variable {A : Type} [CommRing A] {M n : ℕ}

def colM (X : Fin n → Fin M → A) : Matrix (Fin M) (Fin n) A := fun i a => X a i

theorem colM_injective : Function.Injective (colM : (Fin n → Fin M → A) → _) := by
  intro X Y h
  funext a i
  exact congrFun (congrFun h i) a

theorem hform_eq_entry (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (X : Fin n → Fin M → A)
    (a b : Fin n) :
    hform s J (X a) (X b) = (cT s (colM X) * J * colM X) a b := by
  simp only [hform, Matrix.mul_apply, cT, colM, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem mul_shape {p q r s t u : Type} [Fintype q] [Fintype r] [Fintype s] [Fintype t]
    (a : Matrix p q A) (b : Matrix q r A) (c : Matrix r s A) (d : Matrix s t A) (e : Matrix t u A) :
    (((a * b : Matrix p r A) * c : Matrix p s A) * (d * e : Matrix s u A) : Matrix p u A) =
      ((a * ((b * c : Matrix q s A) * d : Matrix q t A) : Matrix p t A) * e : Matrix p u A) := by
  simp only [Matrix.mul_assoc]

theorem cT_cT (s : A →+* A) (hs : ∀ x, s (s x) = x) {m p : Type} (B : Matrix m p A) :
    cT s (cT s B) = B := by
  ext i j
  simp [cT, hs]

end Gen

section Conj

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigma_invol [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) :
    σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

variable (R : Type) [CommRing R] [Algebra F R]

theorem sigR_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

variable {M n : ℕ}

theorem gramR_eq (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colM X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colM X := by
  ext a b
  exact hform_eq_entry _ _ X a b

theorem colM_rmul (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colM (rmul R X g) = colM X * g := by
  ext i a
  simp [colM, rmul, Matrix.mul_apply]

theorem colM_actTup (g : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    colM (actTup R g X) = (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * colM X := by
  ext i a
  simp [colM, actTup, Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Conj

theorem gram_algebra : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ), (∀ (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g) ∧ (∀ (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), rmul R (rmul R X g) g' = rmul R X (g * g')) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, rmul R X 1 = X) ∧ (∀ (S : HermR R σ n) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g ∈ HermR R σ n) ∧ ∀ (J' : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) (R ⊗[F] E)), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) = gramR R σ J' X := by
  intro F E _ _ _ _ _ σ hσ M J _ R _ _ n
  have hs : ∀ x : R ⊗[F] E, sigR R σ (sigR R σ x) = x := sigR_invol R (sigma_invol hσ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X g
    rw [gramR_eq, gramR_eq, colM_rmul, cT_mul]
    exact mul_shape _ _ _ _ _
  · intro X g g'
    apply colM_injective
    rw [colM_rmul, colM_rmul, colM_rmul, Matrix.mul_assoc]
  · intro X
    apply colM_injective
    rw [colM_rmul, Matrix.mul_one]
  · intro S g
    have hS : cT (sigR R σ) (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = S := by
      ext a b
      exact S.2 a b
    have key : cT (sigR R σ) (cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g)
        = cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g := by
      rw [cT_mul, cT_mul, cT_cT _ hs, hS, Matrix.mul_assoc]
    intro a b
    exact congrFun (congrFun key a) b
  · intro J' g hJ X
    rw [gramR_eq, gramR_eq, colM_actTup, cT_mul, hJ]
    exact mul_shape _ _ _ _ _

end GlobalTheory.CompanionTheory.SW.GramAlg
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.DetScale

open Matrix
open scoped Pointwise

section Ring

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem measurable_mulVec (A : Matrix ι ι R) :
    Measurable (fun x : ι → R => A *ᵥ x) :=
  (continuous_const.matrix_mulVec continuous_id : Continuous fun x : ι → R => A *ᵥ x).measurable

theorem char_smul_map (lam : Measure R) [lam.IsAddHaarMeasure] (u : Rˣ) :
    distribHaarChar R u • lam.map (fun x => (u : R) * x) = lam := by
  have hm : Measurable fun x : R => (u : R) * x :=
    (continuous_const.mul continuous_id).measurable
  ext S hS
  rw [Measure.smul_apply, Measure.map_apply hm hS]
  have h1 := distribHaarChar_mul lam u ((fun x : R => (u : R) * x) ⁻¹' S)
  have e : u • ((fun x : R => (u : R) * x) ⁻¹' S) = S := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e] at h1
  rw [ENNReal.smul_def, smul_eq_mul]
  exact h1

theorem map_transvection (lam : Measure R) [lam.IsAddHaarMeasure] (i j : ι) (c : R) (hij : i ≠ j) :
    (Measure.pi fun _ : ι => lam).map (fun x => transvection i j c *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  have ht := measurable_mulVec (transvection i j c)
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  simp [transvection, add_mulVec, single_mulVec, hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)]

theorem map_diagonal (lam : Measure R) [lam.IsAddHaarMeasure] (d : ι → Rˣ) :
    distribHaarChar R (∏ i, d i) •
        (Measure.pi fun _ : ι => lam).map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.smul_apply, Measure.map_apply (measurable_mulVec _) (MeasurableSet.univ_pi hs)]
  have h1 : (fun x : ι → R => diagonal (fun i => (d i : R)) *ᵥ x) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i => (fun y : R => (d i : R) * y) ⁻¹' s i := by
    ext f
    simp [mulVec_diagonal]
  have hm : ∀ i, Measurable fun x : R => (d i : R) * x := fun i =>
    (continuous_const.mul continuous_id).measurable
  rw [h1, Measure.pi_pi, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 := congrArg (fun m : Measure R => m (s i)) (char_smul_map lam (d i))
  simp only [Measure.smul_apply, Measure.map_apply (hm i) (hs i)] at h2
  rw [← h2]
  rfl

end Ring

theorem smul_map_pi {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    {ι : Type} [Fintype ι] [DecidableEq ι] (lam : Measure R) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι F) (h : A.det ≠ 0) :
    distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  let u : Fˣ →* Rˣ := Units.map (algebraMap F R : F →* R)
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun A : Matrix ι ι F => ∀ h : A.det ≠ 0, distribHaarChar R (u (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam) A h ?_ ?_ ?_ h
  · intro D hD h
    have hD' : ∀ i, D i ≠ 0 := fun i => by
      rw [det_diagonal] at hD
      exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
    have e1 : u (Units.mk0 (diagonal D).det h) = ∏ i, u (Units.mk0 (D i) (hD' i)) := by
      rw [← map_prod]
      congr 1
      ext
      simp [det_diagonal]
    have e2 : (diagonal D).map (algebraMap F R) =
        diagonal fun i => ((u (Units.mk0 (D i) (hD' i)) : Rˣ) : R) := by
      ext a b
      by_cases hab : a = b
      · subst hab
        simp [u]
      · simp [u, hab]
    rw [e1, e2]
    exact map_diagonal lam _
  · intro t h
    obtain ⟨i, j, hij, c⟩ := t
    have e1 : u (Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h) = 1 := by
      rw [show Units.mk0 (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩).det h = 1 from
        Units.ext (by simpa [TransvectionStruct.toMatrix] using det_transvection_of_ne i j hij c), map_one]
    have e2 : (TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ : Matrix ι ι F).map (algebraMap F R) =
        transvection i j (algebraMap F R c) := by
      ext a b
      simp [TransvectionStruct.toMatrix, transvection, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, apply_ite (algebraMap F R)]
    rw [e1, e2, map_one, one_smul]
    exact map_transvection lam i j _ hij
  · intro A B hA hB IHA IHB h
    have e1 : Units.mk0 (A * B).det h = Units.mk0 A.det hA * Units.mk0 B.det hB :=
      Units.ext (by simp [det_mul])
    have e2 : (fun x : ι → R => (A * B).map (algebraMap F R) *ᵥ x) =
        (fun x => A.map (algebraMap F R) *ᵥ x) ∘ (fun x => B.map (algebraMap F R) *ᵥ x) := by
      ext1 x
      simp [Matrix.map_mul, mulVec_mulVec]
    rw [e1, e2, map_mul, map_mul, mul_smul,
      ← Measure.map_map (measurable_mulVec _) (measurable_mulVec _),
      ← Measure.map_smul _ (measurable_mulVec _).aemeasurable, IHB hB]
    exact IHA hA

theorem map_mulVec_eq_smul : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type)
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R),
    lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam →
    ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure →
      μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by
  intro F _ R _ _ _ _ _ _ _ _ _ ι _ _ A hA lam hlam c hc μ hμ
  have h1 := smul_map_pi lam A hA
  have h2 := char_smul_map lam (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  set d := distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det hA))
  have h2' : d • lam.map (fun x => algebraMap F R A.det * x) = lam := h2
  rw [hc] at h2'
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set R, IsCompact K ∧ K ∈ 𝓝 (0 : R) := exists_compact_mem_nhds 0
  have hdc : d * c = 1 := by
    have h3 := congrArg (fun m : Measure R => m K) h2'
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    rw [← mul_assoc, ← ENNReal.coe_mul] at h3
    have h4 : ((d * c : ℝ≥0) : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds lam hK0).ne' hKc.measure_lt_top.ne).1
        (h3.trans (one_mul _).symm)
    exact_mod_cast h4
  have h4 : (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      c • Measure.pi fun _ : ι => lam := by
    conv_rhs => rw [← h1]
    rw [smul_smul, mul_comm c d, hdc, one_smul]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • Measure.pi fun _ : ι => lam :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular μ (Measure.pi fun _ : ι => lam)⟩
  rw [hk, Measure.map_smul _ (measurable_mulVec _).aemeasurable, h4, smul_comm]

end GlobalTheory.CompanionTheory.SW.DetScale
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermTop

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_sigR {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, h]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR]

theorem gramR_mem {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) {n M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, hform, JR, Matrix.map_apply, map_sum, map_mul, sigR_sigR R h, sigR_inclR, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

theorem isTopRing [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI := isModTop (F := F) (E := E) R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem exists_homeo [Module.Finite F E] :
    Nonempty ((R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

theorem continuous_sigR [Module.Finite F E] (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

end

theorem herm_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ n : ℕ, LocallyCompactSpace (HermR R σ n) ∧ SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) ∧ BorelSpace (HermR R σ n) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ g : (Fin n → Fin M → R ⊗[F] E) → HermR R σ n, Continuous g ∧ ∀ X, gramR R σ J X = (g X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ n
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  haveI := isTopRing (F := F) (E := E) R
  obtain ⟨e⟩ := exists_homeo (F := F) (E := E) R
  haveI : LocallyCompactSpace (R ⊗[F] E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (R ⊗[F] E) := e.secondCountableTopology
  haveI : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  have hs := continuous_sigR R σ
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R ⊗[F] E))
  have hc : IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
        ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
      ext S
      simp only [Set.mem_iInter]
      rfl
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact hs.comp (continuous_id.matrix_elem b a)
    · exact continuous_id.matrix_elem a b
  refine ⟨hc.locallyCompactSpace, ?_, inferInstance, ⟨rfl⟩, ?_⟩
  · exact TopologicalSpace.Subtype.secondCountableTopology _
  · intro M J hJ
    refine ⟨fun X => ⟨gramR R σ J X, gramR_mem R (sigma_sigma hσ) hJ.1 X⟩, ?_, fun _ => rfl⟩
    refine Continuous.subtype_mk ?_ _
    refine continuous_matrix fun a b => ?_
    simp only [gramR, hR, hform]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    refine ((hs.comp ?_).mul continuous_const).mul ?_
    · exact (continuous_apply i).comp (continuous_apply a)
    · exact (continuous_apply j).comp (continuous_apply b)

end GlobalTheory.CompanionTheory.SW.HermTop
end

