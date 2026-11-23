module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorLatticeAtPlaceIffFrameCoordinatesIntegr
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame.Lat

theorem mem_of_bil {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (g : A →+ B →+ C)
    {SA : Set A} {SB : Set B} {T : AddSubgroup C} (h : ∀ a ∈ SA, ∀ b ∈ SB, g a b ∈ T) {a : A} {b : B}
    (ha : a ∈ AddSubgroup.closure SA) (hb : b ∈ AddSubgroup.closure SB) : g a b ∈ T := by
  induction ha using AddSubgroup.closure_induction with
  | mem a ha =>
    induction hb using AddSubgroup.closure_induction with
    | mem b hb => exact h a ha b hb
    | zero => simpa using T.zero_mem
    | add b b' _ _ h1 h2 => simpa using T.add_mem h1 h2
    | neg b _ h1 => simpa using T.neg_mem h1
  | zero => simpa using T.zero_mem
  | add a a' _ _ h1 h2 => simpa using T.add_mem h1 h2
  | neg a _ h1 => simpa using T.neg_mem h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intAt (v : Pl (F := F)) : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
    evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}

theorem at_mul {v : Pl (F := F)} {a : AF F} (b : AF F) (ha : At (evFin F v) a) : At (evFin F v) (a * b) := by
  intro u hu
  have h := ha u hu
  rw [smul_eq_mul] at h ⊢
  rw [← mul_assoc, h, zero_mul]

theorem int_mul {v : Pl (F := F)} {a b : AF F} (ha : evFin F v a ∈ v.adicCompletionIntegers F)
    (hb : evFin F v b ∈ v.adicCompletionIntegers F) : evFin F v (a * b) ∈ v.adicCompletionIntegers F := by
  rw [map_mul]
  exact mul_mem ha hb

def smulHom (n : ℕ) : AE F E →+ (Fin n → AE F E) →+ (Fin n → AE F E) :=
  AddMonoidHom.mk' (fun c => DistribSMul.toAddMonoidHom _ c)
    (fun c c' => AddMonoidHom.ext fun x => by funext i; simp [add_mul])

theorem smul_mem_latAt {v : Pl (F := F)} {n : ℕ} (X : Spc F E n) {c : AE F E} (hc : c ∈ intAt v) {x : Fin n → AE F E}
    (hx : x ∈ GlobalTheory.InertSph.latAt X v) : c • x ∈ GlobalTheory.InertSph.latAt X v := by
  refine mem_of_bil (smulHom n) ?_ hc hx
  rintro _ ⟨b, hb, hbi, o, rfl⟩ _ ⟨a, ha, hai, y, hy, rfl⟩
  refine AddSubgroup.subset_closure ⟨b * a, at_mul a hb, int_mul hbi hai, o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
  simp only [smulHom, AddMonoidHom.mk'_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_mul, ho]
  ring

theorem smul_incl_mem_latAt {v : Pl (F := F)} {n : ℕ} (X : Spc F E n) {c : AE F E} (hc : c ∈ intAt v) {y : Fin n → E}
    (hy : y ∈ X.L) : (c • fun i => inclR (F := F) (AF F) (y i)) ∈ GlobalTheory.InertSph.latAt X v := by
  refine mem_of_bil (smulHom n) (SB := {fun i => inclR (F := F) (AF F) (y i)}) ?_ hc (AddSubgroup.subset_closure rfl)
  rintro _ ⟨b, hb, hbi, o, rfl⟩ _ rfl
  refine AddSubgroup.subset_closure ⟨b, hb, hbi, o • y, X.L.smul_mem o hy, ?_⟩
  funext i
  have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
  simp only [smulHom, AddMonoidHom.mk'_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, map_mul, ho]
  ring

theorem vecMulVec_mem {v : Pl (F := F)} {n d : ℕ} (X : Spc F E n) (W : Spc F E d) {x : Fin n → AE F E} {y : Fin d → AE F E}
    (hx : x ∈ GlobalTheory.InertSph.latAt X v) (hy : y ∈ GlobalTheory.InertSph.latAt W v) : Matrix.vecMulVec x y ∈ latAtV X W v := by
  let g : (Fin n → AE F E) →+ (Fin d → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Matrix.vecMulVec x y)
        (fun y y' => by ext i j; simp [Matrix.vecMulVec_apply, mul_add]))
      (fun x x' => AddMonoidHom.ext fun y => by ext i j; simp [Matrix.vecMulVec_apply, add_mul])
  refine mem_of_bil g ?_ hx hy
  rintro _ ⟨a, ha, hai, x0, hx0, rfl⟩ _ ⟨b, hb, hbi, y0, hy0, rfl⟩
  refine AddSubgroup.subset_closure ⟨a * b, at_mul b ha, int_mul hai hbi, x0, hx0, y0, hy0, ?_⟩
  ext i j
  simp only [g, AddMonoidHom.mk'_apply, Matrix.vecMulVec_apply, incM, Matrix.smul_apply, Matrix.map_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [Algebra.smul_def, map_mul]
  ring

end GlobalTheory.InertLocFrame.Lat

namespace GlobalTheory.InertLocFrame


open GlobalTheory.InertLocFrame.Lat in
theorem mem_latAtV_iff_xm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ AE F E),
      Function.Injective ι → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : AE F E | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L), (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PV : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) → (∀ x : Fin d → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PW : Matrix (Fin d) (Fin d) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z, z ∈ latAtV X W v ↔ ∃ u : Matrix (Fin d) (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
        GlobalTheory.InertLocFrame.xm ι PV PW u = z := by
  intro F E _ _ _ _ _ v n d X W L _ _ ι hinj hsupp hmul hint PV PW hPV hPW z
  have hsing : ∀ {m : ℕ} (j i : Fin m), (Pi.single j (1 : L) : Fin m → L) i ∈ Formalism.UG.intL L := by
    intro m j i
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
      have h1 : ι 1 ∈ Lat.intAt (E := E) v := (hint 1).1 (one_mem _)
      have h1s : At (evFin F v) (ι 1) := (hsupp _).2 ⟨1, rfl⟩
      let X' : Fin n → AE F E := a • fun i => inclR (F := F) (AF F) (x i)
      let Y' : Fin d → AE F E := ι 1 • fun k => inclR (F := F) (AF F) (y k)
      have hX'm : X' ∈ GlobalTheory.InertSph.latAt X v := AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
      have hY'm : Y' ∈ GlobalTheory.InertSph.latAt W v := Lat.smul_incl_mem_latAt W h1 hy
      have hX's : ∀ i, ∃ t, ι t = X' i := fun i => (hsupp _).1 fun u hu => by
        show u • (a • inclR (F := F) (AF F) (x i)) = 0
        rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      have hY's : ∀ k, ∃ t, ι t = Y' k := fun k => (hsupp _).1 fun u hu => by
        show u • (ι 1 * inclR (F := F) (AF F) (y k)) = 0
        rw [← smul_mul_assoc, h1s u hu, zero_mul]
      let xt : Fin n → L := fun i => pre ι (X' i)
      let yt : Fin d → L := fun k => pre ι (Y' k)
      have hxt : ∀ i, ι (xt i) = X' i := fun i => pre_spec ι (hX's i)
      have hyt : ∀ k, ι (yt k) = Y' k := fun k => pre_spec ι (hY's k)
      let c : Fin n → L := ((PV⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ xt
      let c' : Fin d → L := ((PW⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) *ᵥ yt
      have hPc : (PV : Matrix (Fin n) (Fin n) L) *ᵥ c = xt := by
        simp only [c]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      have hPc' : (PW : Matrix (Fin d) (Fin d) L) *ᵥ c' = yt := by
        simp only [c']
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      have hc : ∀ i, c i ∈ Formalism.UG.intL L := (hPV c).2 (by
        rw [hPc]
        convert hX'm using 1
        funext i
        exact hxt i)
      have hc' : ∀ k, c' k ∈ Formalism.UG.intL L := (hPW c').2 (by
        rw [hPc']
        convert hY'm using 1
        funext k
        exact hyt k)
      refine ⟨Matrix.vecMulVec c' c, fun i j => mul_mem (hc' i) (hc j), ?_⟩
      ext i k
      rw [xm_apply, Matrix.map_apply]
      have e1 : ((PV : Matrix (Fin n) (Fin n) L) * (Matrix.vecMulVec c' c)ᵀ * (PW : Matrix (Fin d) (Fin d) L)ᵀ) i k = xt i * yt k := by
        rw [← hPc, ← hPc']
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
          Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      have e2 : ι 1 * X' i = X' i := by rw [← hxt i, ← hmul, one_mul]
      rw [e1, hmul, hxt, hyt]
      show X' i * (ι 1 * inclR (F := F) (AF F) (y k)) = (a • incM F (Matrix.vecMulVec x y)) i k
      rw [← mul_assoc, mul_comm (X' i), e2]
      simp only [X', incM, Matrix.smul_apply, Matrix.map_apply, Matrix.vecMulVec_apply, Pi.smul_apply, map_mul,
        smul_mul_assoc]
    | zero => exact ⟨0, fun _ _ => zero_mem _, map_zero _⟩
    | add z z' _ _ h h' =>
      obtain ⟨u, hu, rfl⟩ := h
      obtain ⟨u', hu', rfl⟩ := h'
      exact ⟨u + u', fun i j => add_mem (hu i j) (hu' i j), map_add _ _ _⟩
    | neg z _ h =>
      obtain ⟨u, hu, rfl⟩ := h
      exact ⟨-u, fun i j => neg_mem (hu i j), map_neg _ _⟩
  · rintro ⟨u, hu, rfl⟩
    have e : xm ι PV PW u = ∑ j, ∑ l, Matrix.vecMulVec (ι (u l j) • fun i => ι ((PV : Matrix _ _ L) i j))
        (fun k => ι ((PW : Matrix _ _ L) k l)) := by
      ext i k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [xm_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_sum, hmul]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    refine sum_mem fun j _ => sum_mem fun l _ => Lat.vecMulVec_mem X W (Lat.smul_mem_latAt X ((hint _).1 (hu l j)) ?_) ?_
    · have h := (hPV (Pi.single j 1)).1 (hsing j)
      simpa [Matrix.mulVec_single_one] using h
    · have h := (hPW (Pi.single l 1)).1 (hsing l)
      simpa [Matrix.mulVec_single_one] using h

end GlobalTheory.InertLocFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSquareLinearFactorOfPencilLineDiscriminantNeZ
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

def lineSubst {K : Type} [Field K] {N : ℕ} (a b : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K →ₐ[K] Polynomial K :=
  aeval fun p : Fin 1 × Fin N => Polynomial.C (a p.2) + Polynomial.C (b p.2) * Polynomial.X

theorem line_eq_lineSubst {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (a b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    line s a b f = lineSubst a b (spec s f) := by
  simp only [line, spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C, lineSubst]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K),
      IsScalarTower.algebraMap_apply F K (Polynomial K), AlgHom.commutes]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join, lineSubst]

theorem eval_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) = aeval (join s b) f := by
  simp only [spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K)]
    simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join]

theorem lineSubst_lin {K : Type} [Field K] {N : ℕ} (a b y : Fin N → K) :
    lineSubst a b (lin y) = Polynomial.C (∑ j, a j * y j) + Polynomial.C (∑ j, b j * y j) * Polynomial.X := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, lineSubst, map_sum, map_mul, aeval_X, aeval_C, Polynomial.algebraMap_eq, add_mul,
    Finset.sum_add_distrib, Polynomial.C_mul, Finset.sum_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eval_lin {K : Type} [Field K] {N : ℕ} (b y : Fin N → K) :
    eval (fun p : Fin 1 × Fin N => b p.2) (lin y) = ∑ j, b j * y j := by
  simp [lin]

theorem coeff_ne_zero_of_resultant_ne_zero {K : Type} [Field K] {δ : ℕ} (hδ : 1 ≤ δ) (P : Polynomial K)
    (hP : P.natDegree ≤ δ) (h : Polynomial.resultant P (Polynomial.derivative P) δ (δ - 1) ≠ 0) : P.coeff δ ≠ 0 := by
  by_contra hc
  apply h
  have hlt : P.natDegree < δ := by
    rcases hP.lt_or_eq with h1 | h1
    · exact h1
    exfalso
    by_cases hP0 : P = 0
    · rw [hP0, Polynomial.natDegree_zero] at h1
      omega
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp (by rw [Polynomial.leadingCoeff, h1]; exact hc))
  rcases Nat.lt_or_ge δ 2 with h2 | h2
  · obtain rfl : δ = 1 := by omega
    have hd : Polynomial.derivative P = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero (by omega : P.natDegree = 0), Polynomial.derivative_C]
    simp [hd]
  · apply Polynomial.resultant_eq_zero_of_lt_lt _ _ _ _ hlt
    calc (Polynomial.derivative P).natDegree ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le P
      _ < δ - 1 := by omega

theorem noSquare_spec_of_disc_ne_zero : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (s : Fin D → Fin N → K) (a b : Fin N → K), 1 ≤ δ → (GlobalTheory.PencilDisc.line s a b f).natDegree ≤ δ → (GlobalTheory.PencilDisc.line s a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join s b) f → GlobalTheory.PencilDisc.disc δ s a b f ≠ 0 → GlobalTheory.HSChoice.NoSquare (GlobalTheory.HSChoice.spec s f) := by
  intro F K _ _ _ D N δ f s a b hδ hdeg hcoeff hdisc
  have hres : (line s a b f).resultant (Polynomial.derivative (line s a b f)) δ (δ - 1) ≠ 0 := hdisc
  have hc : (line s a b f).coeff δ ≠ 0 := coeff_ne_zero_of_resultant_ne_zero hδ _ hdeg hres
  have hspec0 : eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) ≠ 0 := by
    rw [eval_spec, ← hcoeff]
    exact hc
  refine ⟨fun h0 => hspec0 (by rw [h0, map_zero]), fun y _ hdvd => ?_⟩
  obtain ⟨q, hq⟩ := hdvd
  by_cases hβ : ∑ j, b j * y j = 0
  · apply hspec0
    rw [hq, map_mul, map_pow, eval_lin, hβ]
    simp
  · have hnat : (line s a b f).natDegree = δ :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hc
    have hP0 : line s a b f ≠ 0 := fun h0 => hc (by rw [h0, Polynomial.coeff_zero])
    have hcop : IsCoprime (line s a b f) (Polynomial.derivative (line s a b f)) := by
      by_contra hnc
      apply hres
      have hd' : (Polynomial.derivative (line s a b f)).natDegree ≤ δ - 1 := by
        rw [← hnat]
        exact Polynomial.natDegree_derivative_le _
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd'
      rw [hk, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, ← hnat,
        Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hP0, hnc⟩, mul_zero]
    have hQ : line s a b f = lineSubst a b (lin y) * lineSubst a b (lin y) * lineSubst a b q := by
      rw [line_eq_lineSubst, hq, map_mul, map_pow, sq]
    have h1 : lineSubst a b (lin y) ∣ line s a b f :=
      ⟨lineSubst a b (lin y) * lineSubst a b q, by rw [hQ]; ring⟩
    have h2 : lineSubst a b (lin y) ∣ Polynomial.derivative (line s a b f) := by
      refine ⟨Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        lineSubst a b (lin y) * Polynomial.derivative (lineSubst a b q), ?_⟩
      rw [hQ, Polynomial.derivative_mul, Polynomial.derivative_mul]
      ring
    have hu := hcop.isUnit_of_dvd' h1 h2
    rw [lineSubst_lin] at hu
    have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [add_comm, Polynomial.natDegree_linear hβ] at hdeg0
    exact one_ne_zero hdeg0

end GlobalTheory.PencilDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumConsEqMulOfEffectiveDivisorSuppSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagPush.Dbl

theorem num_cons_eq_mul_of_supp_eq_range : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ Θ : CartierDiv W.Z, Θ.Eff → (Θ.supp : Set W.Z) = Set.range W.δ → ∃ μ : ℤ, μ ≠ 0 ∧ ∀ y : Fin Y.dim → CartierDiv W.Z, letI := algebraΓOfHom (W.p₁ ≫ Y.str); W.num (Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) = μ * interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) fun i => toLB (y i) := by
  intro F _ Y W hW Θ hΘ hsupp
  letI := algebraΓOfHom (W.p₁ ≫ Y.str)
  have hstr : strHom F W.Z = W.p₁ ≫ Y.str := GlobalTheory.strHom_eq fun _ => rfl
  have hp : IsProjOver (strHom F (X := W.Z)) := hstr ▸ W.proj
  have : IsLocallyNoetherian W.Z := by
    obtain ⟨N, ι, _, h⟩ := hp
    have : LocallyOfFiniteType (strHom F (X := W.Z)) := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian (strHom F W.Z)
  obtain ⟨s, hs, e⟩ := GlobalTheory.RatSecCycle.exists_sec_divOfSec_eq Θ hΘ
  set η := genericPoint Y.X
  set w₀ := W.δ η
  have hδ := W.δ.isClosedEmbedding
  have hcl : closure ({w₀} : Set W.Z) = Set.range W.δ := by
    rw [← Set.image_singleton, hδ.closure_image_eq, (genericPoint_spec Y.X).def, Set.image_univ]
  have hd : topologicalKrullDim (closure ({w₀} : Set W.Z)) = Y.dim := by
    rw [topologicalKrullDim_eq_of_isEmbedding hδ.isEmbedding hcl.symm, Y.topologicalKrullDim_eq]
  have hw₀ : w₀ ∈ Θ.supp := by
    show w₀ ∈ (Θ.supp : Set W.Z); rw [hsupp]; exact ⟨η, rfl⟩
  have hmax : ¬ IsMax w₀ := fun h =>
    Θ.genericPoint_notMem_supp ((h (genericPoint_specializes w₀)).mem_closed Θ.supp.isClosed hw₀)
  have hc := GlobalTheory.SecCycle.coheight_eq_one_of_dim_closure hW hmax hd
  refine ⟨Θ.mult w₀, ?_, fun y => ?_⟩
  · have hws : w₀ ∉ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s := fun h =>
      (GlobalTheory.Cartier.notMem_supp_divOfSec.2 h) (e.symm ▸ hw₀)
    have := GlobalTheory.SecCycle.mult_divOfSec_ne_zero (isLB_toLB Θ) s hs hc hws
    rwa [e] at this
  · have hcons : (fun i => toLB ((Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) i)) =
        (Fin.cons (toLB Θ) (fun i => toLB (y i)) : Fin (Y.dim + 1) → LB W.Z) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hF := GlobalTheory.SecCycle.interNum_cons_eq_finsum_mult F W.Z hp Y.dim hW (toLB Θ)
      (isLB_toLB Θ) (fun i => toLB (y i)) (fun i => isLB_toLB (y i)) s hs
    rw [e] at hF
    show interNum F (structureModule W.Z) _ = _
    rw [hcons, hF]
    refine finsum_eq_single _ w₀ fun w hw => ?_
    by_cases hm : Θ.mult w = 0
    · rw [hm, zero_mul]
    obtain ⟨y', rfl⟩ : w ∈ Set.range W.δ := by
      rw [← hsupp]; exact CartierDiv.mem_supp_of_mult_ne_zero hm
    have hy' : y' ≠ η := fun h => hw (by rw [h])
    have hnot : w₀ ∉ closure ({W.δ y'} : Set W.Z) := fun h => by
      have h1 : W.δ y' ⤳ W.δ η := specializes_iff_mem_closure.2 h
      have h2 : y' ⤳ η := hδ.isInducing.specializes_iff.1 h1
      exact hy' (h2.antisymm (genericPoint_specializes y')).eq
    have hsp : w₀ ⤳ W.δ y' := specializes_iff_mem_closure.2 (hcl.symm ▸ ⟨y', rfl⟩ : W.δ y' ∈ closure ({w₀} : Set W.Z))
    have h1 : topologicalKrullDim (closure ({W.δ y'} : Set W.Z)) + 1 ≤ topologicalKrullDim (closure ({w₀} : Set W.Z)) :=
      topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun z hz =>
        ⟨w₀, subset_closure rfl, hnot, hsp.trans (specializes_iff_mem_closure.2 hz)⟩
    rw [hd] at h1
    have hlt : topologicalKrullDim (closure ({W.δ y'} : Set W.Z)) < (Fintype.card (Fin Y.dim) : ℕ) := by
      rw [Fintype.card_fin]; exact GlobalTheory.SheafCycle.lt_of_add_one_le_natCast h1
    rw [GlobalTheory.SheafCycle.interNumRed_eq_zero F hp (fun i => isLB_toLB (y i)) _ hlt, mul_zero]

end GlobalTheory.FlagPush.Dbl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PencilLinePolynomialNatDegreeLeAndCoeff
section
set_option autoImplicit false

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

theorem prod_pow_natDegree_le_and_coeff {R ι : Type} [CommRing R] (s : Finset ι) (v : ι → Polynomial R) (w m : ι → ℕ)
    (h : ∀ p, (v p).natDegree ≤ w p) :
    (∏ p ∈ s, v p ^ m p).natDegree ≤ ∑ p ∈ s, m p * w p ∧
      (∏ p ∈ s, v p ^ m p).coeff (∑ p ∈ s, m p * w p) = ∏ p ∈ s, (v p).coeff (w p) ^ m p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    have h1 : (v p ^ m p).natDegree ≤ m p * w p :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (h p))
    rw [Finset.prod_insert hp, Finset.sum_insert hp, Finset.prod_insert hp]
    refine ⟨Polynomial.natDegree_mul_le.trans (add_le_add h1 ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih.1, ih.2,
      Polynomial.coeff_pow_of_natDegree_le (h p)]

theorem line_natDegree_le_and_coeff (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (u : Fin D → Fin N → R) (a b : Fin N → R) :
    (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧
      (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  classical
  set v : Fin (D + 1) × Fin N → Polynomial R :=
    join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X with hv
  let w : Fin (D + 1) × Fin N → ℕ := fun p => if p.1 = Fin.last D then 1 else 0
  have hdeg : ∀ p, (v p).natDegree ≤ w p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [hv, w, join, if_true, Fin.lastCases_last]
      rw [add_comm]
      exact Polynomial.natDegree_linear_le
    · simp [hv, w, join]
  have hco : ∀ p, (v p).coeff (w p) = join u b p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [hv, w, join]
    · simp [hv, w, join]
  have hsum : ∀ m ∈ f.support, ∑ p, m p * w p = δ := by
    intro m hm
    have := hf m (by simpa using hm) (Fin.last D)
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa [w] using this
    · intro i _ hi
      simp [w, hi]
    · simp
  have hkey : ∀ m ∈ f.support, (∏ p, v p ^ m p).natDegree ≤ δ ∧
      (∏ p, v p ^ m p).coeff δ = ∏ p, join u b p ^ m p := by
    intro m hm
    have := prod_pow_natDegree_le_and_coeff Finset.univ v w m hdeg
    rw [hsum m hm] at this
    simpa only [hco] using this
  have hline : line u a b f =
      ∑ m ∈ f.support, Polynomial.C (algebraMap F R (f.coeff m)) * ∏ p, v p ^ m p := by
    rw [line, ← hv, aeval_def, eval₂_eq']
    rfl
  rw [hline, aeval_def, eval₂_eq']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm =>
    (Polynomial.natDegree_C_mul_le _ _).trans (hkey m hm).1, ?_⟩
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Polynomial.coeff_C_mul, (hkey m hm).2]

end GlobalTheory.PencilDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientIntegralRowReductionStatement
section
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_deficient_integral_row_reduction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (X : Matrix A D k), X.rank < Fintype.card A → ∃ g ∈ GlobalTheory.SplitWeil.KO k A, ∃ i₀ : A, ∀ j, (g.val * X) i₀ j = 0 := by
  first | exact @GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt | exact GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt | (intros; apply GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt <;> assumption)
end

