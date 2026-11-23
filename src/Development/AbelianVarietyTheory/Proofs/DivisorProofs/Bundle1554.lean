module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceZeroAdeleUnitLatticeAtInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSph.Scal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem disc_sub_sq_notMem (v : Pl (F := F)) (b c t : 𝓞 F) (h2 : (2 : 𝓞 F) ∉ v.asIdeal)
    (hroot : ∀ r : 𝓞 F, r ^ 2 + b * r + c ∉ v.asIdeal) : t ^ 2 - (b ^ 2 - 4 * c) ∉ v.asIdeal := by
  intro h
  obtain ⟨s, a, ha, hs⟩ := v.isMaximal.exists_inv h2
  apply hroot (s * (t - b))
  have h4 : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) ∈ v.asIdeal := by
    have e : (2 : 𝓞 F) * (2 * ((s * (t - b)) ^ 2 + b * (s * (t - b)) + c)) =
        (t ^ 2 - (b ^ 2 - 4 * c)) + a * ((t - b) * (a * (t - b) - 2 * t)) := by
      have : a = 1 - s * 2 := by linear_combination hs
      subst this
      ring
    rw [e]
    exact add_mem h (Ideal.mul_mem_right _ _ ha)
  exact ((v.isPrime.mem_or_mem ((v.isPrime.mem_or_mem h4).resolve_left h2)).resolve_left h2)

theorem exists_delta (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E))
    (hin : Formalism.UG.IsInertAt F E v w) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    ∃ (δ : 𝓞 E) (D : 𝓞 F), σ (δ : E) = -(δ : E) ∧ (δ : E) * δ = algebraMap F E (D : F) ∧ D ∉ v.asIdeal ∧
      1 - D ∉ v.asIdeal := by
  have hp : (v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime := by
    rw [show v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = w.asIdeal from hin]
    exact w.isPrime
  obtain ⟨a, b, c, hq, hc, hroot⟩ := GlobalTheory.InertUnitNorm.exists_integral_gen σ hσ v hp
  have hδ : ((2 * a + algebraMap (𝓞 F) (𝓞 E) b : 𝓞 E) : E) = 2 * (a : E) + algebraMap F E (b : F) := rfl
  have hD : ((b ^ 2 - 4 * c : 𝓞 F) : F) = (b : F) ^ 2 - 4 * (c : F) := rfl
  refine ⟨2 * a + algebraMap (𝓞 F) (𝓞 E) b, b ^ 2 - 4 * c, ?_, ?_, ?_, ?_⟩
  · rw [hδ, map_add (f := _), map_mul, map_ofNat, AlgHom.commutes, hc]
    ring
  · rw [hδ, hD, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hq
  · intro h
    apply disc_sub_sq_notMem v b c 0 h2 hroot
    simpa using neg_mem h
  · simpa using disc_sub_sq_notMem v b c 1 h2 hroot

theorem exists_inv (v : Pl (F := F)) (D : 𝓞 F) (hD : D ∉ v.asIdeal) :
    ∃ c : Fv F v, c ∈ v.adicCompletionIntegers F ∧ c * algebraMap F (Fv F v) (D : F) = 1 := by
  have h1 : Valued.v (algebraMap F (Fv F v) (D : F)) = 1 := by
    have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (D : F)
    have h' : v.valuation F (D : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hD
    rw [← h', ← h]
    rfl
  have h0 : algebraMap F (Fv F v) (D : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  refine ⟨(algebraMap F (Fv F v) (D : F))⁻¹, ?_, inv_mul_cancel₀ h0⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h1, inv_one]

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl (F := F)} {z : M} (hz : At (evFin F v) z)
    {a : AF F} (ha : evFin F v a = 1) : a • z = z := by
  have h := hz (a - 1) (by rw [map_sub, map_one, ha, sub_self])
  rwa [sub_smul, one_smul, sub_eq_zero] at h

theorem at_of_mem_latAt {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    At (evFin F v) z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    intro u hu
    rw [smul_smul, ← smul_eq_mul u a, ha u hu, zero_smul]
  | zero => intro u _; exact smul_zero u
  | add x y _ _ hx hy => intro u hu; rw [smul_add, hx u hu, hy u hu, add_zero]
  | neg x _ hx => intro u hu; rw [smul_neg, hx u hu, neg_zero]

theorem lift_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F)
    (o : 𝓞 E) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    (GlobalTheory.LatVac.liftV v c • inclR (F := F) (AF F) (o : E)) • z ∈ latAt W v :=
  GlobalTheory.InertLocFrame.Lat.smul_mem_latAt W (AddSubgroup.subset_closure
    ⟨_, GlobalTheory.LatVac.at_liftV v c, by rwa [GlobalTheory.LatVac.evFin_liftV], o, rfl⟩) hz

end GlobalTheory.InertSph.Scal

namespace GlobalTheory.InertSph


open GlobalTheory.InertSph.Scal GlobalTheory.LatVac in
theorem exists_traceZero_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ β b up um : AE F E, At (evFin F v) β ∧ cA σ β = -β ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      β • z ∈ GlobalTheory.InertSph.latAt W v ∧ b • z ∈ GlobalTheory.InertSph.latAt W v ∧ up • z ∈ GlobalTheory.InertSph.latAt W v ∧
      um • z ∈ GlobalTheory.InertSph.latAt W v ∧ (β * b) • z = z ∧ ((1 + β) * up) • z = z ∧ ((1 - β) * um) • z = z := by
  intro F E _ _ _ _ _ σ B hB d W v w hin
  obtain ⟨δ, D, hσ, hsq, hD, hD1⟩ := exists_delta σ hB.cm v w hin (hB.inert v w hin).1
  obtain ⟨c, hc, hcD⟩ := exists_inv v D hD
  obtain ⟨c', hc', hcD'⟩ := exists_inv v (1 - D) hD1
  have hcD'' : c' * (1 - algebraMap F (Fv F v) (D : F)) = 1 := by
    rwa [show ((1 - D : 𝓞 F) : F) = 1 - (D : F) from rfl, map_sub, map_one] at hcD'
  set x : AE F E := inclR (F := F) (AF F) (δ : E) with hx
  have hxx : x * x = algebraMap (AF F) (AE F E) (algebraMap F (AF F) (D : F)) := by
    rw [hx, ← map_mul, hsq, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).commutes _
  have hp : inclR (F := F) (AF F) ((1 + δ : 𝓞 E) : E) = 1 + x := by
    rw [show ((1 + δ : 𝓞 E) : E) = 1 + (δ : E) from rfl, map_add (f := _), map_one]
  have hm : inclR (F := F) (AF F) ((1 - δ : 𝓞 E) : E) = 1 - x := by
    rw [show ((1 - δ : 𝓞 E) : E) = 1 - (δ : E) from rfl, map_sub, map_one]
  have he : liftV v (1 : Fv F v) * liftV v c' = liftV v c' :=
    smul_eq_of_at (at_liftV v c') (evFin_liftV v 1)
  have he' : algebraMap (AF F) (AE F E) (liftV v (1 : Fv F v)) * algebraMap (AF F) (AE F E) (liftV v c') =
      algebraMap (AF F) (AE F E) (liftV v c') := by rw [← map_mul, he]
  have key : ∀ z ∈ latAt W v, ∀ a : AF F, evFin F v a = 1 → algebraMap (AF F) (AE F E) a • z = z := by
    intro z hz a ha
    rw [algebraMap_smul]
    exact smul_eq_of_at (at_of_mem_latAt W v hz) ha
  have hu : evFin F v (liftV v c' * (1 - algebraMap F (AF F) (D : F))) = 1 := by
    rw [map_mul, map_sub, map_one, evFin_liftV, AlgHom.commutes, hcD'']
  refine ⟨liftV v 1 • x, liftV v c • x, liftV v c' • (1 - x), liftV v c' • (1 + x), ?_, ?_, fun z hz =>
    ⟨lift_smul_mem W v (one_mem _) δ hz, lift_smul_mem W v hc δ hz, hm ▸ lift_smul_mem W v hc' (1 - δ) hz,
      hp ▸ lift_smul_mem W v hc' (1 + δ) hz, ?_, ?_, ?_⟩⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul, at_liftV v 1 u hu, zero_smul]
  · have h : cA σ x = -x := by
      have h1 : cA σ x = inclR (F := F) (AF F) (σ (δ : E)) := by
        simp [hx, cA, inclR]
      rw [h1, hσ, map_neg]
    rw [map_smul, h, smul_neg]
  · have h := key z hz (liftV v 1 * liftV v c * algebraMap F (AF F) (D : F)) (by
      rw [map_mul, map_mul, evFin_liftV, evFin_liftV, AlgHom.commutes, one_mul, hcD])
    convert h using 2
    simp only [Algebra.smul_def, map_mul, ← hxx]
    ring
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (x * (1 - x)) * he'
  · convert key z hz _ hu using 2
    simp only [Algebra.smul_def, map_mul, map_sub, map_one, ← hxx]
    linear_combination (-x * (1 + x)) * he'

end GlobalTheory.InertSph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFrameCoordsOfMemIsotropicUnipoten
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_crd_of_mem_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u ∈ unipRad σ J C, ∃ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c ∧ c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF u hu
  obtain ⟨hC, b, hZ⟩ := (mem_unipRad_iff_frame F E σ n J j m C D Z J₀ hF u).1 hu
  set s := sigR (AF F) σ with hsdef
  set M := (matHom _ σ J u).1 with hMdef
  have hU : cT s M * adMat F J * M = adMat F J := u.2
  have hs : ∀ a : AF F ⊗[F] E, s (s a) = a := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma hF.cm x)
  have cc : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (cT s X) = X :=
    fun X => Matrix.ext fun i k => hs _
  have cadd : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X + Y) = cT s X + cT s Y :=
    fun X Y => Matrix.ext fun i k => map_add s _ _
  have csub : ∀ {a b : ℕ} (X Y : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)), cT s (X - Y) = cT s X - cT s Y :=
    fun X Y => Matrix.ext fun i k => map_sub s _ _
  have cad : ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) E), cT s (adMat F X) = adMat F (cT (σ : E →+* E) X) :=
    fun X => GlobalTheory.AutFunCounterexample.cT_map_gen σ X
  have gram : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) E) (Y : Matrix (Fin n) (Fin b) E),
      cT s (adMat F X) * adMat F J * adMat F Y = adMat F (cT (σ : E →+* E) X * J * Y) := fun X Y => by
    rw [cad]; simp only [adMat, Matrix.map_mul]
  have unit : ∀ {a b : ℕ} (X : Matrix (Fin n) (Fin a) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin b) (AF F ⊗[F] E)),
      cT s (M * X) * adMat F J * (M * Y) = cT s X * adMat F J * Y := fun X Y => by
    have e : cT s X * cT s M * adMat F J * (M * Y) = cT s X * (cT s M * adMat F J * M) * Y := by
      simp only [Matrix.mul_assoc]
    rw [Formalism.UG.cT_mul, e, hU]
  have ad0 : ∀ {a b : ℕ}, adMat F (0 : Matrix (Fin a) (Fin b) E) = 0 := fun {a b} => Matrix.map_zero _ (map_zero _)
  have ad1 : ∀ {a : ℕ}, adMat F (1 : Matrix (Fin a) (Fin a) E) = 1 := fun {a} => Matrix.map_one _ (map_zero _) (map_one _)

  have h1 : cT s (adMat F C) * adMat F J * (M * adMat F D) = 1 := by
    conv_lhs => rw [← hC]
    rw [unit, gram, hF.cd, ad1]
  have h2 : cT s (adMat F Z) * adMat F J * (M * adMat F D) = - cT s b := by
    have e := unit (adMat F Z) (adMat F D)
    rw [hZ, gram, hF.zd, ad0, cadd, Formalism.UG.cT_mul, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc (cT s b),
      Matrix.mul_assoc (cT s b), h1, Matrix.mul_one] at e
    exact eq_neg_of_add_eq_zero_left e
  set c := cT s (adMat F D) * adMat F J * (M * adMat F D) with hc
  have hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J)) +
      adMat F D * (cT s (adMat F C) * adMat F J) = 1 := by
    have e := congrArg (fun X => adMat F X) hF.sum
    simp only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e
    simp only [cad, adMat]
    exact e
  have hD : M * adMat F D = adMat F D - adMat F Z * plus σ J₀ b + adMat F C * c := by
    conv_lhs => rw [← Matrix.one_mul (M * adMat F D), ← hsum]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F Z)),
      ← Matrix.mul_assoc (cT s (adMat F C)), h1, h2, Matrix.mul_one, plus, Matrix.mul_neg, Matrix.mul_neg, ← hc]
    abel
  refine ⟨b, c, ⟨hC, hZ, hD⟩, ?_⟩

  have h0 := unit (adMat F D) (adMat F D)
  rw [gram, hF.dd, ad0] at h0
  have hP : cT s (plus σ J₀ b) = b * adMat F J₀⁻¹ := by
    rw [plus, Formalism.UG.cT_mul, cc, cad, GlobalTheory.UAut.cT_form_inv hF.herm₀]
  conv_lhs at h0 => rw [hD]
  rw [cadd, csub, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hP, Matrix.add_mul, Matrix.sub_mul, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (b * adMat F J₀⁻¹), Matrix.mul_assoc (cT s c),
    Matrix.mul_assoc (cT s c), ← hD, h1, h2, ← hc, Matrix.mul_one] at h0
  rw [← h0, plus, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentRadicalPointWithCoords
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.UnipCrd

section Ring

variable {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)

theorem cT_add' {p q : Type} (M N : Matrix p q R) : cT s (M + N) = cT s M + cT s N := by
  ext i k; simp [cT]

theorem cT_sub' {p q : Type} (M N : Matrix p q R) : cT s (M - N) = cT s M - cT s N := by
  ext i k; simp [cT]

def gr {p q : ℕ} (X : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) : Matrix (Fin p) (Fin q) R :=
  cT s X * A * Y

variable {p q k : ℕ}

theorem gr_add_left (X X' : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X + X') Y = gr s A X Y + gr s A X' Y := by
  simp [gr, cT_add', Matrix.add_mul]

theorem gr_sub_left (X X' : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X - X') Y = gr s A X Y - gr s A X' Y := by
  simp [gr, cT_sub', Matrix.sub_mul]

theorem gr_add_right (X : Matrix (Fin n) (Fin p) R) (Y Y' : Matrix (Fin n) (Fin q) R) :
    gr s A X (Y + Y') = gr s A X Y + gr s A X Y' := by
  simp [gr, Matrix.mul_add]

theorem gr_sub_right (X : Matrix (Fin n) (Fin p) R) (Y Y' : Matrix (Fin n) (Fin q) R) :
    gr s A X (Y - Y') = gr s A X Y - gr s A X Y' := by
  simp [gr, Matrix.mul_sub]

theorem gr_mul_left (X : Matrix (Fin n) (Fin k) R) (M : Matrix (Fin k) (Fin p) R) (Y : Matrix (Fin n) (Fin q) R) :
    gr s A (X * M) Y = cT s M * gr s A X Y := by
  simp [gr, Formalism.UG.cT_mul, Matrix.mul_assoc]

theorem gr_mul_right (X : Matrix (Fin n) (Fin p) R) (Y : Matrix (Fin n) (Fin k) R) (M : Matrix (Fin k) (Fin q) R) :
    gr s A X (Y * M) = gr s A X Y * M := by
  simp [gr, Matrix.mul_assoc]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

theorem cT_adMat {p q : Type} (X : Matrix p q E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k; simp [cT, adMat, sigR, inclR]

theorem gr_adMat {n p q : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E) :
    gr (sigR (AF F) σ) (adMat F J) (adMat F X) (adMat F Y) = adMat F (cT (σ : E →+* E) X * J * Y) := by
  simp only [gr, cT_adMat, adMat, Matrix.map_mul]

theorem invol (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_invol (h : IsCMExt F E σ) (x : AF F ⊗[F] E) : sigR (AF F) σ (sigR (AF F) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, invol σ h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem cT_cT (h : IsCMExt F E σ) {p q : Type} (M : Matrix p q (AF F ⊗[F] E)) :
    cT (sigR (AF F) σ) (cT (sigR (AF F) σ) M) = M := by
  ext i k; simp [cT, sigR_invol σ h]

theorem cT_inv_herm {m : ℕ} (J₀ : Matrix (Fin m) (Fin m) E) (h : IsHermND σ J₀) :
    cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := by
  have hJ : cT (σ : E →+* E) J₀ = J₀ := by
    ext i k; simp [cT, h.1]
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr h.2
  have e : cT (σ : E →+* E) J₀⁻¹ * J₀ = 1 := by
    calc cT (σ : E →+* E) J₀⁻¹ * J₀ = cT (σ : E →+* E) J₀⁻¹ * cT (σ : E →+* E) J₀ := by rw [hJ]
      _ = cT (σ : E →+* E) (J₀ * J₀⁻¹) := (Formalism.UG.cT_mul _ _ _).symm
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Formalism.UG.cT_one]
  exact (Matrix.inv_eq_left_inv e).symm

theorem exists_unipRad_crd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), c + cT (sigR (AF F) σ) c + b * plus σ J₀ b = 0 → ∃ u ∈ unipRad σ J C, Crd σ J C D Z J₀ u b c := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF b c hc
  set s := sigR (AF F) σ with hs
  set p := plus σ J₀ b with hp
  have hu : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have key : cT s p * adMat F J₀ = b := by
    rw [hp, plus, Formalism.UG.cT_mul, cT_cT σ hF.cm, cT_adMat, cT_inv_herm σ J₀ hF.herm₀, Matrix.mul_assoc, adMat,
      adMat, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 0 := by
    intro p q X Y h; rw [gr_adMat, h]; simp
  have g1 : ∀ (X Y : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) X * J * Y = 1 →
      gr s (adMat F J) (adMat F X) (adMat F Y) = 1 := by
    intro X Y h; rw [gr_adMat, h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have gzz : gr s (adMat F J) (adMat F Z) (adMat F Z) = adMat F J₀ := by rw [gr_adMat, hF.zz]
  have hcc := g0 C C hF.cc
  have hdd := g0 D D hF.dd
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have hzc := g0 Z C hF.zc
  have hzd := g0 Z D hF.zd
  have hcd := g1 C D hF.cd
  have hdc := g1 D C hF.dc
  have Ecd : cT s (adMat F C) * adMat F J * (adMat F D - adMat F Z * p + adMat F C * c) = 1 := by
    show gr s (adMat F J) _ _ = 1
    simp only [gr_add_right, gr_sub_right, gr_mul_right, hcd, hcz, hcc]
    simp
  have Ecz : cT s (adMat F C) * adMat F J * (adMat F Z + adMat F C * b) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_mul_right, hcz, hcc]
    simp
  have Ezz : cT s (adMat F Z + adMat F C * b) * adMat F J * (adMat F Z + adMat F C * b) = adMat F J₀ := by
    show gr s (adMat F J) _ _ = _
    simp only [gr_add_right, gr_add_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz]
    simp
  have Edz : cT s (adMat F D - adMat F Z * p + adMat F C * c) * adMat F J * (adMat F Z + adMat F C * b) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_add_left, gr_sub_left, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz, hdz, hdc]
    simp [key]
  have Edd : cT s (adMat F D - adMat F Z * p + adMat F C * c) * adMat F J * (adMat F D - adMat F Z * p + adMat F C * c) = 0 := by
    show gr s (adMat F J) _ _ = 0
    simp only [gr_add_right, gr_add_left, gr_sub_left, gr_sub_right, gr_mul_right, gr_mul_left, hcz, hcc, hzc, gzz,
      hdz, hdc, hcd, hdd, hzd]
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, sub_zero, zero_add, add_zero, zero_sub,
      sub_neg_eq_add, key]
    simp only [Matrix.neg_mul, sub_neg_eq_add]
    rw [← hc]
    abel
  obtain ⟨g, h1, h2, h3⟩ := _root_.GlobalTheory.SphEis.ColImg.exists_point_images F E σ n J j m C D Z J₀ hF (adMat F C) (adMat F D - adMat F Z * p + adMat F C * c)
    (adMat F Z + adMat F C * b) hcc Edd Ecd Ecz Edz Ezz
  exact ⟨g, (_root_.GlobalTheory.SphEis.mem_unipRad_iff_frame F E σ n J j m C D Z J₀ hF g).mpr ⟨h1, b, h2⟩, h1, h2, h3⟩

end GlobalTheory.SphEis.UnipCrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineWeightCharacterTriangularFrameChange
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.FlatChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
theorem exOf_flatWt_some (τ : Psi H) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    exOf Dw (flatWt Dw τ) 0 (some ⟨σ, i⟩) = if σ = τ.1 then -1 else if σ = conjEmb τ.1 then 1 else 0 := by
  classical
  show (wtOf Dw (flatWt Dw τ) 0).1 (σ, (i : ℕ)) = _
  have hi := i.2
  by_cases h : σ (H.rt : E) = H.rt0
  · have hp : (i : ℕ) < Dw.p := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_big (flatWt Dw τ) 0 ⟨σ, h⟩ i hp
    refine e0.trans ?_
    have hne : σ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
    by_cases e : σ = τ.1
    · have : (⟨σ, h⟩ : Psi H) = τ := Subtype.ext e
      simp [flatWt, parWt, this, e]
    · have : (⟨σ, h⟩ : Psi H) ≠ τ := fun e' => e (congrArg Subtype.val e')
      simp [flatWt, parWt, this, e, hne]
  · have h' := conj_mem h
    have hq : (i : ℕ) < Dw.q := by simpa [Datum.mult, h] using hi
    have e0 := wtOf_small (flatWt Dw τ) 0 ⟨conjEmb σ, h'⟩ i hq
    simp only [conjEmb_conjEmb] at e0
    refine e0.trans ?_
    have hne : σ ≠ τ.1 := fun e' => h (e' ▸ τ.2)
    have hiff : (⟨conjEmb σ, h'⟩ : Psi H) = τ ↔ σ = conjEmb τ.1 := by
      constructor
      · intro e'; rw [← congrArg Subtype.val e', conjEmb_conjEmb]
      · intro e'; apply Subtype.ext; show conjEmb σ = τ.1; rw [e', conjEmb_conjEmb]
    by_cases e : σ = conjEmb τ.1
    · have h2 := hiff.2 e
      rw [if_neg hne, if_pos e]
      simp only [flatWt, parWt, if_pos h2]
      norm_num
    · have : (⟨conjEmb σ, h'⟩ : Psi H) ≠ τ := fun e' => e (hiff.1 e')
      simp [flatWt, parWt, this, e, hne]

theorem flatWt_char (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (τ : Psi H) (S : Type) [Field S] (t : Ix Dw → Sˣ) :
    (((∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i : Sˣ)) : S) * ∏ i : Fin (Dw.mult τ.1), (t (some ⟨τ.1, i⟩) : S) =
      ∏ j : Fin (Dw.mult (conjEmb τ.1)), (t (some ⟨conjEmb τ.1, j⟩) : S) := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ τ.2)
  have key : (∏ i, t i ^ exOf Dw (flatWt Dw τ) 0 i) =
      (∏ i : Fin (Dw.mult τ.1), t (some ⟨τ.1, i⟩))⁻¹ * ∏ j : Fin (Dw.mult (conjEmb τ.1)), t (some ⟨conjEmb τ.1, j⟩) := by
    rw [Fintype.prod_option, Fintype.prod_sigma]
    have h0 : exOf Dw (flatWt Dw τ) 0 none = 0 := rfl
    rw [h0, zpow_zero, one_mul]
    rw [Fintype.prod_eq_mul τ.1 (conjEmb τ.1) hne ?_]
    · congr 1
      · rw [← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_pos rfl, zpow_neg_one]
      · refine Finset.prod_congr rfl fun i _ => ?_
        rw [exOf_flatWt_some, if_neg hne.symm, if_pos rfl, zpow_one]
    · rintro σ ⟨h1, h2⟩
      refine Finset.prod_eq_one fun i _ => ?_
      rw [exOf_flatWt_some, if_neg h1, if_neg h2, zpow_zero]
  rw [key, ← Units.coe_prod, ← Units.coe_prod, ← Units.val_mul]
  congr 1
  rw [mul_comm, mul_inv_cancel_left]

end GlobalTheory.FlatChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridCharactersUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GridUnr

theorem chi_eta_unramAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ i : Fin D.R.m, GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) ∧ GlobalTheory.WeilParts.UnramAt e Lc.eta := by
  intro D T Lc sc G μ₀ hμ t v e he hv i
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  refine ⟨GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (G.ch.chi_eq _ h1 h2) v e he fun P hP => ?_,
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hμ.eta v e he fun P _ => Lc.C.isEta.unr P⟩
  exact G.ch.unr _ h1 h2 P (by rw [hP]; exact hv)

end GlobalTheory.GridUnr
end

