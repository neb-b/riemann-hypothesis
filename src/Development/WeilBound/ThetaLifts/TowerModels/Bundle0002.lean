module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.ExistsHaarOfIsCompact
section
noncomputable section
namespace PositivityTheory.ThKG.Tow.Stab
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

def stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : Subgroup (UA σ X.J) where
  carrier := {g | (∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)) ∧
    ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X}
  one_mem' := by
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _
    · simp only [inv_one, mat_one, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_mul, Matrix.map_mul]; exact (hg1 w).mul_left (hh1 w)
    · rw [mul_inv_rev, mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact ⟨(hg2 _ (hh2 z hz).1).1, (hh2 _ (hg2 z hz).2).2⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · set A := (mat g).map (piInf (B.emb w))
      set A' := (mat g⁻¹).map (piInf (B.emb w))
      have e1 : A * A' = 1 := by
        rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      have e2 : A' * A = 1 := by
        rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have hc := hg1 w
      show A' * X.θ w = X.θ w * A'
      calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [e1, Matrix.mul_one]
        _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
        _ = A' * (A * X.θ w) * A' := by rw [hc.eq]
        _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
        _ = X.θ w * A' := by rw [e2, Matrix.one_mul]
    · rw [inv_inv]; exact ⟨(hg2 z hz).2, (hg2 z hz).1⟩

theorem isStab_stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : IsStab B (stabK (σ := σ) B X) := fun _ => Iff.rfl

theorem exists_haar_of_isCompact {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J))
    (hK : IsCompact (K : Set (UA σ J))) : ∃ μ : Measure K, μ.IsHaarMeasure := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact ⟨Measure.haarMeasure ⊤, Measure.isHaarMeasure_haarMeasure _⟩

theorem exists_haar_idele : ∃ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem isClosed_stabK (B : Base F E) {n : ℕ} (X : Spc F E n)
    (hL : IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E))) :
    IsClosed ((stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ X.J => mat g⁻¹ := hm.comp continuous_inv
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have h1 : IsClosed {g : UA σ X.J | ∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))
  have h2 : IsClosed {g : UA σ X.J | ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun z => isClosed_iInter fun _ => ?_
    exact (hL.preimage (hm.matrix_mulVec continuous_const)).inter (hL.preimage (hmi.matrix_mulVec continuous_const))
  exact h1.inter h2

end PositivityTheory.ThKG.Tow.Stab
end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneForm
section
noncomputable section

namespace PositivityTheory.ThKG.Tow.Pln

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem form_swap (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} (hJ : ∀ i j, σ (J j i) = ε * J i j)
    (a b : Fin n → E) : σ (form σ J a b) = ε * form σ J b a := by
  have hJ' : ∀ i j, σ (J i j) = ε * J j i := fun i j => hJ j i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, sigma_sigma h, hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_add_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := by simp [form, add_dotProduct]

theorem form_sub_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a - b) c = form σ J a c - form σ J b c := by simp [form, sub_dotProduct]

theorem form_smul_left {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J (s • a) c = s * form σ J a c := by simp [form, smul_dotProduct]

theorem form_add_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J c (a + b) = form σ J c a + form σ J c b := by
  have : (fun i => σ ((a + b) i)) = (fun i => σ (a i)) + fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a c : Fin n → E) :
    form σ J c (s • a) = σ s * form σ J c a := by
  have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_gram {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E) (u u' : Fin n₁ → E) :
    form σ (ιᵀ * J * ι.map σ) u u' = form σ J (ι *ᵥ u) (ι *ᵥ u') := by
  have e1 : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ fun i => σ (u' i) :=
    funext fun i => RingHom.map_mulVec (σ : E →+* E) ι u' i
  simp only [form, e1, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem map_form (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    e (form σ J a b) = (fun i => e (a i)) ⬝ᵥ J.map e *ᵥ star (fun i => e (b i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Pi.star_apply, h.2.2.2 e]

theorem transpose_mulVec_eq_zero {n n₁ : ℕ} {R : Type} [CommRing R] (ι : Matrix (Fin n) (Fin n₁) R) (w : Fin n → R)
    (hw : ∀ u, (ι *ᵥ u) ⬝ᵥ w = 0) : ιᵀ *ᵥ w = 0 := by
  funext k
  have := hw (Pi.single k 1)
  rwa [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one, ← Matrix.mulVec_transpose] at this

theorem map_herm (h : IsCMExt F E σ) (e : E →+* ℂ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : E} {κ : ℂ}
    (hκ : star κ * e ε = κ) (hJ : ∀ i j, σ (J j i) = ε * J i j) : (κ • J.map e)ᴴ = κ • J.map e := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← h.2.2.2 e, hJ,
    map_mul]
  rw [← mul_assoc, hκ]

theorem form_sub_right {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J c (a - b) = form σ J c a - form σ J c b := by
  have : (fun i => σ ((a - b) i)) = (fun i => σ (a i)) - fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_sub, dotProduct_sub]

theorem map_orth (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (x : Fin n → E) (hx : ∀ u, form σ J (ι *ᵥ u) x = 0) :
    (ι.map e)ᵀ *ᵥ (J.map e *ᵥ star (fun i => e (x i))) = 0 := by
  have h0 : ιᵀ *ᵥ (J *ᵥ fun i => σ (x i)) = 0 := transpose_mulVec_eq_zero ι _ hx
  have hs : star (fun i => e (x i)) = fun i => e (σ (x i)) := funext fun i => by simp [h.2.2.2 e]
  have e2 : (J.map e *ᵥ fun i => e (σ (x i))) = fun i => e ((J *ᵥ fun i => σ (x i)) i) :=
    funext fun i => (RingHom.map_mulVec e J _ i).symm
  have e3 : (ιᵀ.map e *ᵥ fun i => e ((J *ᵥ fun i => σ (x i)) i)) = fun k => e ((ιᵀ *ᵥ (J *ᵥ fun i => σ (x i))) k) :=
    funext fun k => (RingHom.map_mulVec e ιᵀ _ k).symm
  rw [hs, ← Matrix.transpose_map, e2, e3, h0]
  funext k
  simp

theorem map_gram (h : IsCMExt F E σ) (e : E →+* ℂ) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) : (ι.map e)ᵀ * J.map e * (ι.map e).map star = (ιᵀ * J * ι.map σ).map e := by
  have : (ι.map e).map star = (ι.map σ).map e := by ext i j; simp [h.2.2.2 e]
  rw [this, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]

theorem form_single {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    form σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : (fun k => σ ((Pi.single j (1 : E) : Fin n → E) k)) = Pi.single j 1 := by
    funext k; by_cases h : k = j <;> simp [h]
  simp [form, this, Matrix.mulVec_single, single_dotProduct]

def formL {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun z := form σ J z x
  map_add' a b := form_add_left J a b x
  map_smul' s a := form_smul_left J s a x

def conjInt (σ : E →ₐ[F] E) (o : 𝓞 E) : 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E) o

end PositivityTheory.ThKG.Tow.Pln

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def PlaneHerm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsHerm σ B r s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁

def PlaneSkew : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsSkew σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsSkew σ B r s ∧ Y₁.IsSkew σ B (r - 1) (s - 1) ∧ H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁

def PlaneEx : Prop := PlaneHerm ∧ PlaneSkew

def ModelEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∃ M : Model σ X W, M.IsGood B.ψ

def WeilEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om

def PairEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → (∃ M : Model σ X W, M.IsGood B.ψ) ∧
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d →
      ∀ M : Model σ X W, M.IsGood B.ψ → ∃ om, IsPair B M χX χW om r s r' s'

theorem pairEx_of (h₁ : ModelEx) (h₂ : WeilEx) : PairEx := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  refine ⟨h₁ F E σ B hB n d X W r s r' s' hX hW, fun χX χW a b c e M hM => ?_⟩
  obtain ⟨om, hom⟩ := h₂ F E σ B hB n d X W r s r' s' hX hW M hM χX χW a b c e
  exact ⟨om, hB, hX, hW, hM, a, b, c, e, hom⟩

end PositivityTheory.ThKG.Tow

end
end

