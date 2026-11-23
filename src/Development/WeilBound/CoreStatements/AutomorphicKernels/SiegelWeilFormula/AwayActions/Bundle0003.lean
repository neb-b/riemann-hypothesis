module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.SigmaSigma
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.DecAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwayActOf
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace Step

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem away_smul {Ψ : d.MF} (hΨ : d.IsAwayW w Ψ) (c : ℂ) : d.IsAwayW w (c • Ψ) := by
  intro X Z hZ hf
  simp only [Pi.smul_apply, hΨ X Z hZ hf]

theorem away_zero : d.IsAwayW w (0 : d.MF) := fun _ _ _ _ => rfl

theorem tens_key {f g : d.LF} {Ψ Ψ' : d.MF} (hΨ : d.IsAwayW w Ψ) (hΨ' : d.IsAwayW w Ψ')
    (h : R.tens w f Ψ = R.tens w g Ψ') : ∀ u X, f u * Ψ X = g u * Ψ' X := by
  intro u X
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u
  have := congrFun h (X + Z)
  simp only [RD.tens, hZ3, hΨ X Z hZ1 hZ2, hΨ' X Z hZ1 hZ2] at this
  exact this

theorem away_conj (hT : TAll) {x₁ x₂ x' : d.G} {A₁ A₂ : d.LF → d.LF} {B₁ B₂ B' : d.MF → d.MF}
    (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂) (h' : R.StepOK w x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, R.StepOK w (x₁ * x' * x₂) id B := by
  have hsch := d.om_sch
  have hc := R.step_comp w hsch (R.step_comp w hsch h₁ h') h₂
  have h0 := R.step_comp w hsch h₁ h₂
  refine ⟨fun Ψ => if h : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 then
      (Ψ h.choose / B₁ (B₂ Ψ) h.choose) • B₁ (B' (B₂ Ψ)) else 0,
    fun f hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only
    split_ifs with h
    · exact away_smul w (hc.2 Ψ hΨ).1 _
    · exact away_zero w
  · have e := (hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
    have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ
    rw [h1, map_one, Module.End.one_apply, hTΦ] at e0
    have key : ∀ u X, f u * Ψ X = A₁ (A₂ f) u * B₁ (B₂ Ψ) X := tens_key R w hΨ (h0.2 Ψ hΨ).1 e0
    by_cases hz : (∀ u, f u = 0) ∨ ∀ X, Ψ X = 0
    · have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by
        rw [hTΦ]
        funext X
        rcases hz with hz | hz <;> simp [RD.tens, hz])
      subst hΦ0
      rw [map_zero, d.T_zero]
      funext X
      rcases hz with hz | hz
      · simp [RD.tens, hz]
      · have hn : ¬ ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 := fun ⟨X₀, h, _⟩ => h (hz X₀)
        simp [RD.tens, dif_neg hn]
    · push_neg at hz
      obtain ⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩ := hz
      have hex : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 := by
        refine ⟨X₁, hX₁, fun h0' => ?_⟩
        have := key u₀ X₁
        rw [h0', mul_zero] at this
        exact mul_ne_zero hu₀ hX₁ this
      have hB0 := hex.choose_spec.2
      have hA : ∀ u, A₁ (A₂ f) u = f u * (Ψ hex.choose / B₁ (B₂ Ψ) hex.choose) := by
        intro u
        have := key u hex.choose
        rw [mul_div_assoc', eq_div_iff hB0]
        linear_combination -this
      rw [e]
      funext X
      simp only [RD.tens, Function.comp_apply, id_eq, dif_pos hex, Pi.smul_apply, smul_eq_mul, hA]
      ring

end Step

theorem awayAct_of : TAll → AuxiliaryPrimeFunction → AdDecomp → AwayAct := by
  intro hT hA hD F E _ _ _ _ _ σ d R w x hx
  have hsch := d.om_sch
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have he : eW w • inFrame d.b x = eW w • (1 : Matrix _ _ (AE F E)) :=
    (eW_smul_eq_iff d w _ _).2 (by rw [hx, cw_one])
  obtain ⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩ :=
    hD F E σ d ε w₀ hw₀ (eW w) (eW_mul_self w) x he
  obtain ⟨C, s, BW, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  have hW3 := R.step_comp w hsch (R.step_comp w hsch hW hW) hW
  have h4' : w₀ * (w₀ * w₀ * w₀) = 1 := by
    simpa only [mul_assoc] using RD.w_four hw₀
  obtain ⟨BC, hC⟩ := Step.away_conj R w hT hW hW3 (Step.stepN R w hT x₂ c h2 hc) h4'
  have hinv : w₀⁻¹ = w₀ * w₀ * w₀ := (eq_inv_of_mul_eq_one_left (RD.w_four hw₀)).symm
  have hall := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (Step.stepN R w hT x₁ t h1 ht) hC)
    (Step.stepM R w hT x₃ a a' h3 ha')) (Step.stepN R w hT x₄ b h4 hb)
  rw [hxe, hinv]
  exact ⟨_, fun Ψ hΨ => ⟨(hall.2 Ψ hΨ).1, fun f hf Φ hΦ hTΦ => (hall.2 Ψ hΨ).2 f hf Φ hΦ hTΦ⟩⟩

end PositivityTheory.SiegelWeilFormula.KAway

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.SumIdemMul
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsEH (σ : E →ₐ[F] E) {n : ℕ} (ε : ℤ) (g : Matrix (Fin n) (Fin n) E) : Prop := gᵀ + (ε : E) • g.map σ = 0

def fam (σ : E →ₐ[F] E) {n : ℕ} (ε : ℤ) (δ : E) (i : Fin n × Fin n × Bool) : Matrix (Fin n) (Fin n) E :=
  (if i.2.2 then δ else 1) • Matrix.single i.1 i.2.1 1 - ((ε : E) * σ (if i.2.2 then δ else 1)) • Matrix.single i.2.1 i.1 1

theorem mapSingleE₀ {Ω G : Type} [Field Ω] [FunLike G E Ω] [RingHomClass G E Ω] (f : G) {n : ℕ} (p q : Fin n) :
    (Matrix.single p q (1 : E)).map f = Matrix.single p q 1 := by
  ext a c
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem mapSmulE₀ {Ω G : Type} [Field Ω] [FunLike G E Ω] [RingHomClass G E Ω] (f : G) {n : ℕ} (c : E) (M : Matrix (Fin n) (Fin n) E) :
    (c • M).map f = f c • M.map f := by
  ext a b
  simp

theorem fam_isEH (hcm : IsCMExt F E σ) {n : ℕ} (ε : ℤ) (hε : ε * ε = 1) (δ : E) (hδ : σ δ = -δ)
    (i : Fin n × Fin n × Bool) : IsEH σ ε (fam σ ε δ i) := by
  obtain ⟨j, k, b⟩ := i
  have hε' : (ε : E) * (ε : E) = 1 := by exact_mod_cast hε
  have hσl : σ (σ (if b then δ else 1)) = if b then δ else 1 := by
    cases b <;> simp [hδ]
  unfold IsEH fam
  simp only
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_single,
    Matrix.transpose_single, Matrix.map_sub _ (map_sub σ), mapSmulE₀ σ, mapSmulE₀ σ,
    mapSingleE₀, mapSingleE₀]
  simp only [map_mul, map_intCast, hσl, smul_sub, smul_smul]
  have e : (ε : E) * ((ε : E) * (if b then δ else 1)) = if b then δ else 1 := by rw [← mul_assoc, hε', one_mul]
  rw [e]
  abel

theorem span_fam (hcm : IsCMExt F E σ) {n : ℕ} (ε : ℤ) (δ : E) (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) {Ω : Type} [Field Ω]
    (ψ : AE F E →+* Ω) (T : Matrix (Fin n) (Fin n) Ω) :
    ∃ x : Fin n × Fin n × Bool → Ω, T = ∑ i, x i • (fam σ ε δ i).map (ψ.comp (inclR (F := F) (AF F))) := by
  classical
  set ψ' : E →+* Ω := ψ.comp (inclR (F := F) (AF F)) with hψ'
  have hδ' : ψ' δ ≠ 0 := (map_ne_zero ψ').2 hδ0
  have h2 : (2 : Ω) ≠ 0 := by
    have e2 : ψ' 2 = 2 := map_ofNat ψ' 2
    rw [← e2]
    exact (map_ne_zero ψ').2 two_ne_zero
  have key : ∀ j k : Fin n, (1 / 2 : Ω) • (fam σ ε δ (j, k, false)).map ψ' +
      (1 / (2 * ψ' δ)) • (fam σ ε δ (j, k, true)).map ψ' = Matrix.single j k 1 := by
    intro j k
    simp only [fam, Bool.false_eq_true, if_false, if_true]
    rw [Matrix.map_sub _ (map_sub ψ'), Matrix.map_sub _ (map_sub ψ'), mapSmulE₀, mapSmulE₀, mapSmulE₀, mapSmulE₀,
      mapSingleE₀, mapSingleE₀]
    simp only [map_mul, map_intCast, map_one, hδ, map_neg, smul_sub, smul_smul]
    match_scalars <;> field_simp <;> ring
  refine ⟨fun i => T i.1 i.2.1 * (if i.2.2 then 1 / (2 * ψ' δ) else 1 / 2), ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single T]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  have e1 : Matrix.single j k (T j k) = T j k • Matrix.single j k (1 : Ω) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e1, ← key j k, smul_add, mul_smul, mul_smul, add_comm]

theorem cA_algF (a : F) : cA σ (algebraMap F (AE F E) a) = algebraMap F (AE F E) a := by
  rw [IsScalarTower.algebraMap_apply F (AF F) (AE F E), AlgHom.commutes]

theorem map_incM_sum {Ω ι : Type} [Field Ω] [Fintype ι] (ψ : AE F E →+* Ω) {n : ℕ}
    (f : ι → Matrix (Fin n) (Fin n) E) (s : ι → F) :
    (incM F (∑ i, s i • f i)).map ψ = ∑ i, ψ (algebraMap F (AE F E) (s i)) • (f i).map (ψ.comp (inclR (F := F) (AF F))) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [incM, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, map_sum, RingHom.comp_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_mul]
  congr 2
  exact (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes (s i)

theorem isEH_sum {n : ℕ} (ε : ℤ) {ι : Type} [Fintype ι] (f : ι → Matrix (Fin n) (Fin n) E) (hf : ∀ i, IsEH σ ε (f i))
    (s : ι → F) : IsEH σ ε (∑ i, s i • f i) := by
  unfold IsEH at *
  have e : (∑ i, s i • f i).map σ = ∑ i, s i • (f i).map σ := by
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def]
  rw [Matrix.transpose_sum, e, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.transpose_smul, smul_comm, ← smul_add, hf i, smul_zero]

theorem exists_point (hcm : IsCMExt F E σ) {n : ℕ} (ε : ℤ) (hε : ε * ε = 1)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (hX : IsUnit X.det) {Ω : Type} [Field Ω] (φ : AE F E →+* Ω) :
    ∃ g, IsEH σ ε g ∧ φ (X.toBlocks₁₁ - incM F g * X.toBlocks₂₁).det ≠ 0 ∧
      φ (cA σ (X.toBlocks₁₁ - incM F g * X.toBlocks₂₁).det) ≠ 0 := by
  classical
  obtain ⟨δ, hδ0, hδ⟩ := exists_delta hcm
  set A := X.toBlocks₁₁ with hA
  set C := X.toBlocks₂₁ with hC
  let ψ : Bool → (AE F E →+* Ω) := fun k => if k then φ.comp (cA σ).toRingHom else φ
  have hψF : ∀ k (a : F), ψ k (algebraMap F (AE F E) a) = φ (algebraMap F (AE F E) a) := by
    intro k a; cases k
    · rfl
    · change φ (cA σ (algebraMap F (AE F E) a)) = _
      rw [cA_algF]
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have hinj : Function.Injective (fun a : F => φ (algebraMap F (AE F E) a)) := (φ.comp (algebraMap F (AE F E))).injective
  haveI : Infinite Ω := Infinite.of_injective _ hinj
  let fψ : Bool → (Fin n × Fin n × Bool) → Matrix (Fin n) (Fin n) Ω := fun k i =>
    (fam σ ε δ i).map ((ψ k).comp (inclR (F := F) (AF F)))
  let P : Bool → MvPolynomial (Fin n × Fin n × Bool) Ω := fun k => (Matrix.of fun a b =>
    MvPolynomial.C (ψ k (A a b)) - ∑ l, (∑ i, MvPolynomial.X i * MvPolynomial.C (fψ k i a l)) * MvPolynomial.C (ψ k (C l b))).det
  have hev : ∀ k x, MvPolynomial.eval x (P k) = (A.map (ψ k) - (∑ i, x i • fψ k i) * C.map (ψ k)).det := by
    intro k x
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [Matrix.mul_apply, Matrix.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hval : ∀ k (s : Fin n × Fin n × Bool → F), ψ k (A - incM F (∑ i, s i • fam σ ε δ i) * C).det =
      MvPolynomial.eval (fun i => φ (algebraMap F (AE F E) (s i))) (P k) := by
    intro k s
    rw [hev, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_mul, map_incM_sum]
    simp only [hψF, fψ]
  have hne : ∀ k, P k ≠ 0 := by
    intro k h0
    have hXk : (X.map (ψ k)).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact (hX.map (ψ k)).ne_zero
    obtain ⟨T, hT⟩ := exists_T_field (X.map (ψ k)) hXk
    obtain ⟨x, hx⟩ := span_fam hcm ε δ hδ0 hδ (ψ k) T
    have := hev k x
    rw [h0, map_zero] at this
    apply hT
    rw [hx]
    exact this.symm
  have hPP : P true * P false ≠ 0 := mul_ne_zero (hne true) (hne false)
  have hs : ∀ i : Fin n × Fin n × Bool, (Set.range (fun a : F => φ (algebraMap F (AE F E) a))).Infinite :=
    fun _ => Set.infinite_range_of_injective hinj
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ Set.univ.pi (fun _ => Set.range (fun a : F => φ (algebraMap F (AE F E) a))),
      MvPolynomial.eval x (P true * P false) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hPP (MvPolynomial.funext_set _ hs fun x hx => by rw [hcon x hx, map_zero])
  choose s hsx using fun i => hx i (Set.mem_univ i)
  have hxs : x = fun i => φ (algebraMap F (AE F E) (s i)) := funext fun i => (hsx i).symm
  rw [map_mul, hxs] at hx0
  refine ⟨∑ i, s i • fam σ ε δ i, isEH_sum ε _ (fun i => fam_isEH hcm ε hε δ hδ i) s, ?_, ?_⟩
  · have := hval false s
    change φ _ = _ at this
    rw [this]
    exact right_ne_zero_of_mul hx0
  · have := hval true s
    change φ (cA σ _) = _ at this
    rw [this]
    exact left_ne_zero_of_mul hx0

theorem sum_idem_mul {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (η : ι → R) (hi : ∀ i, η i * η i = η i)
    (ho : ∀ i j, i ≠ j → η i * η j = 0) (a b : ι → R) :
    (∑ i, η i * a i) * (∑ j, η j * b j) = ∑ i, η i * (a i * b i) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [mul_mul_mul_comm, ho i j (Ne.symm hj), zero_mul])
    (fun h => absurd (Finset.mem_univ i) h), mul_mul_mul_comm, hi]

def QS (σ : E →ₐ[F] E) {n : ℕ} (ε : ℤ) (M : Matrix (Fin n) (Fin n) (AE F E)) : Prop :=
  Mᵀ + ((ε : ℤ) : AE F E) • M.map (cA σ) = 0

theorem qs_zero {n : ℕ} (ε : ℤ) : QS σ ε (0 : Matrix (Fin n) (Fin n) (AE F E)) := by
  ext a b; simp [QS]

theorem qs_add {n : ℕ} (ε : ℤ) {M N : Matrix (Fin n) (Fin n) (AE F E)} (hM : QS σ ε M) (hN : QS σ ε N) :
    QS σ ε (M + N) := by
  unfold QS at *
  rw [Matrix.transpose_add, Matrix.map_add _ (map_add _), smul_add, add_add_add_comm, hM, hN, add_zero]

theorem qs_smul {n : ℕ} (ε : ℤ) (a : AF F) {M : Matrix (Fin n) (Fin n) (AE F E)} (hM : QS σ ε M) : QS σ ε (a • M) := by
  unfold QS at *
  have e : (a • M).map (cA σ) = a • M.map (cA σ) := by ext i j; simp [map_smul]
  rw [Matrix.transpose_smul, e, smul_comm, ← smul_add, hM, smul_zero]

theorem qs_sum {n : ℕ} (ε : ℤ) {ι : Type} (s : Finset ι) (M : ι → Matrix (Fin n) (Fin n) (AE F E)) (h : ∀ i ∈ s, QS σ ε (M i)) :
    QS σ ε (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using qs_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact qs_add ε (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem qs_incM {n : ℕ} (ε : ℤ) {g : Matrix (Fin n) (Fin n) E} (hg : IsEH σ ε g) : QS σ ε (incM F g) := by
  unfold QS
  ext a b
  have hab : g b a + (ε : E) * σ (g a b) = 0 := by
    have := congrFun (congrFun (show gᵀ + (ε : E) • g.map σ = 0 from hg) a) b
    simpa using this
  simp only [incM, Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.zero_apply, cA_inclR]
  rw [show ((ε : ℤ) : AE F E) = inclR (F := F) (AF F) (ε : E) from (map_intCast _ _).symm, ← map_mul, ← map_add (f := _), hab,
    map_zero]

end PositivityTheory.SiegelWeilFormula.KAway

end
end

