module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0071
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsUnitaryStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayley_endomorphisms_unitary : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → Formalism.REAL.IsUnitary ε E := by
  first | exact @GlobalTheory.CapUnitary.isUnitary_of_isE | exact GlobalTheory.CapUnitary.isUnitary_of_isE | (intros; apply GlobalTheory.CapUnitary.isUnitary_of_isE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharacterEqWeilPairing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem datum_character_eq_zpow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    {F : Type} [Field F] {M : ℕ} (hM : 0 < M) {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ M)
    (φ : Dw.La →+ Additive Fˣ) (hφ : ∀ a, φ (M • a) = 0) :
    ∃ d : Dw.La, ∀ a, Additive.toMul (φ a) = ζ ^ Dw.EF a d := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : Module.Projective ℤ Dw.La := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 Dw.proj
    haveI : Module.Free ℤ (Dw.La →₀ 𝓞 E) := inferInstance
    exact Module.Projective.of_split (s.restrictScalars ℤ)
      ((Finsupp.linearCombination (𝓞 E) id).restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hs x)
  let f : ℤ →ₗ[ℤ] Additive Fˣ := LinearMap.toSpanSingleton ℤ (Additive Fˣ) (Additive.ofMul ζ)
  have hmem : ∀ a, φ.toIntLinearMap a ∈ LinearMap.range f := by
    intro a
    have h1 : Additive.toMul (φ a) ∈ rootsOfUnity M F := by
      rw [mem_rootsOfUnity, ← toMul_nsmul, ← map_nsmul, hφ]; rfl
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_mem_rootsOfUnity h1
    refine ⟨i, ?_⟩
    change (i : ℤ) • Additive.ofMul ζ = φ a
    rw [natCast_zsmul, ← ofMul_pow, hi]; rfl
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property f.rangeRestrict
    (φ.toIntLinearMap.codRestrict _ hmem) f.surjective_rangeRestrict
  obtain ⟨d, hd⟩ := Dw.unimod.2 ψ
  refine ⟨-d, fun a => ?_⟩
  have skew : Dw.EF a (-d) = ψ a := by
    have := Dw.alt (d + a)
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt] at this
    rw [map_neg, ← hd]
    linarith
  have h2 : f (ψ a) = φ a := congrArg Subtype.val (LinearMap.congr_fun hψ a)
  rw [skew, ← h2]
  rfl

theorem character_eq_weil_pairing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] (A : PolAV (Sp (FractionRing R))), letI := H.starRing; ∀ (oA : A.OAct (𝓞 E)) (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a g => g ≫ oA.act a) (fun n g g' c => WeilIs A.A A.L n g g' (unitOn c))) (N k : ℕ), 1 ≤ N → 1 ≤ k → Nat.Coprime N k → ∀ β u u' : 𝓞 E, β * star β = (N : 𝓞 E) → u * β + u' * star β = 1 → ∀ κ : (TFK (R := R) F ⟶ A.A) → Fˣ, (∀ z z', z ≫ oA.act β = 1 → z' ≫ oA.act β = 1 → κ (z * z') = κ z * κ z') → ∃ b : TFK (R := R) F ⟶ A.A, b ≫ oA.act (star β) = 1 ∧ ∀ z, z ≫ oA.act β = 1 → WeilIs A.A A.L ((k * N : ℕ) : ℤ) z b (unitOn (κ z)) := by
  intro E _ _ _ H R _ _ F _ _ A
  let _ := H.starRing
  intro oA Dw I N k hN hk hco β u u' hβ huu κ hκ
  have hM : 0 < k * N := Nat.mul_pos hk hN
  have hlin : ∀ (c : 𝓞 E) b, I.ev (k * N) (c • b) = I.ev (k * N) b ≫ oA.act c := fun c b => I.lin _ c b
  obtain ⟨t, k', htk⟩ := (Nat.isCoprime_iff_coprime.2 hco).map (Int.castRingHom (𝓞 E))
  simp only [eq_intCast, Int.cast_natCast] at htk
  obtain ⟨ε, w, v, hw, hv⟩ : ∃ ε w v : 𝓞 E, β * ε = ((k * N : ℕ) : 𝓞 E) * w ∧ 1 = ε + v * β := by
    refine ⟨k * k' * u' * star β, k' * u', star β * t + k * k' * u, ?_, ?_⟩
    · push_cast
      rw [← hβ]; ring
    · linear_combination (-(k * k' : 𝓞 E)) * huu - htk - t * hβ
  have hzero : ∀ (c : 𝓞 E) (a : Dw.La), I.ev (k * N) ((((k * N : ℕ) : 𝓞 E) * c) • a) = 1 := by
    intro c a
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
    exact (I.ker _ hM _).2 ⟨_, rfl⟩
  have hkill : ∀ a, I.ev (k * N) (ε • a) ≫ oA.act β = 1 := by
    intro a
    rw [← hlin, smul_smul, hw, hzero]
  have hfix : ∀ a, I.ev (k * N) a ≫ oA.act β = 1 → I.ev (k * N) (ε • a) = I.ev (k * N) a := by
    intro a ha
    obtain ⟨f, hf⟩ := (I.ker _ hM (β • a)).1 (by rw [hlin]; exact ha)
    have h1 : a = ε • a + (k * N) • (v • f) := by
      rw [smul_comm (k * N) v f, ← hf, smul_smul, ← add_smul, ← hv, one_smul]
    conv_rhs => rw [h1, I.add, (I.ker _ hM _).2 ⟨_, rfl⟩, _root_.mul_one]
  let φ : Dw.La →+ Additive Fˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (κ (I.ev (k * N) (ε • a))))
    (fun a b => by rw [smul_add, I.add, hκ _ _ (hkill a) (hkill b), ofMul_mul])
  have hφ : ∀ a, φ ((k * N) • a) = 0 := by
    intro a
    rw [← map_zero φ]
    change Additive.ofMul (κ (I.ev (k * N) (ε • (k * N) • a))) = Additive.ofMul (κ (I.ev (k * N) (ε • 0)))
    rw [smul_comm ε (k * N) a, (I.ker _ hM _).2 ⟨_, rfl⟩, smul_zero,
      (I.ker _ hM 0).2 ⟨0, (smul_zero _).symm⟩]
  obtain ⟨d, hd⟩ := datum_character_eq_zpow Dw hM (I.ζ_prim _ hM) φ hφ
  refine ⟨I.ev (k * N) (H.bar ε • d), ?_, fun z hz => ?_⟩
  · rw [← hlin, smul_smul]
    change I.ev (k * N) ((H.bar β * H.bar ε) • d) = 1
    rw [← map_mul, hw, map_mul, map_natCast, hzero]
  · have hzN : z ^ N = 1 := pow_eq_one_of_kill oA.toRingAct (by rw [_root_.mul_comm]; exact hβ) z hz
    obtain ⟨a, rfl⟩ := (I.onto _ hM z).1 (by rw [pow_mul', hzN, one_pow])
    have h1 : κ (I.ev (k * N) a) = I.ζ (k * N) ^ Dw.EF a (H.bar ε • d) := by
      rw [← Dw.adj, ← hd]
      change _ = κ (I.ev (k * N) (ε • ε • a))
      rw [hfix _ (hkill a), hfix a hz]
    rw [h1]
    exact I.isom _ hM _ _

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoefHasDerivAt
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

namespace GlobalTheory.TensorStd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def coefL {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => herm H (g *ᵥ v) w
      map_add' := fun g h => by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c g => by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }

theorem coefL_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    coefL H v w g = herm H (g *ᵥ v) w := rfl

theorem coef_hasDerivAt {k r : ℕ} (X : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    HasDerivAt (fun t : ℝ => herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ v) w)
      (herm (Hpk k r) (X *ᵥ v) w) 0 := by
  have h1 := B5.curve_hasDerivAt (1 : Mx k r) X 0
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at h1
  exact ((coefL (Hpk k r) v w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

theorem hpart_sum {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H Z + Complex.I • hpart2 H Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [this, ← smul_add]
  have : Z - H⁻¹ * Zᴴ * H + (Z + H⁻¹ * Zᴴ * H) = (2 : ℂ) • Z := by rw [two_smul]; abel
  rw [this, smul_smul]; norm_num

theorem dOp_tensor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (V →L[ℂ] V)} {B : Fin k → (Fin (2 * r + k + 1) → ℂ)}
    {πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))}
    (hπ : IsRepW k r z π) (hπt : IsRepW k r z πt) (hB : IsFrameOf k r [z] B)
    (hf : ∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d))
    {X : Mx k r} (hX : InLieW k r z X) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    dOp πt X y c = dOp π X (y c) + ∑ d, herm (Hpk k r) (X *ᵥ B d) (B c) • y d := by
  have h1 := dOp_hasDeriv hπt.1 hπt.2 hX
  have h2 := dOp_hasDeriv hπ.1 hπ.2 hX
  have h3 : HasDerivAt (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) (dOp πt X y c) 0 :=
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin k => V) c).comp
      (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h4 : ∀ d, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (y d)) (dOp π X (y d)) 0 := fun d =>
    ((ContinuousLinearMap.apply ℂ V (y d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h5 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ => (coef_hasDerivAt X (B d) (B c)).fun_smul (h4 d)
  have h6 : (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) = fun t : ℝ => ∑ d,
      herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ B d) (B c) • π (NormedSpace.exp ((t : ℂ) • X)) (y d) :=
    funext fun t => hf _ (exp_uw hX t) y c
  rw [h6] at h3
  rw [h3.unique h5]
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hπ.1.1, hB.2.1,
    Finset.sum_add_distrib, one_apply_eq_self]
  simp

theorem EB_tensor_std : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsRepW k r z πt → IsFrameOf k r [z] B → (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) → ∀ a b y c, EB πt B a b y c = EB π B a b (y c) + if c = a then y b else 0 := by
  intro V _ _ _ k r z π B πt _ _ hπ hπt hB hf a b y c
  obtain ⟨l1, l2⟩ := frame_lie hB a b
  have e1 := dOp_tensor hπ hπt hB hf l1 y c
  have e2 := dOp_tensor hπ hπt hB hf l2 y c
  have e3 : ∀ d, herm (Hpk k r) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) +
      Complex.I * herm (Hpk k r) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) =
      if d = b then (if c = a then 1 else 0) else 0 := by
    intro d
    rw [← coefL_apply, ← coefL_apply, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _), hpart_sum, coefL_apply,
      Qx8.unitB_mulVec, hB.2.1]
    have := hB.2.1 a c
    by_cases hd : d = b
    · subst hd
      have e : herm (Hpk k r) ((1 : ℂ) • B a) (B c) = herm (Hpk k r) (B a) (B c) := by rw [one_smul]
      rw [if_pos rfl, if_pos rfl, e, this]
      simp only [eq_comm]
    · simp [hd, herm]
  show dOp πt _ y c + Complex.I • dOp πt _ y c = (dOp π _ (y c) + Complex.I • dOp π _ (y c)) + _
  rw [e1, e2, smul_add, Finset.smul_sum, add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  simp only [smul_smul, ← add_smul, e3]
  by_cases hc : c = a <;> simp [hc]

end GlobalTheory.TensorStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionExpandMatrixUnitsStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedAction_expand_matrixUnits : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  first | exact @GlobalTheory.dC_expand_units | exact GlobalTheory.dC_expand_units | (intros; apply GlobalTheory.dC_expand_units <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasicStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_unitary_smooth_basic : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → (∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) ∧ (∀ v, R.σ 1 v = v) ∧ (∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm) ∧ (∀ v ∈ R.TK, v ∈ R.sm) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.TK, R.σ g v ∈ R.TK) ∧ (∀ v, R.KFin v → v ∈ R.TK) ∧ (∃ w, ‖w‖ = 1 ∧ R.KFin w ∧ PI.UpqRep.IsLowUnitH k r ε mu R.σ w) ∧ (∀ v, ContinuousOn (fun g => R.σ g v) (GG k r)) := by
  first | exact @GlobalTheory.rep_basic_of_isDS | exact GlobalTheory.rep_basic_of_isDS | (intros; apply GlobalTheory.rep_basic_of_isDS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyCompatibleStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_tensor_cayley_compatible : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDS ε (muI s)) → TensRaw dualM R RI io pr → IsUnit Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧ (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧ (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧ (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧ (∀ s y d, ((io' s y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • io s c (y : (RI s).H)) ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  first | exact @GlobalTheory.RawTens.rawTens | exact GlobalTheory.RawTens.rawTens | (intros; apply GlobalTheory.RawTens.rawTens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaMul

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem alg {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (C : IsCub θ) (k : ℕ) (a B b x : A)
    (g₁ g g₂ gs gy w w₁ : U) (h₁ : g₂ * θ a b B = g * g₁) (h₂ : gs * θ a (B ^ k) b = g * gy) :
    hv θ k a B (x * b) * (g₁ * w₁) * (hv θ k (a * B ^ k) b x * (gs * w)) =
      hv θ k a (b * B) x * (g₂ * (cubN θ k 1 B b * gy * (w * w₁))) := by
  have e₁ := UUA.hv_comp C k a B b x
  have e₂ := C.N_split k a B b
  have e₃ : hv θ k a B b = cubN θ k a B b * (θ a b B)⁻¹ := rfl
  rw [mul_comm b B]
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  have b₁ := congrArg Additive.ofMul h₁
  have b₂ := congrArg Additive.ofMul h₂
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ - b₁ + b₂

theorem exists_gen_mul {k : ℕ} (p p₁ : QkPt D F k) (b₂ : TF (R := R) F ⟶ D.P.A) (hb : b₂ = p.g.b * p₁.g.b)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w₁ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₁.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw₁ : w₁.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F b₂) (DegPre.lineε k)), w₂.IsGen ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (σ : T ⟶ TF (R := R) F) (z : T.left) (J), Good D.P.L z J →
        val w₂ σ.left z J = cubN (th D z J) k 1 (σ ≫ p₁.g.b) (σ ≫ p.g.b) * val (p.g.s p₁.y) σ.left z J *
          (val w σ.left z J * val w₁ σ.left z J) := by
  obtain ⟨N, hN, vN⟩ := exists_cubN D.cub (1 : TF (R := R) F ⟶ D.P.A) p₁.g.b p.g.b k
  obtain ⟨w₂, hw₂, v₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b₂) (ε' := DegPre.lineε k) (fun U _ h => by
      have l : ∀ b : TF (R := R) F ⟶ D.P.A, ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i =
          h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) := fun b => by
        rw [Fin.prod_univ_two]; rfl
      have g : ∏ i, h (DegPre.gtφ D F p.g.b p₁.y i) ^ DegPre.gtε i =
          h (p₁.g.b ^ k * p.g.b).left ^ (-1 : ℤ) * h (p₁.g.b ^ k).left ^ (1 : ℤ) * h p.g.b.left ^ (1 : ℤ) *
            h (1 : TF (R := R) F ⟶ D.P.A).left ^ (-1 : ℤ) := by
        rw [Fin.prod_univ_four, ← cPoint_y p₁]; rfl
      refine Eq.trans (prod_sum₂ (K := Fin 8 ⊕ Fin 4) (K' := Fin 2 ⊕ Fin 2) (U := U) _
        (prod_sum₂ (K := Fin 8) (K' := Fin 4) (U := U) _ rfl g)
        (prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := U) _ (l _) (l _))) (Eq.trans ?_ (l b₂).symm)
      rw [hb, mul_comm p.g.b p₁.g.b]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (p.g.s p₁.y)) (LB.mulGen D.P.L _ _ _ _ w w₁))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hN (p.g.isGen _)) (mulGen_isGen _ _ _ _ _ _ _ hw hw₁))
  refine ⟨w₂, hw₂, fun T σ z J hJ => ?_⟩
  rw [v₂ _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, vN T σ z J hJ, MonObj.comp_one]

theorem phi_mul_core (hG : GlobalFnsSt) {k : ℕ} (p p₁ p₂ : QkPt D F k) (hy : p₂.y = p.y + p₁.y)
    (hg : p.g.IsAdd p₁.g p₂.g)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w₁ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₁.g.b) (DegPre.lineε k))) (hw : w.IsGen) (hw₁ : w₁.IsGen) :
    ∃ w₂ : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₂.g.b) (DegPre.lineε k)), w₂.IsGen ∧
      ∀ s t t' : Fam D F k, PhiRel D F k p₁ w₁ s t → PhiRel D F k p w t t' → PhiRel D F k p₂ w₂ s t' := by
  have hb : p₂.g.b = p.g.b * p₁.g.b := hg.1
  obtain ⟨w₂, hw₂, v₂⟩ := exists_gen_mul p p₁ p₂.g.b hb w w₁ hw hw₁
  refine ⟨w₂, hw₂, fun s t t' h₁ h => ?_⟩
  rw [phiRel_iff hG _ _ hw₁] at h₁
  rw [phiRel_iff hG _ _ hw] at h
  rw [phiRel_iff hG _ _ hw₂]
  intro α β hαβ T ρ z J hJ
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e := h (α + p₁.y) β (by rw [← hαβ, hy]; abel) T ρ z J hJ
  have e₁ := h₁ α (α + p₁.y) rfl T (ρ ≫ DegPre.trPt D F p.g.b) z J hJ
  have hf : (ρ ≫ DegPre.trPt D F p.g.b) ≫ fst (TF (R := R) F) D.P.A = ρ ≫ fst _ _ := by
    rw [Category.assoc, tr_fst]
  have hp : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.prB D F = (ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b) := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, ← Category.assoc]
  have ht : (ρ ≫ DegPre.trPt D F p.g.b) ≫ DegPre.trPt D F p₁.g.b = ρ ≫ DegPre.trPt D F p₂.g.b := by
    rw [Category.assoc, trPt_mul, hb]
  have hy₁ : cP D T p₁.y = ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k := by
    rw [← comp_cP D (ρ ≫ fst (TF (R := R) F) D.P.A), cPoint_y]; exact map_pow (preHom (ρ ≫ fst (TF (R := R) F) D.P.A)) _ _
  have u₁ : uVal D F k α p₁.g.b (ρ ≫ DegPre.trPt D F p.g.b) z J =
      hv (th D z J) k (cP D T α) ((ρ ≫ fst _ _) ≫ p₁.g.b) ((ρ ≫ DegPre.prB D F) * ((ρ ≫ fst _ _) ≫ p.g.b)) := by
    rw [uVal, hp, ← Category.assoc (ρ ≫ DegPre.trPt D F p.g.b), hf]; rfl
  have u₂ : uVal D F k (α + p₁.y) p.g.b ρ z J =
      hv (th D z J) k (cP D T α * ((ρ ≫ fst _ _) ≫ p₁.g.b) ^ k) ((ρ ≫ fst _ _) ≫ p.g.b) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, cPoint_add, hy₁, ← Category.assoc]; rfl
  have u₃ : uVal D F k α p₂.g.b ρ z J =
      hv (th D z J) k (cP D T α) (((ρ ≫ fst _ _) ≫ p.g.b) * ((ρ ≫ fst _ _) ≫ p₁.g.b)) (ρ ≫ DegPre.prB D F) := by
    rw [uVal, ← Category.assoc, hb, MonObj.comp_mul]; rfl
  have g₁ : val (p₂.g.s α) (ρ ≫ fst _ _).left z J *
      th D z J (cP D T α) ((ρ ≫ fst _ _) ≫ p.g.b) ((ρ ≫ fst _ _) ≫ p₁.g.b) =
      val (p.g.s α) (ρ ≫ fst _ _).left z J * val (p₁.g.s α) (ρ ≫ fst _ _).left z J := by
    have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hg.2 α) (ρ ≫ fst (TF (R := R) F) D.P.A).left).trans
      (val_mul hJ _ _ _))
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
    refine Eq.trans ?_ (val_cub D.cub (ρ ≫ fst (TF (R := R) F) D.P.A) hJ (cP D _ α) p.g.b p₁.g.b).symm
    rw [comp_cP]
  have g₂ := gt_mul (ρ ≫ fst (TF (R := R) F) D.P.A) hJ p.g α p₁.y
  rw [hy₁] at g₂
  rw [ht, hf, u₁, val_mul hJ] at e₁
  rw [e₁, u₂, val_mul hJ, _root_.mul_assoc, ← Units.val_mul, alg C k _ _ _ _ _ _ _ _ _ _ _ g₁ g₂] at e
  rw [e, u₃, val_mul hJ, v₂ T _ z J hJ]

end GlobalTheory.ThetaMul

namespace GlobalTheory

theorem phi_mul : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ p p₁ p₂ : QkPt D.toPre F k, p₂.y = p.y + p₁.y → p.g.IsAdd p₁.g p₂.g → ∀ (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (w₁ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₁.g.b) (DegPre.lineε k))), w.IsGen → w₁.IsGen → ∃ w₂ : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₂.g.b) (DegPre.lineε k)), w₂.IsGen ∧ ∀ s t t' : Fam D.toPre F k, PhiRel D.toPre F k p₁ w₁ s t → PhiRel D.toPre F k p w t t' → PhiRel D.toPre F k p₂ w₂ s t' := by
  intro hL V _ _ _ D F _ _ k _ p p₁ p₂ hy hg w w₁ hw hw₁
  exact ThetaMul.phi_mul_core hL.globalFns p p₁ p₂ hy hg w w₁ hw hw₁

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitaryWFrameToFrame
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P

namespace GlobalTheory.FrameTrans

variable {k r : ℕ}

noncomputable def swapMat (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (B B' : Fin k → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  1 + Matrix.of fun p q => ∑ c, (B' c p - B c p) * herm H (bvec q) (B c)

end GlobalTheory.FrameTrans

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntertwinerDOpOfStabiliser
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

namespace GlobalTheory

theorem intertwiner_dOp_of_stabiliser {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁]
    [FiniteDimensional ℂ V₁] {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂]
    [FiniteDimensional ℂ V₂] {k r : ℕ} {z e : Fin (2 * r + k + 1) → ℂ}
    {π₁ : Mx k r → (V₁ →L[ℂ] V₁)} {π₂ : Mx k r → (V₂ →L[ℂ] V₂)} (T : V₁ →L[ℂ] V₂)
    (h₁ : IsRepW k r z π₁) (h₂ : IsRepW k r z π₂)
    (hT : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, T (π₁ h v) = π₂ h (T v))
    {X : Mx k r} (hX : InLieW k r z X) (he : X *ᵥ e = 0) (v : V₁) :
    T (dOp π₁ X v) = dOp π₂ X (T v) := by
  have d₁ := dOp_hasDeriv h₁.1 h₁.2 hX
  have d₂ := dOp_hasDeriv h₂.1 h₂.2 hX
  have e₁ := ((T.comp (ContinuousLinearMap.apply ℂ V₁ v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) d₁
  have e₂ := ((ContinuousLinearMap.apply ℂ V₂ (T v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) d₂
  have hf : (((T.comp (ContinuousLinearMap.apply ℂ V₁ v)).restrictScalars ℝ) ∘
      fun t : ℝ => π₁ (NormedSpace.exp ((t : ℂ) • X))) =
      (((ContinuousLinearMap.apply ℂ V₂ (T v)).restrictScalars ℝ) ∘
      fun t : ℝ => π₂ (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact hT _ (exp_uw hX t) (Qx8.exp_fix he t) v
  rw [hf] at e₁
  exact e₁.unique e₂

theorem intertwiner_EB_of_stabiliser : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] (k r m : ℕ) (z e : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (T : V₁ →L[ℂ] V₂) (B : Fin m → (Fin (2 * r + k + 1) → ℂ)), IsRepW k r z π₁ → IsRepW k r z π₂ → IsFrameOf k r [z, e] B → (∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, T (π₁ h v) = π₂ h (T v)) → ∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v) := by
  intro V₁ _ _ _ V₂ _ _ _ k r m z e π₁ π₂ T B h₁ h₂ hB hT a b v
  have hz : IsFrameOf k r [z] B := ⟨hB.1, hB.2.1, fun c y hy => hB.2.2 c y (by simp at hy; simp [hy])⟩
  have he : IsFrameOf k r [e] B := ⟨hB.1, hB.2.1, fun c y hy => hB.2.2 c y (by simp at hy; simp [hy])⟩
  have lz := frame_lie hz a b
  have le := frame_lie he a b
  have p1 := intertwiner_dOp_of_stabiliser T h₁ h₂ hT lz.1 le.1.2 v
  have p2 := intertwiner_dOp_of_stabiliser T h₁ h₂ hT lz.2 le.2.2 v
  show T (ecOp π₁ (unitB (Hpk k r) B a b) v) = ecOp π₂ (unitB (Hpk k r) B a b) (T v)
  unfold ecOp
  simp only [_root_.add_apply, _root_.smul_apply, map_add (f := _), map_smul, p1, p2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModelStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  first | exact @GlobalTheory.quotMeas_ae_mem_and_measurable | exact GlobalTheory.quotMeas_ae_mem_and_measurable | (intros; apply GlobalTheory.quotMeas_ae_mem_and_measurable <;> assumption)
end

