module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndProdG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0085
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.IndAmb
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem indF_stable {G H Y : Type} [Group G] [Group H] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace G]
    [IsTopologicalGroup G] (j : H →* G) (y : Representation ℂ H Y) (X : Submodule ℂ Y) (g : G) (f : G → Y)
    (hf : f ∈ IndF j y X) : rightReg ℂ G Y g f ∈ IndF j y X := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  refine ⟨⟨fun x => h1 (x * g), fun h x => ?_⟩, ?_⟩
  · show f (j h * x * g) = y h (f (x * g))
    rw [mul_assoc, h2]
  · have h4 : IsOpen {a : G | rightReg ℂ G Y a f = f} := h3
    have h5 := h4.preimage (f := fun a : G => g⁻¹ * a * g) (by fun_prop)
    show IsOpen {a : G | rightReg ℂ G Y a (rightReg ℂ G Y g f) = rightReg ℂ G Y g f}
    convert h5 using 1
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      funext x
      have := congrFun h (x * g⁻¹)
      change f (x * g⁻¹ * a * g) = f (x * g⁻¹ * g) at this
      change f (x * (g⁻¹ * a * g)) = f x
      simpa [mul_assoc] using this
    · intro h
      funext x
      have := congrFun h (x * g)
      change f (x * g * (g⁻¹ * a * g)) = f (x * g) at this
      change f (x * a * g) = f (x * g)
      simpa [mul_assoc] using this

private theorem simple_of_sub {G H Y : Type} [Group G] [Group H] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace G]
    [IsTopologicalGroup G] (j : H →* G) (y : Representation ℂ H Y) (X : Submodule ℂ Y) (y' : Representation ℂ H X)
    (hy : ∀ h v, (y' h v : Y) = y h v)
    (H' : ∀ Q ≤ IndF j y' ⊤, (∀ g, ∀ f ∈ Q, rightReg ℂ G X g f ∈ Q) → Q = ⊥ ∨ Q = IndF j y' ⊤) :
    SimpleIn (rightReg ℂ G Y) (IndF j y X) := by
  refine ⟨fun g f hf => indF_stable j y X g f hf, fun Q hQ hst => ?_⟩
  let Φ : (G → X) →ₗ[ℂ] (G → Y) := X.subtype.compLeft G
  have hΦ : ∀ f x, Φ f x = (f x : Y) := fun _ _ => rfl
  have hmem : ∀ f, f ∈ IndF j y' ⊤ ↔ Φ f ∈ IndF j y X := by
    intro f
    have hs : {a : G | rightReg ℂ G X a f = f} = {a : G | rightReg ℂ G Y a (Φ f) = Φ f} := by
      ext a
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        funext x
        exact congrArg Subtype.val (congrFun h x)
      · intro h
        funext x
        exact Subtype.ext (congrFun h x)
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩
      refine ⟨⟨fun x => (f x).2, fun h x => ?_⟩, ?_⟩
      · rw [hΦ, hΦ, h2, hy]
      · have h4 : IsOpen {a : G | rightReg ℂ G X a f = f} := h3
        rw [hs] at h4
        exact h4
    · rintro ⟨⟨-, h2⟩, h3⟩
      refine ⟨⟨fun x => trivial, fun h x => Subtype.ext ?_⟩, ?_⟩
      · rw [hy]
        exact h2 h x
      · have h4 : IsOpen {a : G | rightReg ℂ G Y a (Φ f) = Φ f} := h3
        rw [← hs] at h4
        exact h4
  have hsurj : ∀ F ∈ IndF j y X, ∃ f, Φ f = F := fun F hF => ⟨fun x => ⟨F x, hF.1.1 x⟩, rfl⟩
  rcases H' (Q.comap Φ) (fun f hf => (hmem f).2 (hQ hf)) (fun g f hf => hst g (Φ f) hf) with h | h
  · left
    rw [eq_bot_iff]
    intro F hF
    obtain ⟨f, rfl⟩ := hsurj F (hQ hF)
    have : f ∈ Q.comap Φ := hF
    rw [h, Submodule.mem_bot] at this
    rw [this, map_zero]
    exact Submodule.zero_mem _
  · right
    refine le_antisymm hQ fun F hF => ?_
    obtain ⟨f, rfl⟩ := hsurj F hF
    have : f ∈ Q.comap Φ := by
      rw [h]
      exact (hmem f).2 hF
    exact this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.indAmb :
    ∀ {r : ℕ} {G : Fin r → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] (P : ∀ i, Subgroup (G i)) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
      (y : Representation ℂ (∀ i, P i) Y) (X : Submodule ℂ Y), SimpleIn y X → (∀ v ∈ X, IsOpen {p : ∀ i, P i | y p v = v}) →
      (∀ i, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (P i) V) (f : V →ₗ[ℂ] Y), LocOk (P i) ρ ∧ f ≠ 0 ∧ (∀ v, f v ∈ X) ∧
        ∀ p v, f (ρ p v) = y (Pi.mulSingle i p) (f v)) →
      SimpleIn (rightReg ℂ (∀ i, G i) Y) (IndF (piIncl P) y X) := by
  intro r G _ _ _ P Y _ _ y X hX hop hloc
  by_cases h0 : X = ⊥
  · refine ⟨fun g f hf => indF_stable _ y X g f hf, fun Q hQ _ => Or.inl ?_⟩
    rw [eq_bot_iff]
    intro F hF
    rw [Submodule.mem_bot]
    funext x
    have := (hQ hF).1.1 x
    rw [h0, Submodule.mem_bot] at this
    exact this
  let y' : Representation ℂ ((∀ i, P i) × PUnit.{1}) X := (GlobalTheory.PRep.sub y X hX.1).comp (MonoidHom.fst _ _)
  have hy : ∀ a (v : X), (y' a v : Y) = y a.1 v := fun _ _ => rfl
  have hirr : y'.IsIrreducible := by
    have : Nontrivial X := Submodule.nontrivial_iff_ne_bot.2 h0
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
    · exact bot_ne_top (α := Submodule ℂ X) (congrArg Subrepresentation.toSubmodule h)
    · rcases hX.2 (S.toSubmodule.map X.subtype) (Submodule.map_subtype_le _ _) (by
        rintro g _ ⟨v, hv, rfl⟩
        exact ⟨y' (g, 1) v, S.apply_mem_toSubmodule _ hv, rfl⟩) with h | h
      · left
        apply Subrepresentation.toSubmodule_injective
        apply Submodule.map_injective_of_injective X.injective_subtype
        rw [h]
        exact (Submodule.map_bot _).symm
      · right
        apply Subrepresentation.toSubmodule_injective
        apply Submodule.map_injective_of_injective X.injective_subtype
        rw [h]
        exact (Submodule.map_subtype_top _).symm
  have key := indProdG r P y' hirr (fun v => by
      convert hop v v.2 using 2 with p
      exact funext fun p => propext Subtype.ext_iff) (fun i => by
      obtain ⟨V, _, _, ρ, f, h1, h2, h3, h4⟩ := hloc i
      refine ⟨V, inferInstance, inferInstance, ρ, f.codRestrict X h3, h1, fun h => h2 ?_, fun p v => Subtype.ext (h4 p v)⟩
      ext v
      exact congrArg Subtype.val (LinearMap.congr_fun h v))
  refine simple_of_sub (piIncl P) y X (y'.comp (MonoidHom.inl _ _)) (fun _ _ => rfl) fun Q hQ hst => key Q hQ hst fun c f hf => ?_
  have : (fun x => y' (1, c) (f x)) = f := by
    funext x
    apply Subtype.ext
    rw [hy]
    simp
  rw [this]
  exact hf
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.OpenStab
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.xMem :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ : Measure (G1 K 2)) [μ.IsHaarMeasure] (τ : Submodule ℂ (L2 μ)) (κ : Measure (archCompact K 2)) (p : archCompact K 2 → ℂ), IdemA κ p → (∀ S φ, φ ∈ Xs μ τ κ p S ↔ IsX μ τ κ p S φ) ∧ (CuspIrr μ τ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι : GS 2 w →* FA K 2), Function.Injective w → IsEmb w ι → ∀ φ ∈ Xs μ τ κ p (im w), IsOpen {g | rS ι g φ = φ} ∧ ∀ g, rS ι g φ ∈ Xs μ τ κ p (im w)) :=
  _root_.UpperTheory.Reformulated.B.Gul4.xMem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RepsSmul
section
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

private theorem reps_smul {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) (φ : G1 K n → ℂ) (c : ℂ)
    (h : ∃ v ∈ τ, Reps μ v φ) : ∃ v ∈ τ, Reps μ v (fun y => c * φ y) := by
  obtain ⟨w, hw, hq⟩ := h
  refine ⟨c • w, τ.smul_mem _ hw, ?_⟩
  filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_smul c w), hq] with y e2 e4
  rw [e2, Pi.smul_apply, e4, smul_eq_mul]

private theorem zt_zero' : zt K 0 = 1 := by
  have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext (by simp)
  rw [zt, this, map_one]

private theorem lv_zero' (m₁ m₂ : G1 K 2) :
    ((lv m₁ m₂ 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (m₁ : AdelicGLn.AdelicGL K 2) (m₂ : AdelicGLn.AdelicGL K 2) := by
  rw [blkLaws.1, neg_zero, zt_zero', mul_one, mul_one]

private theorem lv_ray' (r : {r : ℝ // 0 < r}) :
    ((lv 1 1 (Real.log r.1) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (centralSection K 2 r) (centralSection K 2 r⁻¹) := by
  have h := Real.exp_log r.2
  have h1 : (⟨Real.exp (Real.log r.1), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = r := Subtype.ext h
  have h2 : (⟨Real.exp (-Real.log r.1), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = r⁻¹ := by
    apply Subtype.ext
    change Real.exp (-Real.log r.1) = r.1⁻¹
    rw [Real.exp_neg, h]
  rw [blkLaws.1, zt, zt, h1, h2]
  simp

private theorem nn_zero : nn (K := K) 0 = 1 := unipOne_zero 2

private theorem hh_lv (m₁ m₂ : G1 K 2) (t : ℝ) (g : G1 K (2 + 2)) : HH (lv m₁ m₂ t * g) = t + HH g := by
  have := (hpSpec (K := K)).1 0 m₁ m₂ t g
  rwa [nn_zero, one_mul] at this

private theorem hh_nn (X : UPos (2 + 2) 2 → AdeleRing (𝓞 K) K) (g : G1 K (2 + 2)) : HH (nn X * g) = HH g := by
  have := (hpSpec (K := K)).1 X 1 1 0 g
  rwa [blkLaws.2.2.1, mul_one, zero_add] at this

private theorem arc_mem {n : ℕ} (k : archCompact K n) : arc1 k ∈ KG K n := by
  have hk : infEmb K n k ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) := k.2
  have h := congrArg Subtype.val (retractOne_coe (⟨_, maxCompact_le_normOneGL hk⟩ : normOneGL (K := K) (n := n)))
  change ((retractOne (infEmb K n k) : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact
  exact h ▸ hk

private theorem fin_mem {n : ℕ} {u : FA K n} (hu : u ∈ AdelicGLn.integralFiniteGL K n) : fin1 u ∈ KG K n := by
  unfold fin1
  rw [MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL (finEmb_mem_maxCompact hu))]
  exact finEmb_mem_maxCompact hu

private theorem flat_k (f : G1 K (2 + 2) → ℂ) (g : G1 K (2 + 2)) {k : G1 K (2 + 2)} (hk : k ∈ KG K (2 + 2)) :
    flat 0 f (g * k) = Complex.exp ((0 + 2) * (HP 2 2 g : ℂ)) * f (g * k) := by
  have : HP 2 2 (g * k) = HP 2 2 g := ((hpSpec (K := K)).2.1 k hk).2 g
  rw [flat, this]

private theorem fixA_flat (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) (f : G1 K (2 + 2) → ℂ) :
    FixA κ e (flat 0 f) ↔ FixA κ e f := by
  refine forall_congr' fun g => ?_
  simp only [flat_k f g (arc_mem _), mul_left_comm (e _)]
  rw [integral_const_mul, flat, mul_right_inj' (Complex.exp_ne_zero _)]

private theorem sec_tr {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {f : G1 K (2 + 2) → ℂ}
    (hf : IsSec τ₁ τ₂ f) (y : G1 K (2 + 2)) :
    IsSec τ₁ τ₂ fun x => Complex.exp (2 * ((HH (x * y) - HH x : ℝ) : ℂ)) * f (x * y) := by
  obtain ⟨-, -, -, hc, hb⟩ := hpSpec (K := K)
  refine ⟨?_, ?_, fun X g => ?_, fun r x g hx => ?_, fun g => ?_⟩
  · exact ((continuous_const.mul (Complex.continuous_ofReal.comp ((hc.comp (continuous_mul_const y)).sub hc))).cexp).mul
      (hf.cont.comp (continuous_mul_const y))
  · obtain ⟨R, hR⟩ := hb {y} isCompact_singleton
    obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨Real.exp (2 * R) * C, fun g => ?_⟩
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul (Real.exp_le_exp.2 ?_) (hC _) (norm_nonneg _) (Real.exp_pos _).le
    have := (le_abs_self _).trans (hR g y rfl)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    linarith
  · rw [mul_assoc, hh_nn, hh_nn, hf.unip]
  · have e : x = lv 1 1 (Real.log r.1) * g := Subtype.ext (by rw [hx, Subgroup.coe_mul, lv_ray'])
    have e2 : f (x * y) = f (g * y) := hf.ray r _ _ (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, mul_assoc])
    beta_reduce
    rw [e2, e, mul_assoc, hh_lv, hh_lv, add_sub_add_left_eq_sub]
  · obtain ⟨d, φ, ψ, hφ, hψ, hx⟩ := hf.levi (g * y)
    refine ⟨d, fun i m => Complex.exp (2 * ((HH (g * y) - HH g : ℝ) : ℂ)) * φ i m, ψ,
      fun i => ⟨continuous_const.mul (hφ i).1, reps_smul _ _ _ _ (hφ i).2⟩, hψ, fun m₁ m₂ x h => ?_⟩
    have e : x = lv m₁ m₂ 0 * g := Subtype.ext (by rw [h, Subgroup.coe_mul, lv_zero'])
    have e2 := hx m₁ m₂ (x * y) (by rw [Subgroup.coe_mul, Subgroup.coe_mul, h, mul_assoc])
    beta_reduce
    rw [e2, e, mul_assoc, hh_lv, hh_lv, add_sub_add_left_eq_sub, Finset.mul_sum]
    simp only [mul_assoc]

private theorem sec_add {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure] {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {f f' : G1 K (2 + 2) → ℂ}
    (hf : IsSec τ₁ τ₂ f) (hf' : IsSec τ₁ τ₂ f') (c : ℂ) : IsSec τ₁ τ₂ (f + c • f') :=
  _root_.UpperTheory.Reformulated.B.Glb3.sec_add hf hf' c

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.secTr :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ), IdemA κ e → (IsSec τ₁ τ₂ 0 ∧ ∀ f f', IsSec τ₁ τ₂ f → IsSec τ₁ τ₂ f' → ∀ c : ℂ, IsSec τ₁ τ₂ (f + c • f')) ∧
      (∀ f : G1 K (2 + 2) → ℂ, Continuous f → (FixA κ e (flat 0 f) ↔ FixA κ e f) ∧
        ∀ U : Subgroup (FA K (2 + 2)), U ≤ AdelicGLn.integralFiniteGL K (2 + 2) → (FixF U (flat 0 f) ↔ FixF U f)) ∧
      (∀ f f' : G1 K (2 + 2) → ℂ, flat 0 f = flat 0 f' → f = f') ∧
      ∀ f (h : FA K (2 + 2)), IsSec τ₁ τ₂ f → FixA κ e f → ∃ f', IsSec τ₁ τ₂ f' ∧ FixA κ e f' ∧ ∀ x, flat 0 f' x = flat 0 f (x * fin1 h) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e _
  refine ⟨⟨⟨continuous_const, ⟨0, fun g => by simp⟩, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun g => ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun _ _ _ _ => by simp⟩⟩,
    fun f f' hf hf' c => sec_add hf hf' c⟩, fun f _ => ⟨fixA_flat κ e f, fun U hU => ?_⟩, fun f f' h => ?_, fun f h hf hA => ?_⟩
  · refine forall₂_congr fun u hu => forall_congr' fun g => ?_
    rw [flat_k f g (fin_mem (hU hu)), flat, mul_right_inj' (Complex.exp_ne_zero _)]
  · funext x
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) (congrFun h x)
  · have key : ∀ x, flat 0 (fun x => Complex.exp (2 * ((HH (x * fin1 h) - HH x : ℝ) : ℂ)) * f (x * fin1 h)) x =
        flat 0 f (x * fin1 h) := fun x => by
      simp only [flat]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    refine ⟨_, sec_tr hf (fin1 h), (fixA_flat κ e _).1 fun g => ?_, key⟩
    have hc : ∀ k : archCompact K (2 + 2), g * arc1 k * fin1 h = g * fin1 h * arc1 k := fun k => by
      rw [mul_assoc, mul_assoc]
      exact congrArg (g * ·) (MultiplicityOne.finProj_mul_archProj_comm h _).symm
    simp only [key, hc]
    exact (fixA_flat κ e f).2 hA _
end

