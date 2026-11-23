module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0091
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0092

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapIntegrability
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem be_apply_isBes : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∀ v ∈ R.TK, ∀ ξ : Wp, IsBes R z π (fun w => be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v ξ) := by
  intro hH k r ε mu h R Wp _ _ _ _ z π u μW μN μG νq hDS hgap hok hS v hv ξ
  obtain ⟨-, C, Ws, hWs, hC⟩ := GlobalTheory.T.besselIntegral_integrable_and_cwContinuous_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv
  obtain ⟨hlin, -⟩ := GlobalTheory.T.bessel_gap_pairing hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS
  have heq := GlobalTheory.T.bessel_integral_equivariant_of_gap hH k r ε mu h R Wp z π u μW μN μG νq hDS hgap hok hS v hv
  refine ⟨fun w hw w' hw' => ?_, fun a w hw => ?_, fun g hg m hm w hw => ?_, ‖ξ‖ * C, Ws, hWs, fun w hw => ?_⟩
  · simp only [(hlin v hv w hw w' hw' 0).1, ContinuousLinearMap.add_apply]
  · simp only [(hlin v hv w hw w hw a).2, ContinuousLinearMap.smul_apply]
  · simp only [heq w hw g hg m hm, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [mul_comm, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingGapBoundStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_orbital_integral_factors_through_left_functional : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ A : R.H → Wq → Wq → Wp, (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = A y (ContinuousLinearMap.adjoint X (l x)) c := by
  first | exact @GlobalTheory.BesselFirstLeft.bessel_integrate_left | exact GlobalTheory.BesselFirstLeft.bessel_integrate_left | (intros; apply GlobalTheory.BesselFirstLeft.bessel_integrate_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyEndomorphismsModularStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayley_endomorphisms_modular : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), 1 ≤ k → R.IsDS ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → IsMod ε E mu := by
  first | exact @GlobalTheory.isMod_smooth_of_isDS | exact GlobalTheory.isMod_smooth_of_isDS | (intros; apply GlobalTheory.isMod_smooth_of_isDS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorBesselMomentStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_tensor_bessel_moment : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (RI : Fin (2 * r + k + 1) → Rep k r) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp), 1 ≤ k → R.IsDS ε mu → (∀ s, (RI s).IsDS ε (mu - Pi.single s 1)) → TensRaw dualM R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π l → ∀ s, ∃ c : ℂ, ‖c‖ = Formalism.QuantumDeterminants.Tz k r z * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ v ∈ R.sm, l (ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (fun c' => io s c' (∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d)))) = c • l v := by
  first | exact @GlobalTheory.bessel_ev_projector_value | exact GlobalTheory.bessel_ev_projector_value | (intros; apply GlobalTheory.bessel_ev_projector_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivPointsOfIsPowGrp
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem nonempty_tateIso_of_mulEquiv_pi {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (Dw Dw' : Datum H) (j : ℕ) (e : Dw'.La ≃ₗ[𝓞 E] (Fin j → Dw.La))
    (he : ∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i))
    (F : Type) [Field F] (Q Q' : Type) [Group Q] [Group Q'] (φ : Q' ≃* (Fin j → Q))
    (act : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (hact : ∀ a x i, φ (act' a x) i = act a (φ x i))
    (w : ℕ → Q → Q → Fˣ → Prop) (w' : ℕ → Q' → Q' → Fˣ → Prop)
    (hw : ∀ k, 0 < k → ∀ (x x' : Q') (c : Fin j → Fˣ), (∀ i, w k (φ x i) (φ x' i) (c i)) → w' k x x' (∏ i, c i))
    (I : TateIso Dw F Q act w) : Nonempty (TateIso Dw' F Q' act' w') := by
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow
            ev := fun n a => φ.symm (fun i => I.ev n (e a i))
            add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }⟩
  · intro n a b
    rw [← map_mul]
    congr 1
    funext i
    simp [I.add]
  · intro n c a
    apply φ.injective
    funext i
    simp [hact, I.lin]
  · intro n hn a
    rw [MulEquiv.map_eq_one_iff, funext_iff]
    simp only [Pi.one_apply, I.ker n hn]
    constructor
    · intro h
      choose b hb using h
      refine ⟨e.symm b, e.injective ?_⟩
      funext i
      simp [hb i]
    · rintro ⟨b, rfl⟩ i
      exact ⟨e b i, by simp⟩
  · intro n hn x
    rw [← φ.map_eq_one_iff, map_pow, funext_iff]
    simp only [Pi.pow_apply, Pi.one_apply, I.onto n hn]
    constructor
    · intro h
      choose b hb using h
      refine ⟨e.symm b, φ.injective ?_⟩
      funext i
      simp [hb i]
    · rintro ⟨a, rfl⟩ i
      exact ⟨e a i, by simp⟩
  · intro n m hn hm a
    rw [← map_pow]
    congr 1
    funext i
    simp [I.tower n m hn hm]
  · intro n hn a b
    have hz : I.ζ n ^ Dw'.EF a b = ∏ i, I.ζ n ^ Dw.EF (e a i) (e b i) := by
      rw [he]
      exact map_prod (zpowersHom Fˣ (I.ζ n)) (fun i => Multiplicative.ofAdd (Dw.EF (e a i) (e b i))) Finset.univ
    rw [hz]
    apply hw n hn
    intro i
    simpa using I.isom n hn (e a i) (e b i)

theorem exists_mulEquiv_points_of_isPowGrp {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) (T : Over S) :
    ∃ φ : (T ⟶ G') ≃* (Fin j → (T ⟶ G)), ∀ x i, φ x i = x ≫ p.pr i := by
  let f : (T ⟶ G') →* (Fin j → (T ⟶ G)) := MonoidHom.mk' (fun x i => x ≫ p.pr i) (by
    intro x y
    funext i
    have := p.hom i
    exact MonObj.mul_comp x y (p.pr i))
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply p.lim.hom_ext
      rintro ⟨i⟩
      exact congrFun h i
    · intro y
      refine ⟨p.lim.lift (Fan.mk T y), ?_⟩
      funext i
      exact p.lim.fac (Fan.mk T y) ⟨i⟩
  exact ⟨MulEquiv.ofBijective f hf, fun _ _ => rfl⟩

theorem exists_tateIso_of_isPowPolAV : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (act : 𝓞 E → (A.A ⟶ A.A)) (act' : 𝓞 E → (A'.A ⟶ A'.A)), (∀ a i, act' a ≫ pA.pr i = pA.pr i ≫ act a) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := R) F ⟶ A.A) (fun a x => x ≫ act a) (fun k x x' z => WeilIs A.A A.L k x x' (unitOn z))), ∃ Dw' : Datum H, Nonempty (TateIso Dw' F (TFK (R := R) F ⟶ A'.A) (fun a x => x ≫ act' a) (fun k x x' z => WeilIs A'.A A'.L k x x' (unitOn z))) := by
  intro h1 h2 h4 htw E _ _ _ H R _ _ j A A' pA F _ _ act act' hact Dw I
  obtain ⟨Dw', e, he, -, -⟩ := _root_.GlobalTheory.exists_datum_pow E H Dw j
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_points_of_isPowGrp pA.toIsPowGrp (TFK (R := R) F)
  refine ⟨Dw', nonempty_tateIso_of_mulEquiv_pi Dw Dw' j e he F _ _ φ _ _ ?_ _ _ ?_ I⟩
  · intro a x i
    simp only [hφ, Category.assoc, hact]
  · intro k hk x x' c hc
    simp only [hφ] at hc
    exact GlobalTheory.T.weilPairing_powPolAV_eq_prod_field h1 h2 h4 htw R j A A' pA F k hk x x' c hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainLowering
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh


open Matrix in
theorem _root_.GlobalTheory.WigSh.exists_wigMap_chain_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : _root_.Formalism.FourierDecayAlt.Q.Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), _root_.Formalism.QuantumDeterminants.inWb (n + 1) r z → 0 < _root_.Formalism.QuantumDeterminants.Tz (n + 1) r z → _root_.Formalism.FourierDecayAlt.Q.IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → _root_.Formalism.FourierDecayAlt.Q.IsFrameOf (n + 1) r [z] B → (∀ j, j > l → L j < L l - (n₀ : ℤ)) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : _root_.Formalism.FourierDecayAlt.Q.Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), _root_.Formalism.FourierDecayAlt.Q.IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - (n₀ : ℝ))) ∧ _root_.GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ _root_.Formalism.FourierDecayAlt.Qr.CapSp (_root_.Formalism.FourierDecayAlt.Qr.subA (_root_.Formalism.FourierDecayAlt.Qr.EB π B)) (_root_.Formalism.FourierDecayAlt.Qr.shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, _root_.GlobalTheory.WigSh.wM (Function.update L l (L l - (j : ℤ))) M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l n₀
  induction n₀ with
  | zero =>
    intro hz hT hType hL hrel hB hgap
    refine ⟨V, inferInstance, inferInstance, inferInstance, π, fun _ => ContinuousLinearMap.id ℂ V,
      ?_, ?_, ?_⟩
    · simpa using hType
    · exact _root_.GlobalTheory.WigSh.wigMap_zero_of_contraction V V (n + 1) r z π π
        (ContinuousLinearMap.id ℂ V) (fun v => le_rfl) (fun h _ v => rfl)
    · intro M v _
      simp only [Finset.prod_range_zero, Complex.ofReal_one, one_smul,
        ContinuousLinearMap.id_apply]
      refine ext_inner_left ℂ fun w => ?_
      rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.id_apply]
  | succ m ih =>
    intro hz hT hType hL hrel hB hgap
    have hm : (0 : ℤ) ≤ m := Nat.cast_nonneg m
    have hgap' : ∀ j, j > l → L j < L l - (m : ℤ) := fun j hj => by
      have := hgap j hj
      push_cast at this
      linarith
    obtain ⟨V₁, i₁, i₂, i₃, π₁, A₁, hType₁, hA₁, hprod₁⟩ := ih hz hT hType hL hrel hB hgap'
    set L₁ := Function.update L l (L l - m) with hL₁def
    set u₁ := Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - m) with hu₁def
    have hL₁ : StrictAnti L₁ := by
      intro a b hab
      by_cases ha : a = l
      · subst ha
        have hb : b ≠ a := ne_of_gt hab
        rw [hL₁def, Function.update_self, Function.update_of_ne hb]
        have := hgap b hab
        push_cast at this
        linarith
      · by_cases hb : b = l
        · subst hb
          rw [hL₁def, Function.update_self, Function.update_of_ne ha]
          have := hL hab
          linarith
        · rw [hL₁def, Function.update_of_ne ha, Function.update_of_ne hb]
          exact hL hab
    have hne₁ : ∀ j : Fin (n + 1), L₁ j ≠ L₁ l - 1 := by
      intro j
      by_cases hj : j = l
      · subst hj
        omega
      · rw [hL₁def, Function.update_self, Function.update_of_ne hj]
        rcases lt_or_gt_of_ne hj with h | h
        · have := hL h
          omega
        · have := hgap j h
          push_cast at this
          omega
    have hrel₁ : ∀ j : Fin (n + 1),
        (u₁ ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L₁ j : ℂ) := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [hu₁def, hL₁def, Function.update_self, Function.update_self]
        have := hrel j
        push_cast at this ⊢
        linear_combination this
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [hu₁def, hL₁def, Function.update_of_ne hj, Function.update_of_ne hj']
        exact hrel j
    obtain ⟨V₂, j₁, j₂, j₃, π₂, A₂, hType₂, hA₂, hprod₂⟩ :=
      _root_.GlobalTheory.WignerStepLower.wigner_step_lowering V₁ n r z π₁ u₁ β L₁ B l hz hT hType₁ hL₁ hrel₁ hB hne₁
    refine ⟨V₂, j₁, j₂, j₃, π₂, fun ω => (A₁ ω).comp (A₂ ω), ?_,
      _root_.GlobalTheory.WigSh.wigMap_comp V V₁ V₂ (n + 1) r z π π₁ π₂ m 1 A₁ A₂ hA₁ hA₂, ?_⟩
    · have key : Function.update u₁ ((l : ℕ) + 1) (u₁ ((l : ℕ) + 1) - 1) =
          Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - ((m + 1 : ℕ) : ℝ)) := by
        rw [hu₁def, Function.update_idem, Function.update_self]
        congr 1
        push_cast
        ring
      rw [← key]
      exact hType₂
    · intro M v hv
      have hadj := _root_.GlobalTheory.adjoint_mem_CapSp_subA V V₁ n r z π π₁ B
        (A₁ (B (Fin.last n))) (_root_.Formalism.FourierDecayAlt.Qr.shf β M) ⟨hType.2.1, hType.2.2.1⟩ ⟨hType₁.2.1, hType₁.2.2.1⟩
        hType.2.2.2.1 hType₁.2.2.2.1 hB
        (fun h hh hfix => by
          have := hA₁.2.1 h hh (B (Fin.last n))
          rwa [hfix] at this) v hv
      simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
      rw [hprod₂ M _ hadj, map_smul, hprod₁ M v hv, Finset.prod_range_succ, Complex.ofReal_mul,
        mul_comm, mul_smul]

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaising
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem chain_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j < l → L l + (n₀ : ℤ) < L j) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L l (L l + (j : ℤ))) M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l n₀ hz hT hπ hL hu hB
  induction n₀ with
  | zero =>
    intro _
    refine ⟨V, inferInstance, inferInstance, inferInstance, π, fun _ => ContinuousLinearMap.id ℂ V, ?_, ?_, ?_⟩
    · simpa using hπ
    · exact wigMap_zero_of_contraction V V (n + 1) r z π π _ (fun v => le_rfl) (fun h _ v => rfl)
    · intro M v _
      simp [ContinuousLinearMap.adjoint_id]
  | succ m ih =>
    intro hreg
    obtain ⟨V₂, i1, i2, i3, π₂, A, hπ₂, hA, hAA⟩ := ih (fun j hj => by
      have := hreg j hj
      push_cast at this
      omega)
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    have hL' : StrictAnti (Function.update L l (L l + (m : ℤ))) := by
      intro a b hab
      have h1 := hL hab
      by_cases ha : a = l
      · have hb : b ≠ l := fun hb => hab.ne (ha.trans hb.symm)
        subst ha
        rw [Function.update_self, Function.update_of_ne hb]
        omega
      · by_cases hb : b = l
        · subst hb
          rw [Function.update_self, Function.update_of_ne ha]
          have := hreg a hab
          push_cast at this
          omega
        · rw [Function.update_of_ne ha, Function.update_of_ne hb]
          exact h1
    have hu' : ∀ j : Fin (n + 1),
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (m : ℝ)) ((j : ℕ) + 1) : ℝ) : ℂ) -
          ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + ((Function.update L l (L l + (m : ℤ)) j : ℤ) : ℂ) := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self, Function.update_self]
        have := hu j
        push_cast at this ⊢
        linear_combination this
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
        exact hu j
    have hreg' : ∀ j, Function.update L l (L l + (m : ℤ)) j ≠ Function.update L l (L l + (m : ℤ)) l + 1 := by
      intro j
      rw [Function.update_self]
      rcases lt_trichotomy j l with hj | hj | hj
      · rw [Function.update_of_ne hj.ne]
        have := hreg j hj
        push_cast at this
        omega
      · subst hj
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne hj.ne']
        have := hL hj
        omega
    obtain ⟨V₃, j1, j2, j3, π₃, a, hπ₃, ha, haa⟩ :=
      _root_.GlobalTheory.WigSh.wigner_step_raise V₂ n r z π₂ _ β _ B l hz hT hπ₂ hL' hu' hB hreg'
    refine ⟨V₃, j1, j2, j3, π₃, fun ω => (A ω).comp (a ω), ?_,
      wigMap_comp V V₂ V₃ (n + 1) r z π π₂ π₃ m 1 A a hA ha, ?_⟩
    · rw [Function.update_self, Function.update_idem] at hπ₃
      have e : u ((l : ℕ) + 1) + ((m + 1 : ℕ) : ℝ) = u ((l : ℕ) + 1) + (m : ℝ) + 1 := by
        push_cast
        ring
      rw [e]
      exact hπ₃
    · intro M v hv
      have hc := GlobalTheory.adjoint_mem_CapSp_subA V V₂ n r z π π₂ B (A (B (Fin.last n))) (shf β M)
        ⟨hπ.2.1, hπ.2.2.1⟩ ⟨hπ₂.2.1, hπ₂.2.2.1⟩ hπ.2.2.2.1 hπ₂.2.2.2.1 hB
        (fun h hh he => by
          have := hA.2.1 h hh (B (Fin.last n))
          rwa [he] at this) v hv
      have h2 := haa M _ hc
      show A (B (Fin.last n)) (a (B (Fin.last n))
        (ContinuousLinearMap.adjoint ((A (B (Fin.last n))).comp (a (B (Fin.last n)))) v)) = _
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, h2, map_smul, hAA M v hv,
        smul_smul, Finset.prod_range_succ]
      push_cast
      rw [mul_comm]

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowth
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomMass

theorem integrand_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {d : ℝ} (hd : 0 ≤ d) (v : Wp) :
    ENNReal.ofReal (1 * (d * ‖v‖ ^ 2)) = ((‖((Real.sqrt d : ℝ) : ℂ) • v‖₊ : ENNReal)) ^ 2 := by
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hd, one_mul]

theorem mom_mass : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  obtain ⟨⟨-, -, -, -, hOK⟩, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  obtain ⟨-, -, hgap, -⟩ := hfam ν hν
  have hDS := hFam ν hν
  obtain ⟨hBe, hpos, hdeg⟩ := hSF ν hν
  have key : NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧
      ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq =
        ENNReal.ofReal (‖w‖ ^ 2) := by
    intro hnz
    have hiso := GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq (l ν) (dg ν) hDS hgap hOK hSide hBe
      hdeg hnz
    refine ⟨hiso, fun w hw => ?_⟩
    rw [← hiso.2 w hw]
    unfold PI.BesselPeriodGGP.l2SG
    exact lintegral_congr fun x => integrand_eq hpos.le _
  refine ⟨fun w hw => ?_, key⟩
  by_cases hnz : NzOn (R ν) (l ν)
  · exact ((key hnz).2 w hw).le
  · have hz : ∀ v ∈ (R ν).sm, l ν v = 0 := by
      intro v hv
      by_contra hne
      exact hnz ⟨v, hv, hne⟩
    obtain ⟨-, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r _ _ (R ν) hDS
    obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hSide
    obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
    have : ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      rw [← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hz _ (hsm _ hx w hw)]
      simp
    rw [this]
    exact bot_le

end GlobalTheory.MomMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsometricBesselCompareStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometric_bessel_compare : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp) (Bm' : R'.H → Wp), R.IsDS ε mu → R'.IsDS ε mu' → mu ≠ mu' → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → IsIsoB R' z π νq Bm' → ∀ w ∈ R.sm, ∀ y ∈ R'.sm, ∫ x, ⟪Bm' (R'.σ (Matrix.of x) y), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = 0 := by
  first | exact @GlobalTheory.bessel_orth_of_param_ne | exact GlobalTheory.bessel_orth_of_param_ne | (intros; apply GlobalTheory.bessel_orth_of_param_ne <;> assumption)
end

