module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceTensorRatFiniteAlgebraModuleTopology
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismsSameMatrixIsomorphicTestData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMat

private theorem topS_tensor_left_ext {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) {Z : Scheme.{0}}
    (f g : Z ⟶ (topS Rg ⊗ A).left) (h : f ≫ (snd (topS Rg) A).left = g ≫ (snd (topS Rg) A).left) : f = g := by
  have P := IsPullback.of_hasPullback (topS Rg).hom A.hom
  have h' : f ≫ pullback.snd (topS Rg).hom A.hom = g ≫ pullback.snd (topS Rg).hom A.hom := h
  apply P.hom_ext
  · have hm : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    rw [← cancel_mono (topS Rg).hom, Category.assoc, Category.assoc, P.w, ← Category.assoc, h', Category.assoc]
  · exact h'

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem mat_determines : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A₁ B₁ : Over (Sp R)) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) (A₂ B₂ : Over (Sp R)) [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → IsTest A B L M t A₂ B₂ φA₂ φB₂ Φ₂ → IsMat L M k bA bB eA eB t A₁ B₁ φA₁ φB₁ Φ₁ c → IsMat L M k bA bB eA eB t A₂ B₂ φA₂ φB₂ Φ₂ c → IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ (𝟙 (Sp R)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A₁ B₁ _ _ φA₁ φB₁ Φ₁ A₂ B₂ _ _ φA₂ φB₂ Φ₂ c T₁ T₂ M₁ M₂
  obtain ⟨-, hBab, hL, hM, -, -, -, -, hva, -, hbc⟩ := hH
  let ψA : A₂.left ⟶ A₁.left := T₁.1.1.lift φA₂ A₂.hom T₂.1.1.w
  let ψB : B₂.left ⟶ B₁.left := T₁.2.1.1.lift φB₂ B₂.hom T₂.2.1.1.w
  have hψA1 : ψA ≫ φA₁ = φA₂ := T₁.1.1.lift_fst _ _ _
  have hψA2 : ψA ≫ A₁.hom = A₂.hom := T₁.1.1.lift_snd _ _ _
  have hψB1 : ψB ≫ φB₁ = φB₂ := T₁.2.1.1.lift_fst _ _ _
  have hψB2 : ψB ≫ B₁.hom = B₂.hom := T₁.2.1.1.lift_snd _ _ _
  have gA : IsGrpPullback A₂ A₁ (𝟙 _) ψA :=
    IsGrpPullback.cancel T₁.1 (by rw [Category.id_comp, hψA1]; exact T₂.1) (by rw [hψA2, Category.comp_id])
  have gB : IsGrpPullback B₂ B₁ (𝟙 _) ψB :=
    IsGrpPullback.cancel T₁.2.1 (by rw [Category.id_comp, hψB1]; exact T₂.2.1) (by rw [hψB2, Category.comp_id])
  refine ⟨ψA, ψB, gA, gB, hψA1, hψB1, ?_⟩
  suffices key : Φ₂.left ≫ φB₂ = ψA ≫ Φ₁.left ≫ φB₁ by
    apply T₁.2.1.1.hom_ext
    · rw [Category.assoc, hψB1, key, Category.assoc]
    · rw [Category.assoc, hψB2, Over.w Φ₂, Category.assoc, Over.w Φ₁, hψA2]

  obtain ⟨ψA₁, ψB₁, eA₁, eB₁, g₁⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₁
  obtain ⟨ψA₂, ψB₂, eA₂, eB₂, g₂⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₂
  obtain ⟨x, b', hx, hb', hemb⟩ := GlobalTheory.T.embeds_after_baseChange_specTopOpen_of_stable_basis B M k bB hBab hM hva hbc
  have hG : ψA ≫ ψA₁ = ψA₂ := topS_tensor_left_ext A _ _ (by rw [Category.assoc, eA₁, eA₂, hψA1])
  let H : (baseAt x ⊗ B).left ⟶ (topS Rg ⊗ B).left := (homAt x ▷ B).left
  have hHi : IsIso (homAt x) := by
    have : IsIso ((Over.forget _).map (homAt x)) := hx
    exact isIso_of_reflects_iso (homAt x) (Over.forget _)
  have hH : IsIso H := (inferInstance : IsIso ((Over.forget _).map (homAt x ▷ B)))
  have hHs : H ≫ (snd (topS Rg) B).left = (snd (baseAt x) B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  let F₁ : A₂.left ⟶ (topS Rg ⊗ B).left := ψA ≫ Φ₁.left ≫ ψB₁
  let F₂ : A₂.left ⟶ (topS Rg ⊗ B).left := Φ₂.left ≫ ψB₂
  suffices hF : F₂ ≫ inv H = F₁ ≫ inv H by
    have e1 : F₂ = F₁ := by simpa using congrArg (· ≫ H) hF
    have e2 : F₂ ≫ (snd (topS Rg) B).left = F₁ ≫ (snd (topS Rg) B).left := by rw [e1]
    simp only [F₁, F₂, Category.assoc] at e2
    rwa [eB₁, eB₂] at e2

  have memw : ∀ {P Q : Scheme.{0}} (W : LB Q) (φ : P ⟶ Q) (j : Fin 1 → W.ι) (y : P), φ y ∈ W.U (j 0) →
      y ∈ LB.wchart W (fun _ : Fin 1 => φ) j := fun W φ j y h =>
    Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h
  have hsx : (snd (topS Rg) B).left = inv H ≫ (snd (baseAt x) B).left := by
    rw [← hHs, IsIso.inv_hom_id_assoc]
  have hbase : ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseAt x ⊗ B).left) (z : Z) (pM : Fin 1 → M.ι) (j : Fin mB),
      r z ∈ (LPow B M (k : ℤ) (baseAt x)).U pM →
      gs r z _ ((b' j).f pM) = gs (r ≫ H) z _ ((bB j).f pM) := by
    intro Z r z pM j hz
    rw [hb' j pM, gs_res _ _ _ hz, gs_pull]
    exact chart_le_res B M (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (k : ℤ) pM hz
  have hmono : Mono (baseAt x).hom := by
    have : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    change Mono (x ≫ (topS Rg).hom); infer_instance
  have hπ : ∀ F : A₂.left ⟶ (topS Rg ⊗ B).left, F ≫ inv H ≫ (fst (baseAt x) B).left ≫ (baseAt x).hom =
      F ≫ (snd (topS Rg) B).left ≫ B.hom := by
    intro F
    have w : (fst (baseAt x) B).left ≫ (baseAt x).hom = (snd (baseAt x) B).left ≫ B.hom :=
      pullback.condition
    rw [w, hsx]; simp only [Category.assoc]
  refine GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively (fst (baseAt x) B).left b' hemb _ _ ?_ ?_
  · rw [← cancel_mono (baseAt x).hom]
    simp only [Category.assoc]
    rw [hπ, hπ]
    simp only [F₁, F₂, Category.assoc]
    rw [reassoc_of% eB₁, reassoc_of% eB₂, T₁.2.1.1.w, T₂.2.1.1.w, reassoc_of% (Over.w Φ₂), reassoc_of% (Over.w Φ₁),
      reassoc_of% hψA2]
  · intro z
    obtain ⟨q0, hq0⟩ := exists_chart hL (φA₂ z)
    obtain ⟨p₁, hp₁⟩ := exists_chart hM ((ψA ≫ Φ₁.left ≫ φB₁) z)
    obtain ⟨p₂, hp₂⟩ := exists_chart hM ((Φ₂.left ≫ φB₂) z)
    have mA₂ : (𝟙 A₂.left ≫ ψA₂) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      refine memw L _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, eA₂]; exact hq0
    have mA₁ : (ψA ≫ ψA₁) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      rw [hG]; simpa using mA₂
    have mB₂ : (𝟙 A₂.left ≫ Φ₂.left ≫ ψB₂) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₂) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, Category.assoc, eB₂]; exact hp₂
    have mB₁ : (ψA ≫ Φ₁.left ≫ ψB₁) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₁) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, eB₁]; exact hp₁
    obtain ⟨u₂, hu₂⟩ := g₂ A₂.left (𝟙 _) z _ _ mB₂ mA₂
    obtain ⟨u₁, hu₁⟩ := g₁ A₂.left ψA z _ _ mB₁ mA₁
    simp only [Category.id_comp] at hu₂
    rw [hψA2, hG] at hu₁
    refine ⟨fun j => ∑ i, gs A₂.hom z ⊤ (c i j) * gs ψA₂ z _ ((bA i).f (fun _ => q0)), ⟨fun _ => p₂, ?_, u₂, fun l => ?_⟩,
      ⟨fun _ => p₁, ?_, u₁, fun l => ?_⟩⟩
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₂ l
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₁ l

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAway

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

def intAfP (p : ℕ) : Set (AfP p) :=
  {a | ∀ v : AwayP p, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}

theorem isOpen_intAfP (p : ℕ) : IsOpen (intAfP p) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem natCast_mem (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
  _root_.natCast_mem _ n

theorem exists_nat_local (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b.natAbs, Int.natAbs_pos.2 hb0, ?_⟩
  have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) (|b|) := by
    rw [← Int.natCast_natAbs, map_natCast]
  rw [e]
  rcases abs_choice b with h | h
  · rw [h, mul_comm]; exact hbx
  · rw [h, map_neg, neg_mul, mul_comm]; exact neg_mem hbx

theorem eval_natCast_mul {p : ℕ} (v : AwayP p) (n : ℕ) (a : AfP p) :
    AfP.eval v ((n : AfP p) * a) = (n : v.1.adicCompletion ℚ) * AfP.eval v a := by
  rw [map_mul, map_natCast]

theorem exists_nat_adele {p : ℕ} (a : AfP p) : ∃ n : ℕ, 0 < n ∧ (n : AfP p) * a ∈ intAfP p := by
  choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 (AfP.eval v a)
  have hS : {v : AwayP p | ¬ AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp (a : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]).2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [eval_natCast_mul]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]
    exact mul_mem (natCast_mem w.1 k) (hm w)
  · have hw' : AfP.eval w a ∈ w.1.adicCompletionIntegers ℚ := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem w.1 _) hw'

theorem exists_pow_of_integral_away (p : ℕ) [Fact p.Prime] (r : ℚ)
    (h : ∀ v : AwayP p, (v.1.valuation ℚ r) ≤ 1) : ∃ (k : ℤ) (e : ℕ), r * (p : ℚ) ^ e = k := by
  have hden : r.den = p ^ r.den.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd r.den_nz fun {ℓ} hℓ hdvd => ?_
    by_contra hne
    have hℓ' : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ
    let v : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)}, (Ideal.span_singleton_prime hℓ'.ne_zero).2 hℓ',
      by simpa using hℓ.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro h'
      have h'' : Associated (ℓ : ℤ) (p : ℤ) := Ideal.span_singleton_eq_span_singleton.1 h'
      exact hne (by simpa using Int.natAbs_eq_iff_associated.2 h'')
    have h1 := Rat.valuation_le_one_iff_den.1 (h ⟨v, hv⟩)
    exact h1 (Ideal.mem_span_singleton.2 (by exact_mod_cast hdvd))
  refine ⟨r.num, r.den.primeFactorsList.length, ?_⟩
  have : ((p : ℚ) ^ r.den.primeFactorsList.length) = (r.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.mul_den_eq_num]

theorem den_bounded_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Ω : Set (AfP p)), IsCompact Ω → ∃ M : ℕ, 0 < M ∧
    ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Ω → ∃ (k : ℤ) (e : ℕ), q * ((M : ℚ) * (p : ℚ) ^ e) = k := by
  intro p _ Ω hΩ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun q hq => ?_⟩
  obtain ⟨a, ha, hqa⟩ := Set.mem_iUnion₂.mp (ht hq)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hqa' : (m a : AfP p) * algebraMap ℚ (AfP p) q ∈ intAfP p := hqa
  have hint : ∀ v : AwayP p, v.1.valuation ℚ (((∏ a ∈ t, m a : ℕ) : ℚ) * q) ≤ 1 := by
    intro v
    have h2 : AfP.eval v (algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q)) ∈
        v.1.adicCompletionIntegers ℚ := by
      have e : algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q) =
          (k : AfP p) * ((m a : AfP p) * algebraMap ℚ (AfP p) q) := by
        rw [map_mul, map_natCast, hk, Nat.cast_mul]; ring
      rw [e, eval_natCast_mul]
      exact mul_mem (natCast_mem v.1 k) (hqa' v)
    rw [AlgHom.commutes] at h2
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    exact h2
  obtain ⟨z, e, hz⟩ := exists_pow_of_integral_away p _ hint
  exact ⟨z, e, by rw [← hz]; ring⟩

end GlobalTheory.DenAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralArchimedeanMatricesLeftMulJacobianStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ), ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  first | (exact @GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (exact GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (intros; apply GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseThetaTransformHasLevelCompactFiniteSuppor
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

noncomputable def finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : (Fin N → Af F) →+ VA F N where
  toFun v := (0, fun i => pairA F 0 (v i))
  map_zero' := rfl
  map_add' v w := by
    refine Prod.ext (add_zero _).symm ?_
    funext i
    exact Prod.ext (add_zero _).symm rfl

theorem continuous_finEmbSnd (F : Type) [Field F] [NumberField F] (N : ℕ) : Continuous (finEmbSnd F N) :=
  continuous_const.prodMk (continuous_pi fun i => continuous_const.prodMk (continuous_apply i))

theorem dotProduct_finEmbSnd {F : Type} [Field F] [NumberField F] {N : ℕ} (x : Fin N → AF F) (v : Fin N → Af F) :
    x ⬝ᵥ (finEmbSnd F N v).2 = pairA F 0 (Bd (Af F) (half F N) (fin x) v) := by
  have h : Bd (Af F) (half F N) (fin x) v = ∑ i, fin x i * v i := by
    simp [Bd, half]
  rw [h]
  refine Prod.ext ?_ ?_
  · change fstA F (∑ i, x i * pairA F 0 (v i)) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_mul]; exact mul_zero _
  · change sndA F (∑ i, x i * pairA F 0 (v i)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl

theorem invV_level_support : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)), Ctx ψ lam ν (half F N) → ∀ 𝓓 : Set (Fin N → AF F), IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν) → muV N ν 𝓓 = 1 → ∀ f : VA F N → ℂ, QuasiV ψ f → LevelV ψ f → (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, invV ψ ν 𝓓 f (x + u) = invV ψ ν 𝓓 f x) ∧ ∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, invV ψ ν 𝓓 f x ≠ 0 → fin x ∈ K := by
  intro F _ _ N _ ψ lam ν hc 𝓓 hD _ f hq hl
  obtain ⟨U, hU, hf⟩ := hl
  have h0 : inf (0 : Fin N → AF F) = 0 := rfl
  refine ⟨⟨U.comap (AddMonoidHom.inl (Fin N → AF F) (Fin N → AF F)),
    hU.preimage (f := fun u : Fin N → AF F => ((u, 0) : VA F N)) (continuous_id.prodMk continuous_const), ?_⟩, ?_⟩
  · intro u hu hi x
    rw [← invV_heisV_fst, hf (u, 0) hu hi h0]
  · refine ⟨_, (_root_.GlobalTheory.SWQ.finite_annihilators F N ψ lam ν (half F N) hc).1 (U.comap (finEmbSnd F N))
      (hU.preimage (continuous_finEmbSnd F N)), fun x hx v hv => ?_⟩
    have h1 := invV_heisV_snd hc.2.2.2.1 hD hq (finEmbSnd F N v).2 x
    rw [show ((0 : Fin N → AF F), (finEmbSnd F N v).2) = finEmbSnd F N v from rfl, hf _ hv h0 rfl,
      dotProduct_finEmbSnd] at h1
    exact mul_right_cancel₀ hx (h1.symm.trans (one_mul _).symm)

end GlobalTheory.ThetaTransform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigPull
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigPull

theorem pull_top_injective {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Sp k) (g : Y ⟶ X) (hg : Dense (Set.range g)) (B : LB X) (hB : B.IsLB) :
    Function.Injective (H0.pull (p := p) (B := B) (O := ⊤) g (W := ⊤) le_top) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  obtain ⟨σ, rfl⟩ := (H0.bijective_ofSec_top (p := p) (B := B)).2 f
  by_contra hne
  have hσ : σ ≠ 0 := fun h => hne (by rw [h, map_zero])
  have hgen := (sec_ne_zero_iff σ).1 hσ
  obtain ⟨y, hy⟩ : ∃ y, g y ∈ nonzeroLocus σ := by
    obtain ⟨_, hy, ⟨y, rfl⟩⟩ := hg.inter_open_nonempty _ (nonzeroLocus σ).isOpen ⟨_, hgen⟩
    exact ⟨y, hy⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hB.cover.ge (trivial : g y ∈ (⊤ : X.Opens)))
  have hj : y ∈ (B.pull g).U (fun _ => i) := mem_pull.2 hi
  have e := H0.germ_pull (p := p) (B := B) (O := ⊤) g (W := ⊤) le_top (fun _ => i) y trivial hj
    (H0.ofSec p ⊤ σ)
  rw [hf, map_zero] at e
  have hu : IsUnit ((g.stalkMap y).hom (H0.germ (p := p) (O := ⊤) i (g y) (show g y ∈ (⊤ : X.Opens) from trivial) hi (H0.ofSec p ⊤ σ))) :=
    IsUnit.map _ ((H0.germ_ofSec (p := p) (O := ⊤) _ _ (show g y ∈ (⊤ : X.Opens) from trivial) hi σ).symm ▸ (isUnit_ger_iff σ hi).2 hy)
  rw [← e] at hu
  exact not_isUnit_zero hu

theorem finite_H0_top {E : Type} [Field E] {Y : Scheme.{0}} (p : Y ⟶ Sp E) (B : LB Y) :
    letI := algebraΓOfHom p
    Module.Finite E (coh (twist (structureModule Y) B) 0) → Module.Finite E (H0 p B ⊤) := by
  letI := algebraΓOfHom p
  intro h
  letI : Module E B.Sec := Module.compHom _ (algebraMap E Γ(Y, ⊤))
  haveI : IsScalarTower E Γ(Y, ⊤) B.Sec := IsScalarTower.of_compHom _ _ _
  have e (c : E) : algebraMap E Γ(Y, ⊤) c = algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  exact Module.Finite.equiv (((cohZeroTwistEquiv B).restrictScalars E).trans
    (LinearEquiv.ofBijective { H0.ofSec p ⊤ with
      map_smul' := fun c σ => (e c ▸ H0.ofSec_smul c σ :) } H0.bijective_ofSec_top))

theorem isBig_pull : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (g : Y ⟶ X), IsProjOver (g ≫ p) → topologicalKrullDim Y = topologicalKrullDim X →
    Dense (Set.range g) → ∀ N : LB X, (letI := algebraΓOfHom p; IsBig k N) →
    (letI := algebraΓOfHom (g ≫ p); IsBig k (N.pull g)) := by
  intro k _ X Y _ p g hp hd hg N hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (g ≫ p)
  have hL : ∀ m, (lbPow (N.pull g) m).IsLB := fun m => isLB_lbPow (LB.isLB_pull hN.isLB g) m
  have hfin : ∀ m, Module.Finite k (coh (twist (structureModule Y) (lbPow (N.pull g) m)) 0) :=
    fun m => finite_coh_zero_twist_of_isProjOver (fun _ => rfl) hp (hL m)
  have hle : ∀ m, lbH0 k (lbPow N m) ≤ lbH0 k (lbPow (N.pull g) m) := by
    intro m
    have hB := isLB_lbPow hN.isLB m
    have hB' := LB.isLB_pull hB g
    have ec := (cls_eq_iff (hL m) hB').2 (lbIso_lbPow_pull hN.isLB g m)
    rw [lineBundleGlobalSectionsDim_congr_picardClass (hL m) hB' ec, ← H0.finrank_top p, ← H0.finrank_top (g ≫ p)]
    haveI := finite_H0_top (g ≫ p) ((lbPow N m).pull g)
      (finite_coh_zero_twist_congr hB' (hL m) ec.symm (hfin m))
    exact LinearMap.finrank_le_finrank_of_injective (pull_top_injective p g hg _ hB)
  obtain ⟨D, hD, c, hc, hm⟩ := hN.growth
  exact ⟨LB.isLB_pull hN.isLB g, hfin, D, hd.trans hD, c, hc,
    hm.mono fun m h => h.trans (by exact_mod_cast hle m)⟩

end GlobalTheory.BigPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactIntegralUnitaryPointsAtPlace
section
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem isCompact_isIntV (G : HTGroup p) (v : AwayP p) :
    @IsCompact _ (moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)) {y | IsIntV G v y} := by
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  set b := basV G v
  have hc : Continuous b.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
  have hbox : IsCompact (Set.univ.pi fun _ : Fin (Module.finrank ℚ G.C) ↦
      (v.1.adicCompletionIntegers ℚ : Set (Qv v))) :=
    isCompact_univ_pi fun _ ↦ LevelExists.isCompact_intCompl v.1
  have hset : {y | IsIntV G v y} = b.equivFun.symm '' (Set.univ.pi fun _ ↦
      (v.1.adicCompletionIntegers ℚ : Set (Qv v))) := by
    rw [LinearEquiv.image_symm_eq_preimage]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi, Module.Basis.equivFun_apply]
    rfl
  rw [hset]
  exact hbox.image hc

theorem isCompact_IntV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), IsCompact (IntV G v) := by
  intro p _ G v
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C
  have hPc := isCompact_isIntV G v
  have hOc := LevelExists.isCompact_intCompl v.1
  set P : Set (Qv v ⊗[ℚ] G.C) := {y | IsIntV G v y}
  set O : Set (Qv v) := (v.1.adicCompletionIntegers ℚ : Set (Qv v))
  have hσ : Continuous (fun y : Qv v ⊗[ℚ] G.C ↦ (starT G.star (Qv v) y).unop) := by
    let σl : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (Qv v) y).unop
        map_add' := fun x y ↦ by simp only [map_add (f := _), MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add (f := _), MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (Qv v) (Qv v ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (Qv v) : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let g : Gv G v → ((Qv v ⊗[ℚ] G.C) × (Qv v ⊗[ℚ] G.C)ᵐᵒᵖ) × (Qv v × (Qv v)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hg : Topology.IsClosedEmbedding g :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal
  let K := (P ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' P)) ×ˢ (O ×ˢ (MulOpposite.opHomeomorph.symm ⁻¹' O))
  have hKC : IntV G v = g ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2, h3, h4⟩
  rw [hKC]
  exact hg.isCompact_preimage ((hPc.prod
    (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hPc)).prod
    (hOc.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hOc)))

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSmulOfCharpolyCoeffMulIntStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_natCast_smul_of_mul_charpoly_coeff_int : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ), (∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) → IsIntegral ℤ ((M : ℤ) • x) := by
  first | (exact @GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (exact GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int) | (intros; apply GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int  <;> assumption)
end

