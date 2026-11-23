module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0007
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0005
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0006
public import Development.AutomorphicArithmetic.AdelicQuotients.TwNormConjDiagonalEqConjNormGL
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle0005
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0004
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0003
public import Development.AutomorphicArithmetic.AdelicQuotients.HaarConstOfHaarExists
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0011
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0010
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.FirstGeometricConditionOfProperties
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private noncomputable abbrev th (σ : E ≃ₐ[F] E) (n : ℕ) : Monoid.End (AdelicGLn.AdelicGL E n) := mapGL n (galAd σ)

private theorem ht_pow (σ : E ≃ₐ[F] E) (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (y : AdelicGLn.AdelicGL E n) (m : ℕ) :
    heightOff q ((th σ n ^ m) y) = heightOff q y := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ_apply']; exact (UpperTheory.heightOff_mapGL_galAd F E σ n q _).trans ih

private theorem ht_norm (σ : E ≃ₐ[F] E) (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (y : AdelicGLn.AdelicGL E n) {Y : ℝ}
    (hy : heightOff q y ≤ Y) (m : ℕ) :
    heightOff q (twNorm (th σ n) m y) ≤ (AutomorphicForm.heightConst E n * Y) ^ m := by
  obtain ⟨h1, h2, h3⟩ := UpperTheory.one_le_heightOff_and_submultiplicative F E n q
  have hK := AutomorphicForm.one_le_heightConst (K := E) (n := n)
  induction m with
  | zero => rw [twNorm_zero, h2, pow_zero]
  | succ m ih =>
    rw [twNorm_succ]
    refine (h3 _ _).trans ?_
    rw [ht_pow, pow_succ]
    have a1 := h1 y
    have a2 := h1 (twNorm (th σ n) m y)
    calc _ = heightOff q (twNorm (th σ n) m y) * (AutomorphicForm.heightConst E n * heightOff q y) := by ring
      _ ≤ _ := mul_le_mul ih (mul_le_mul_of_nonneg_left hy (by linarith)) (by positivity) (by linarith)

private theorem iw_pow (σ : E ≃ₐ[F] E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (y : AdelicGLn.AdelicGL E n)
    (hy : finAt w y ∈ GLnLocal.iwahori (w.adicCompletion E) n) (m : ℕ) :
    ∀ w' : HeightOneSpectrum (𝓞 E), w' = (σ ^ m) • w →
      finAt w' ((th σ n ^ m) y) ∈ GLnLocal.iwahori (w'.adicCompletion E) n := by
  induction m with
  | zero => intro w' h; rw [pow_zero, one_smul] at h; subst h; exact hy
  | succ m ih =>
    intro w' h
    rw [pow_succ', mul_smul] at h
    subst h
    rw [pow_succ_apply']
    exact UpperTheory.finAt_mapGL_galAd_mem_iwahori F E σ n _ _ (ih _ rfl)

private theorem norm_at [IsGalois F E] (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (n : ℕ)
    (q : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E q) (hs : Function.Surjective (completionMap q w₀.1))
    (y : AdelicGLn.AdelicGL E n)
    (hy : ∀ w : PlacesOver E q, w ≠ w₀ → finAt w.1 y ∈ GLnLocal.iwahori (w.1.adicCompletion E) n) (m : ℕ)
    (hm : m + 1 ≤ Module.finrank F E) :
    ∃ i ∈ GLnLocal.iwahori (w₀.1.adicCompletion E) n, finAt w₀.1 (twNorm (th σ n) (m + 1) y) = finAt w₀.1 y * i := by
  have hord : orderOf σ = Module.finrank F E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  induction m with
  | zero => exact ⟨1, one_mem _, by rw [twNorm_succ, twNorm_zero, one_mul, mul_one]; rfl⟩
  | succ m ih =>
    obtain ⟨i, hi, e⟩ := ih (by omega)
    have hne : (σ ^ (m + 1))⁻¹ • w₀ ≠ w₀ := fun h => by
      have h1 := UpperTheory.eq_one_of_smul_place_eq_of_completionMap_surjective F E q w₀ hs _ h
      rw [inv_eq_one] at h1
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega) h1
    have h2 := iw_pow σ n _ y (hy _ hne) (m + 1) w₀.1 (by rw [coe_smul_placesOver, smul_inv_smul])
    exact ⟨i * _, mul_mem hi h2, by rw [twNorm_succ, finAt_mul, e, mul_assoc]⟩

private theorem small_false (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E q) (γ : GL (Fin n) E)
    (x : AdelicGLn.AdelicGL E n) (p : F[X]) (hp : p.Monic)
    (hd : p.map (algebraMap F E) ∣ (γ : Matrix (Fin n) (Fin n) E).charpoly) (j : ℕ)
    (hs : ‖((p.map (algebraMap F E)).map (algebraMap E (w₀.1.adicCompletion E))).coeff 0‖ * 2 ^ j ≤ 1) :
    (2 : ℝ) ^ j ≤ (AutomorphicForm.heightConst E n * heightOff q (x⁻¹ * AdelicGLn.diagonal E n γ * x)) ^ n := by
  obtain ⟨c1, c2⟩ := UpperTheory.charpoly_local_adelic_conj_diagonal_eq E n γ x
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have h21 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  rw [coeff_map, coeff_map] at hs
  have hne : algebraMap F E (p.coeff 0) ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := hd
    have h1 := congrArg (fun s : E[X] => s.coeff 0) hr
    simp only [mul_coeff_zero, coeff_map, h0, zero_mul] at h1
    have h3 := Matrix.det_eq_sign_charpoly_coeff (γ : Matrix (Fin n) (Fin n) E)
    rw [h1, mul_zero] at h3
    exact (Matrix.isUnits_det_units γ).ne_zero h3
  have hs' : ‖algebraMap E (w₀.1.adicCompletion E) (algebraMap F E (p.coeff 0))‖ ≤ (2 ^ j : ℝ)⁻¹ := by
    rw [← one_div, le_div_iff₀ h2]; exact hs
  have key := UpperTheory.one_le_mul_heightConst_heightOff_pow_of_small_at_place F E n q w₀ (x⁻¹ * AdelicGLn.diagonal E n γ * x) _ _ hne
    (fun w => by
      have := UpperTheory.norm_coeff_zero_dvd_charpoly_le_infinitePlace E w n _ _ (AutomorphicForm.one_le_locHeight _)
        (AutomorphicForm.norm_apply_le_locHeight (infAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x)))
        ((p.map (algebraMap F E)).map (algebraMap E w.Completion)) ((hp.map _).map _)
        (by rw [c2]; exact Polynomial.map_dvd _ hd)
      rwa [coeff_map, coeff_map] at this)
    (fun w => by
      have := UpperTheory.norm_coeff_zero_dvd_charpoly_le_adicCompletion E w n _ _ (AutomorphicForm.one_le_locHeight _)
        (AutomorphicForm.norm_apply_le_locHeight (finAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x)))
        ((p.map (algebraMap F E)).map (algebraMap E (w.adicCompletion E))) ((hp.map _).map _)
        (by rw [c1]; exact Polynomial.map_dvd _ hd)
      rwa [coeff_map, coeff_map] at this)
    (fun w => UpperTheory.norm_algebraMap_base_le_one_of_placesOver F E q w₀ w _ (hs'.trans (inv_le_one_of_one_le₀ h21))) hs'
  rwa [← div_eq_inv_mul, one_le_div h2] at key

private theorem core [IsGalois F E] (hA : A1) (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) (n : ℕ) (hn : 0 < n)
    (q : HeightOneSpectrum (𝓞 F)) (w₀ : PlacesOver E q) (hs : ∀ w : PlacesOver E q, Function.Surjective (completionMap q w.1))
    (ν : Fin n → ℤ) (hν : Function.Injective ν) (hsum : ∑ i, ν i = 0)
    (hJ : ∀ J : Finset (Fin n), J.Nonempty → J ≠ Finset.univ → ∑ i ∈ J, ν i ≠ 0)
    (j : ℕ) (hj0 : 0 < j) (Y : ℝ) (hY : 1 ≤ Y)
    (hj : (AutomorphicForm.heightConst E n * AutomorphicForm.heightConst E n ^ Module.finrank F E) ^ n *
      Y ^ (Module.finrank F E * n) < 2 ^ j)
    (δ : GL (Fin n) E) (x y : AdelicGLn.AdelicGL E n)
    (hy : y = x⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) x)
    (hht : heightOff q y ≤ Y)
    (a b : GL (Fin n) (w₀.1.adicCompletion E)) (ha : a ∈ GLnLocal.iwahori (w₀.1.adicCompletion E) n)
    (hb : b ∈ GLnLocal.iwahori (w₀.1.adicCompletion E) n)
    (hab : finAt w₀.1 y = a * Cartan.diagPow (w₀.1.adicCompletion E) n (fun i => (j : ℤ) * ν i) * b)
    (hoth : ∀ w : PlacesOver E q, w ≠ w₀ → finAt w.1 y ∈ GLnLocal.iwahori (w.1.adicCompletion E) n) :
    EllElt σ δ := by
  have hK := AutomorphicForm.one_le_heightConst (K := E) (n := n)
  obtain ⟨P, hP⟩ := charpoly_normGL_lifts σ hσ δ
  have hPm : P.Monic := by
    refine Polynomial.monic_of_injective (algebraMap F E).injective ?_
    rw [hP]; exact Matrix.charpoly_monic _
  have hPd : P.natDegree = n := by
    rw [← natDegree_map_eq_of_injective (algebraMap F E).injective P, hP, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  refine ⟨P, ?_, hP⟩
  have hN : twNorm (th σ n) (Module.finrank F E) y = x⁻¹ * AdelicGLn.diagonal E n (normGL σ δ) * x := by
    rw [hy]; exact UpperTheory.twNorm_conj_diagonal_eq_conj_normGL F E σ n δ x
  have hH := ht_norm σ n q y hht (Module.finrank F E)
  rw [hN] at hH
  have hbad : ∀ p : F[X], p.Monic → p ∣ P →
      ¬ ‖((p.map (algebraMap F E)).map (algebraMap E (w₀.1.adicCompletion E))).coeff 0‖ * 2 ^ j ≤ 1 := by
    intro p hp hd h
    have h1 := small_false n q w₀ (normGL σ δ) x p hp (by rw [← hP]; exact Polynomial.map_dvd _ hd) j h
    have h0 := (UpperTheory.one_le_heightOff_and_submultiplicative F E n q).1 (x⁻¹ * AdelicGLn.diagonal E n (normGL σ δ) * x)
    have h2 := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hH (by linarith : 0 ≤ AutomorphicForm.heightConst E n)) n
    have h3 : (AutomorphicForm.heightConst E n * (AutomorphicForm.heightConst E n * Y) ^ Module.finrank F E) ^ n =
        (AutomorphicForm.heightConst E n * AutomorphicForm.heightConst E n ^ Module.finrank F E) ^ n * Y ^ (Module.finrank F E * n) := by
      rw [pow_mul, ← mul_pow, mul_pow _ Y, mul_assoc]
    linarith
  have hl0 : 0 < Module.finrank F E := Module.finrank_pos
  obtain ⟨i, hi, hNi⟩ := norm_at σ hσ n q w₀ (hs w₀) y hoth (Module.finrank F E - 1) (by omega)
  rw [show Module.finrank F E - 1 + 1 = Module.finrank F E by omega, hN, hab, mul_assoc _ b i] at hNi
  have hc := (UpperTheory.charpoly_local_adelic_conj_diagonal_eq E n (normGL σ δ) x).1 w₀.1
  rw [hNi, ← hP] at hc
  rw [hPm.irreducible_iff_natDegree]
  refine ⟨fun h => by rw [h, natDegree_one] at hPd; omega, fun p₁ p₂ h₁ h₂ h12 => ?_⟩
  by_contra hcon
  have hd12 : p₁.natDegree + p₂.natDegree = n := by rw [← h12, h₁.natDegree_mul h₂] at hPd; exact hPd
  have hinj : ∀ p : F[X], ((p.map (algebraMap F E)).map (algebraMap E (w₀.1.adicCompletion E))).natDegree =
      p.natDegree := fun p => by
    rw [natDegree_map_eq_of_injective (RingHom.injective _), natDegree_map_eq_of_injective (RingHom.injective _)]
  have hp1 : 0 < p₁.natDegree := by
    exact Nat.pos_of_ne_zero fun h => hcon (Or.inl h)
  have hp2 : 0 < p₂.natDegree := by
    exact Nat.pos_of_ne_zero fun h => hcon (Or.inr h)
  rcases UpperTheory.norm_coeff_zero_factor_charpoly_iwahori_diagPow_le hA E w₀.1 n ν hν hsum hJ j hj0 a ha (b * i) (mul_mem hb hi)
    ((p₁.map (algebraMap F E)).map (algebraMap E _)) ((p₂.map (algebraMap F E)).map (algebraMap E _))
    ((h₁.map _).map _) ((h₂.map _).map _) (by rw [hinj]; exact hp1) (by rw [hinj]; exact hp2)
    (by rw [← Polynomial.map_mul, ← Polynomial.map_mul, h12, ← hc, ← mul_assoc]) with h | h
  · exact hbad p₁ h₁ ⟨p₂, h12.symm⟩ h
  · exact hbad p₂ h₂ ⟨p₁, by rw [mul_comm, h12]⟩ h

end

theorem UpperTheory.ConvolutionTheory.G.firstGeometricCondition_of_properties :
    A1 → N5 → EllipticityFromProductFormula := by
  intro hA _ F E _ _ _ _ _ _ σ hσ n hn
  have hK := AutomorphicForm.one_le_heightConst (K := E) (n := n)
  refine ⟨(AutomorphicForm.heightConst E n * AutomorphicForm.heightConst E n ^ Module.finrank F E) ^ n,
    Module.finrank F E * n, ?_⟩
  intro q w₀ hs ν hν hsum hJ j Y hY hj f hf δ x y hy hfy
  obtain ⟨hht, ⟨a, ha, b, hb, hab⟩, hoth⟩ := hf y hfy
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · exfalso
      have h1 : 1 ≤ (AutomorphicForm.heightConst E n * AutomorphicForm.heightConst E n ^ Module.finrank F E) ^ n *
          Y ^ (Module.finrank F E * n) :=
        one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hK)))
          (one_le_pow₀ hY)
      rw [pow_zero] at hj
      linarith
    · exact h
  exact core hA σ hσ n hn q w₀ hs ν hν hsum hJ j hj0 Y hY hj δ _ _ hy hht a b ha hb hab hoth
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.StableTwistedTraceFormulaComparison
section
open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem match_qI {n : ℕ} {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R]
    [MeasurableSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)] {ι : R →+* S} {s : S →+* S} {l : ℕ}
    {μS : Measure (GL (Fin n) S)} {μR : Measure (GL (Fin n) R)} {c : ℂ} {φ : GL (Fin n) S → ℂ} {f : GL (Fin n) R → ℂ}
    (h : Match ι s l μS μR c φ f) (γ : GL (Fin n) R) (hγ : γ.val.charpoly.Separable) (H : Subgroup (GL (Fin n) R))
    (hH : H = Subgroup.centralizer {γ}) (ν : Measure H) (hν : ν.IsHaarMeasure) :
    (∀ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ →
      qI μS ((mapGL n ι).comp H.subtype) ν (fun x => φ (x⁻¹ * δ * mapGL n s x)) =
        c * qI μR H.subtype ν (fun x => f (x⁻¹ * γ * x))) ∧
    ((¬ ∃ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ) → qI μR H.subtype ν (fun x => f (x⁻¹ * γ * x)) = 0) := by
  subst hH
  exact h γ hγ ν hν

private theorem cent_mul {G : Type} [Group G] (z g : G) (hz : ∀ x, z * x = x * z) :
    Subgroup.centralizer {g} = Subgroup.centralizer {z * g} := by
  ext t
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change (t * g = g * t) ↔ (t * (z * g) = (z * g) * t)
  rw [← mul_assoc, ← hz t, mul_assoc, mul_assoc, mul_right_inj]

private theorem lc_cent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (g : G) :
    LocallyCompactSpace (Subgroup.centralizer {g}) := by
  have : IsClosed (Subgroup.centralizer {g} : Set G) := Set.isClosed_centralizer _
  exact this.locallyCompactSpace

attribute [-instance] GlobalTheory.LGrp.locallyCompact_GL GlobalTheory.SplitFlip.locallyCompact_GL
  GlobalTheory.SplitFlip.secondCountable_GL in
private theorem main (hGl : Glob) (hC : HaarConst) (hX : HaarEx) (hRF : RPF) (hRE : RPE) (hRC : RPCen) (hSF : SideF) (hSE : SideE)
    (hK : K1) (hKF : SelmerRankBoundLaurent) (hH : H1) (hZ : ZNorm) (hN : LocNorm) (hS : SepLoc) (hL : CentLoc) : G4 := by
  classical
  intro F E _ _ _ _ _ _ σ hσ n hn hp _ _ _ _ _ _ _ _ μE μF μiE μiF mE mF hμE hμF hiE hiF hmE hmF
  obtain ⟨μE', μF', uE, uF, hG⟩ := hGl F E σ hσ n hn μE μF hμE hμF
  obtain ⟨aE, haE, hEE⟩ := hC _ _ _ _ _ _ _ (hRE F E n) μE' μiE mE uE.1 hiE hmE
  obtain ⟨aF, haF, hEF⟩ := hC _ _ _ _ _ _ _ (hRF F n) μF' μiF mF uF.1 hiF hmF
  refine ⟨aE / aF, div_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haE)) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haF)), ?_⟩
  intro S φi fi φ f ci c hφi hφi' hfi hfi' hφ hoff hMi hM γ γ₁ hγ₁ hirr ν hν
  have hsep : IsRegSemisimple γ := hirr.separable
  obtain ⟨ν', hν', hGF, hGE⟩ := hG γ γ₁ hγ₁ hsep ν hν
  obtain ⟨hs1, hs2, hs3⟩ := hS F n γ hsep
  haveI : LocallyCompactSpace (TA γ) := lc_cent _
  haveI : LocallyCompactSpace (TI γ) := lc_cent _
  haveI : ∀ v, LocallyCompactSpace (TF γ v) := fun v => lc_cent _
  haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ∀ v, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology _
  have hT := fun S' => hX _ _ _ _ _ _ _ (hRC _ _ _ _ _ _ _ (hRF F n) (AdelicGLn.diagonal F n γ)) ν' Measure.haar
    (fun _ => Measure.haar) hν' inferInstance (fun _ => inferInstance) S'
  have hcF := (hKF F n hn γ hsep)
  rw [eventually_cofinite] at hcF
  have hFside := fun (S' : Finset (Pl F)) (h1 : S ⊆ S') (h2 : hcF.toFinset ⊆ S') (b : NNReal) (hb : b ≠ 0)
      (hE : EulT γ ν' Measure.haar (fun _ => Measure.haar) b S') =>
    hSF F n hn μF' μiF mF uF hiF (fun v => (hmF v).1) γ hsep ν' Measure.haar (fun _ => Measure.haar) hν' inferInstance
      (fun _ => inferInstance) S' aF b haF hb hE (hEF S') fi f hfi hfi' (fun v => (hφ v).2.2.1)
      (fun v hv => ⟨(hoff v fun h => hv (h1 h)).2.1, by
        by_contra h
        exact hv (h2 (hcF.mem_toFinset.2 h))⟩)
  have hMi' := fun s : ℝ => match_qI hMi _ (hs2 s) (TI γ) (cent_mul _ _ (hL F n _).2.1) Measure.haar inferInstance
  have hM' := fun v => match_qI (hM v) _ (hs3 v) (TF γ v) rfl Measure.haar inferInstance
  constructor
  · intro δ hδ
    have hcE := hK F E σ hσ n hn δ γ hsep hδ
    rw [eventually_cofinite] at hcE
    obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset ∪ hcE.toFinset)
    have h1 : S ⊆ S ∪ hcF.toFinset ∪ hcE.toFinset := Finset.subset_union_left.trans Finset.subset_union_left
    obtain ⟨m1, e1⟩ := hFside _ h1 (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE
    obtain ⟨m2, e2⟩ := hSE F E σ hσ n hn μE' μiE mE uE hiE (fun v => (hmE v).1) γ hsep δ hδ ν' Measure.haar (fun _ => Measure.haar)
      hν' inferInstance (fun _ => inferInstance) _ aE b haE hb hE (hEE _) φi φ hφi hφi' (fun v => (hφ v).1)
      (fun v hv => ⟨(hoff v fun h => hv (h1 h)).1, by
        by_contra h
        exact hv (Finset.subset_union_right (hcE.mem_toFinset.2 h))⟩)
    obtain ⟨n1, n2⟩ := hN F E σ hσ n hn δ γ hδ
    rw [hGF _ m1, hGE δ hδ _ m2, e1, e2]
    have i1 := fun s : ℝ => (hMi' s).1 (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) (by
      rw [hZ F E σ hσ n hn, n1, ← map_mul])
    have i2 := fun v => (hM' v).1 _ (n2 v)
    simp only [i1, i2]
    rw [integral_const_mul, Finset.prod_mul_distrib, ← Finset.prod_subset h1 fun v _ hv => (hoff v hv).2.2]
    have : ((aF : ℝ) : ℂ) ≠ 0 := by exact_mod_cast haF
    push_cast
    field_simp
  · intro hno
    by_cases hi : ∃ δ, twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ =
        mapGL n (infMap F E) (pI F n (AdelicGLn.diagonal F n γ))
    · have : ¬ ∀ v : Pl F, ∃ δ, twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ =
          mapGL n (incFin E v) (finAt v (AdelicGLn.diagonal F n γ)) := fun h => hno (hH F E σ hσ n hn hp γ hirr hi h)
      obtain ⟨v, hv⟩ := not_forall.1 this
      obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset ∪ {v})
      obtain ⟨m1, e1⟩ := hFside _ (Finset.subset_union_left.trans Finset.subset_union_left)
        (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE
      rw [hGF _ m1, e1, Finset.prod_eq_zero (i := v) (by simp) ((hM' v).2 hv), mul_zero]
    · obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset)
      obtain ⟨m1, e1⟩ := hFside _ Finset.subset_union_left Finset.subset_union_right b hb hE
      have i1 := fun s : ℝ => (hMi' s).2 (by
        rintro ⟨δ, hδ⟩
        refine hi ⟨(pI E n (zA E n s))⁻¹ * δ, ?_⟩
        have h := hZ F E σ hσ n hn s ((pI E n (zA E n s))⁻¹ * δ)
        rw [mul_inv_cancel_left, hδ, map_mul] at h
        exact (mul_left_cancel h).symm)
      rw [hGF _ m1, e1]
      simp only [i1, integral_zero, mul_zero, zero_mul]

theorem UpperTheory.ConvolutionTheory.G.stable_twisted_trace_formula_comparison :
    Q1 → Q2 → Q3 → N3 → N5 → P1 → P2 → K1 → H1 → G4 := by
  intro _ _ _ n3 n5 _ p2 k1 h1
  have qpush : QPush := UpperTheory.quotient_haar_measure_pushforward
  have splitEq : SplitEquiv := UpperTheory.adelicGL_split_equiv
  have splitQ : SplitQ := UpperTheory.quotient_measure_split
  have uniOf : UniOf := UpperTheory.haar_unimodular_criterion
  have haarEx : HaarEx := UpperTheory.exists_haarMeasure_adelicGL
  have haarConst : HaarConst := UpperTheory.haar_const_of_haar_exists haarEx
  have uniLoc : UniLoc := UpperTheory.local_unimodular_of_exists_haar_measure haarEx
  have rpCen : RPCen := UpperTheory.restrictedProduct_centralizer_adelicGL
  have euler : Euler := UpperTheory.eulerProduct_of_quotient_pushforward_support qpush UpperTheory.euler_product_support_finite
  have sideAbs : SideAbs := UpperTheory.geometric_side_absolutely_convergent_of_euler_fubini euler UpperTheory.orbital_integral_fubini
  have qsub : QSub := UpperTheory.haar_quotient_subgroup
  have rpf : RPF := UpperTheory.restrictedProduct_finite_adelicGL
  have rpe : RPE := UpperTheory.restrictedProduct_extension_of_base_regroup rpf
  have compat : Compat := UpperTheory.adele_galois_action_baseChange_compat
  have galCont : GalCont := UpperTheory.adele_galois_action_continuous compat rpe
  have locEmb : LocEmb := UpperTheory.adele_baseChange_local_isClosedEmbedding
  have unitIff : UnitIff := UpperTheory.adicCompletion_integers_baseChange_iff
  have centLoc : CentLoc := UpperTheory.centralSection_local_scalar
  have centBC : CentBC := UpperTheory.centralSection_baseChange
  have zNorm : ZNorm := UpperTheory.twistedNorm_central_of_baseChange_compat compat centLoc centBC
  have locNorm : LocNorm := UpperTheory.twistedNorm_local_of_compat compat
  have sepLoc : SepLoc := UpperTheory.separableLocal_of_separableScalar UpperTheory.charpoly_separable_unit_smul centLoc
  have tComm : TComm := UpperTheory.torusCommutative_of_centralizerCommutative UpperTheory.centralizer_commutative_of_separable_charpoly
  have triv : Triv := UpperTheory.baseChange_trivial_extension
  have boundE : BoundE := UpperTheory.adelicBound_of_centralizer_localization n5 compat centLoc rpe
  have infF : InfF := UpperTheory.infinitePart_finite_of_adelicBound p2 triv boundE
  have k1F : SelmerRankBoundLaurent := UpperTheory.maximalCompactNorm_of_unit_criterion k1 triv unitIff compat
  have spl : Spl := UpperTheory.splitCentralizer_of_splitEquiv splitEq n5 centBC
  have glob : Glob := UpperTheory.globalOrbitalComparison_of_split qsub splitQ uniOf tComm spl n3 n5 centBC
  have sideF : SideF := UpperTheory.orbitalSideBaseField_of_absoluteConvergence sideAbs rpf rpCen uniLoc uniOf tComm sepLoc centLoc infF
  have sideE : SideE := UpperTheory.orbitalSideExtension_of_absoluteConvergence sideAbs rpf rpe rpCen uniLoc uniOf tComm sepLoc centLoc compat galCont locEmb unitIff locNorm boundE n3 n5 p2
  exact main glob haarConst haarEx rpf rpe rpCen sideF sideE k1 k1F h1 zNorm locNorm sepLoc centLoc
end

