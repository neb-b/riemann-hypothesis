module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0031
public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0047
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemOfEig
section
noncomputable section

namespace LevelTowerAlt

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights TensorProduct

theorem abel_abstract :
    ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L Ψ : Type) [Field L] [NumberField L] [Fintype Ψ] (B : HermitianBundle.{0} L)
      (F F' : Ψ → Submodule (𝓞 L) B.carrier) (m N : ℕ) (La : ℝ), 1 ≤ Fintype.card Ψ * m → 1 ≤ La →
      ((Fintype.card Ψ * N : ℕ) : ℝ) ≤ Real.exp La → Module.finrank (𝓞 L) B.carrier ≤ Fintype.card Ψ * N →
      (∀ τ, B.rank (F τ) ≤ m) →
      B.slopeMax ≤ ((C₀ * Real.log (2 + Module.finrank (𝓞 L) B.carrier + max (-B.normDegree ⊤) 0) : ℝ) : EReal) →
      ∑ τ, B.normDegree (F τ) + ∑ τ, B.normDegree (F' τ) ≤ B.normDegree ⊤ →
      (∀ τ, |B.normDegree (F τ) - B.normDegree (F' τ)| ≤ C₀ * N * La) →
      ∑ τ, B.normDegree (F τ) ≤ C * (Fintype.card Ψ * m) * La := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := LowerBound.InteriorDichotomy.proof C₀ 0 C₀ hC₀ le_rfl hC₀
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro L Ψ _ _ _ B F F' m N La hfm hLa hexp hrank hm hslope hsum0 hdd
  set f : ℝ := (Fintype.card Ψ : ℝ) with hf
  set h : ℝ := -B.normDegree ⊤ with hh
  set n : ℝ := (Module.finrank (𝓞 L) B.carrier : ℝ) with hn
  set g : ℝ := max ((Fintype.card Ψ * N : ℕ) : ℝ) 1 with hg
  set x : ℝ := ∑ τ, B.normDegree (F τ) with hx
  set y : ℝ := ∑ τ, B.normDegree (F' τ) with hy
  have hLa0 : 0 < La := by linarith
  have hf0 : 0 ≤ f := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hg1 : 1 ≤ g := le_max_right _ _
  have hfN : f * N ≤ g := by
    have : ((Fintype.card Ψ * N : ℕ) : ℝ) ≤ g := le_max_left _ _
    simpa [hf] using this
  have hng : n ≤ g := by
    have h1 : n ≤ ((Fintype.card Ψ * N : ℕ) : ℝ) := Nat.cast_le.2 hrank
    exact h1.trans (le_max_left _ _)
  have hfj : (1 : ℝ) ≤ f * m := by
    have : ((1 : ℕ) : ℝ) ≤ ((Fintype.card Ψ * m : ℕ) : ℝ) := by exact_mod_cast hfm
    simpa [hf] using this
  have hgexp : g ≤ Real.exp La := max_le hexp (Real.one_le_exp hLa0.le)

  set μ : ℝ := C₀ * Real.log (2 + n + max h 0) with hμ
  have harg : 1 ≤ 2 + n + max h 0 := by
    have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 := le_max_right h 0
    linarith
  have hμ0 : 0 ≤ μ := mul_nonneg hC₀ (Real.log_nonneg harg)
  have hμg : μ ≤ C₀ * Real.log (2 + g + max h 0) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) hC₀
  have hxle : x ≤ f * m * μ := by
    have h1 : ∀ τ, B.normDegree (F τ) ≤ m * μ := fun τ =>
      (HermitianBundle.normDegree_le_rank_mul B _ μ hslope).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hm τ) hμ0)
    calc x ≤ ∑ _τ : Ψ, (m : ℝ) * μ := Finset.sum_le_sum fun τ _ => h1 τ
      _ = f * m * μ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf]; ring

  have hsum : x + y ≤ -h := by
    rw [hh, neg_neg]
    exact hsum0
  have hxy : x - y ≤ f * (C₀ * N * La) := by
    have h1 : x - y ≤ ∑ _τ : Ψ, C₀ * N * La := by
      rw [hx, hy, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun τ _ => (le_abs_self _).trans (hdd τ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    exact h1
  have hfC : f * (C₀ * N * La) ≤ C₀ * g * La := by
    have : C₀ * (f * N) * La ≤ C₀ * g * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfN hC₀) hLa0.le
    calc f * (C₀ * N * La) = C₀ * (f * N) * La := by ring
      _ ≤ _ := this
  have hyp : LowerBound.InteriorDichotomy.Hyp C₀ 0 C₀ h (-x) g (f * m) La :=
    { one_le_g := hg1
      one_le_fj := hfj
      g_le_exp := hgexp
      one_le_La := hLa
      lower := by
        have h1 : f * m * μ ≤ f * m * (C₀ * Real.log (2 + g + max h 0)) :=
          mul_le_mul_of_nonneg_left hμg (by linarith)
        have h2 : f * m * (C₀ * Real.log (2 + g + max h 0) + 0 * La) =
            f * m * (C₀ * Real.log (2 + g + max h 0)) := by ring
        rw [h2]
        linarith
      upper := by linarith }
  have hfin := hC h (-x) g (f * m) La hyp
  have h1 : C * (f * m) * La ≤ max C 0 * (f * m) * La :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hLa0.le
  have h2 : x ≤ C * (f * m) * La := by linarith
  exact h2.trans h1

theorem mem_eigSp_iff {R M O : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    (ρ : O →+* Module.End R M) (σ : O →+* R) (x : M) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

def intLift {E L : Type} [Field E] [Field L] (σ : 𝓞 E →+* L) : 𝓞 E →+* 𝓞 L where
  toFun a := ⟨σ a, map_isIntegral_int σ (RingOfIntegers.isIntegral a)⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ a b)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ a b)

theorem intLift_apply {E L : Type} [Field E] [Field L] (σ : 𝓞 E →+* L) (a : 𝓞 E) :
    algebraMap (𝓞 L) L (intLift σ a) = σ a := rfl

theorem exists_smul_mem_of_eig {R M O ι : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [CommRing O]
    (ρ : O →+* Module.End R M) (σ : ι → (O →+* R)) (s : ι) (N : Submodule R M) (hN : N ≤ eigSp ρ (σ s))
    (T : Finset ι) (hT : ∀ t ∈ T, σ t ≠ σ s) :
    ∀ y ∈ eigSp ρ (σ s), y ∈ N ⊔ ⨆ t ∈ T, eigSp ρ (σ t) → ∃ d : R, d ≠ 0 ∧ d • y ∈ N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro y _ hy
    refine ⟨1, one_ne_zero, ?_⟩
    simpa using hy
  | insert t T ht ih =>
    intro y hy hy'
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 (hT t (Finset.mem_insert_self _ _))
    let φ : M →ₗ[R] M := ρ a - σ t a • LinearMap.id
    have hφ : ∀ u, ∀ z ∈ eigSp ρ (σ u), φ z = (σ u a - σ t a) • z := fun u z hz => by
      change ρ a z - σ t a • z = _
      rw [(mem_eigSp_iff _ _ _).1 hz a, sub_smul]
    have hle : N ⊔ ⨆ u ∈ insert t T, eigSp ρ (σ u) ≤ (N ⊔ ⨆ u ∈ T, eigSp ρ (σ u)).comap φ := by
      refine sup_le (fun z hz => ?_) (iSup₂_le fun u hu z hz => ?_)
      · rw [Submodule.mem_comap, hφ s z (hN hz)]
        exact Submodule.mem_sup_left (N.smul_mem _ hz)
      · rw [Submodule.mem_comap, hφ u z hz]
        rcases Finset.mem_insert.1 hu with rfl | hu
        · rw [sub_self, zero_smul]
          exact Submodule.zero_mem _
        · exact Submodule.mem_sup_right (Submodule.smul_mem _ _
            (Submodule.mem_iSup_of_mem u (Submodule.mem_iSup_of_mem hu hz)))
    have h1 := hle hy'
    rw [Submodule.mem_comap, hφ s y hy] at h1
    obtain ⟨d, hd, h2⟩ := ih (fun u hu => hT u (Finset.mem_insert_of_mem hu)) _ (Submodule.smul_mem _ _ hy) h1
    exact ⟨d * (σ s a - σ t a), mul_ne_zero hd (sub_ne_zero.2 ha.symm), by rwa [mul_smul]⟩

theorem orthAt_saturation {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    {F F' G G' : Submodule (𝓞 L) B.carrier} (h : OrthAt B F F') (hG : ∀ x ∈ G, ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ F)
    (hG' : ∀ x ∈ G', ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ F') : OrthAt B G G' := by
  intro σ x hx y hy
  obtain ⟨a, ha, hx⟩ := hG x hx
  obtain ⟨b, hb, hy⟩ := hG' y hy
  have h1 : inner ℂ (fibreVec B.metric σ (a • x)) (fibreVec B.metric σ (b • y)) = 0 := h σ _ hx _ hy
  rw [fibreVec_smul, fibreVec_smul, inner_smul_left, inner_smul_right] at h1
  have ha' : σ (a : L) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast ha
  have hb' : σ (b : L) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hb
  exact (mul_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left ((map_ne_zero _).2 ha'))).resolve_left hb'

variable {E L Ψ V : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (ρM : 𝓞 E →+* Module.End (𝓞 L) A.Bq.carrier)

theorem eig_facts (hcard : 2 * Fintype.card Ψ = Module.finrank ℚ E)
    (hρ : ∀ (a : 𝓞 E) (x : A.Λ), A.f ⟨A.ρ a x, A.stable a x x.2⟩ = ρM a (A.f x)) :
    (∀ s, A.Bq.rank (eigSp ρM (intLift (A.σ s))) = A.Bq.rank (A.img s)) ∧
    (∀ s, A.Bq.normDegree (A.img s) ≤ A.Bq.normDegree (eigSp ρM (intLift (A.σ s)))) ∧
    ∑ s, A.Bq.normDegree (eigSp ρM (intLift (A.σ s))) ≤ A.Bq.normDegree ⊤ := by
  classical
  have h1 : ∀ s, A.img s ≤ eigSp ρM (intLift (A.σ s)) := by
    rintro s _ ⟨x, hx, rfl⟩
    have hx' : (x : V) ∈ eigSp A.ρ (A.σ s) := (Submodule.mem_inf.1 hx).2
    refine (mem_eigSp_iff _ _ _).2 fun a => ?_
    rw [← hρ, ← map_smul]
    congr 1
    refine Subtype.ext ?_
    change A.ρ a x = intLift (A.σ s) a • (x : V)
    rw [(mem_eigSp_iff _ _ _).1 hx' a, ← algebraMap_smul L (intLift (A.σ s) a), intLift_apply]
  have h2 : ∀ s, ∀ y ∈ eigSp ρM (intLift (A.σ s)), ∃ a : 𝓞 L, a ≠ 0 ∧ a • y ∈ A.img s := by
    intro s y hy
    have h3 : y ∈ CanonicalFiltration.saturation A.Bq (⨆ t, A.img t) := by
      rw [A.saturation_iSup_img hcard]
      exact Submodule.mem_top
    obtain ⟨c, hc, h3⟩ := h3
    have hle : (⨆ t, A.img t) ≤ A.img s ⊔ ⨆ t ∈ Finset.univ.erase s, eigSp ρM (intLift (A.σ t)) := by
      refine iSup_le fun t z hz => ?_
      by_cases hts : t = s
      · subst hts
        exact Submodule.mem_sup_left hz
      · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem t
          (Submodule.mem_iSup_of_mem (Finset.mem_erase.2 ⟨hts, Finset.mem_univ t⟩) (h1 t hz)))
    obtain ⟨d, hd, h4⟩ := exists_smul_mem_of_eig ρM (fun t => intLift (A.σ t)) s (A.img s) (h1 s) (Finset.univ.erase s)
      (fun t ht h => (Finset.mem_erase.1 ht).1 (A.σ_bij.1 (RingHom.ext fun a => by
        rw [← intLift_apply, ← intLift_apply (A.σ s)]
        exact congrArg _ (DFunLike.congr_fun h a)))) _ (Submodule.smul_mem _ c hy) (hle h3)
    exact ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩
  have mono : ∀ {X Y : Submodule (𝓞 L) A.Bq.carrier}, X ≤ Y → A.Bq.rank X ≤ A.Bq.rank Y := fun h =>
    Submodule.finrank_mono h
  have h5 : ∀ s, A.Bq.rank (eigSp ρM (intLift (A.σ s))) = A.Bq.rank (A.img s) := fun s =>
    le_antisymm ((mono (Y := CanonicalFiltration.saturation A.Bq (A.img s)) fun y hy => h2 s y hy).trans
      (CanonicalFiltration.rank_saturation A.Bq _).le) (mono (h1 s))
  refine ⟨h5, fun s => div_le_div_of_nonneg_right
    (CanonicalFiltration.degree_le_of_le_of_rank_eq A.Bq (h1 s) (h5 s).symm) (Nat.cast_nonneg _), ?_⟩
  have hI := _root_.GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup L A.Bq (Ψ ⊕ Ψ) (fun s => eigSp ρM (intLift (A.σ s))) fun s s' h =>
    orthAt_saturation A.Bq (F := A.img s) (F' := A.img s') (by
      rw [A.img_eq, A.img_eq]
      exact A.orth s s' h) (h2 s) (h2 s')
  have hr : A.Bq.rank (⨆ s, eigSp ρM (intLift (A.σ s))) = A.Bq.rank ⊤ := by
    refine le_antisymm (mono le_top) ?_
    have := CanonicalFiltration.rank_saturation A.Bq (⨆ s, A.img s)
    rw [A.saturation_iSup_img hcard] at this
    rw [this]
    exact mono (iSup_mono h1)
  rw [← hI.1]
  exact div_le_div_of_nonneg_right (CanonicalFiltration.degree_le_of_le_of_rank_eq A.Bq le_top hr) (Nat.cast_nonneg _)

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LimsupAddTendsto
section
open Filter Topology Metric Set
open ReciprocityTheory.AnForm.A (IsPsh coordDiv limsupExt molli shrink polyMax)

namespace LevelTowerAlt.Bdd

theorem isPsh_comp {m n : ℕ} {U : Set (Fin n → ℂ)} {V : Set (Fin m → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    {u : (Fin n → ℂ) → ℝ} (hc : ContinuousOn u U) (hu : IsPsh U u) {F : (Fin m → ℂ) → Fin n → ℂ}
    (hF : AnalyticOnNhd ℂ F V) (hFU : MapsTo F V U) : IsPsh V (fun v => u (F v)) := by
  have hcF : ContinuousOn (fun v => u (F v)) V := hc.comp hF.continuousOn hFU
  refine ⟨hcF.upperSemicontinuousOn, fun z w hd => ?_⟩
  have hl : Continuous fun ζ : ℂ => z + ζ • w := by fun_prop
  have hmaps : MapsTo (fun ζ : ℂ => z + ζ • w) (closedBall 0 1) V := fun ζ hζ => hd ζ (by simpa using hζ)
  have hint : CircleIntegrable (fun ζ : ℂ => u (F (z + ζ • w))) 0 1 :=
    ((hcF.comp hl.continuousOn hmaps).mono sphere_subset_closedBall).circleIntegrable zero_le_one
  refine ⟨hint, le_of_forall_pos_le_add fun η hη => ?_⟩
  have hK : IsCompact ((fun ζ : ℂ => F (z + ζ • w)) '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn (hF.continuousOn.comp hl.continuousOn hmaps)
  set Kc := (fun ζ : ℂ => F (z + ζ • w)) '' closedBall 0 1 with hKc
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hU
    (by rintro _ ⟨ζ, hζ, rfl⟩; exact hFU (hmaps hζ))
  have huc := (hK.cthickening (r := δ₀)).uniformContinuousOn_of_continuous (hc.mono hsub)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm n
  have hε : 0 < min δ₀ (δ / 2) := lt_min hδ₀ (half_pos hδ)
  set ε := min δ₀ (δ / 2) with hεd
  obtain ⟨ho, hsm, hp, hb⟩ := (ReciprocityTheory.AnForm.A.mollify_thm n ρ U u hU hu).1 ε hε
  have hball : ∀ x ∈ Kc, closedBall x ε ⊆ cthickening δ₀ Kc := fun x hx =>
    (closedBall_subset_closedBall (min_le_left _ _)).trans (closedBall_subset_cthickening hx δ₀)
  have hshr : ∀ x ∈ Kc, x ∈ shrink U ε := fun x hx => (hball x hx).trans hsub
  have hup : ∀ x ∈ Kc, molli ρ ε u x ≤ u x + η := fun x hx => by
    refine (hb x (hshr x hx)).2.trans (csSup_le ⟨_, x, mem_closedBall_self hε.le, rfl⟩ ?_)
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hδu y (hball x hx hy) x (hball x hx (mem_closedBall_self hε.le))
      ((mem_closedBall.1 hy).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hδ)))
    rw [Real.dist_eq] at h1
    linarith [le_abs_self (u y - u x)]
  have hV' : IsOpen (V ∩ F ⁻¹' shrink U ε) := hF.continuousOn.isOpen_inter_preimage hV ho
  have h2 : ContDiffOn ℝ 2 (molli ρ ε u) (shrink U ε) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hlevi := (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm n _ _ ho h2).1 hp
  have hC : ContDiffOn ℝ 2 (molli ρ ε u ∘ F) (V ∩ F ⁻¹' shrink U ε) := fun v hv =>
    ((h2.contDiffAt (ho.mem_nhds hv.2)).comp v
      ((hF v hv.1).restrictScalars (𝕜 := ℝ)).contDiffAt).contDiffWithinAt
  have hP : IsPsh (V ∩ F ⁻¹' shrink U ε) (molli ρ ε u ∘ F) :=
    (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm m _ _ hV' hC).2 ⟨hC, fun v hv a => by
      rw [ReciprocityTheory.AnForm.levi_comp a (hF v hv.1) (h2.contDiffAt (ho.mem_nhds hv.2))]
      exact hlevi.2 _ hv.2 _⟩
  obtain ⟨hi2, hle⟩ := hP.2 z w fun ζ hζ => ⟨hd ζ hζ, hshr _ ⟨ζ, by simpa using hζ, rfl⟩⟩
  have hz : F z ∈ Kc := ⟨0, mem_closedBall_self zero_le_one, by simp⟩
  have h3 := Real.circleAverage_mono hi2 (hint.add (circleIntegrable_const η 0 1)) fun ζ hζ =>
    hup _ ⟨ζ, sphere_subset_closedBall (by simpa using hζ), rfl⟩
  rw [Real.circleAverage_add hint (circleIntegrable_const η 0 1), Real.circleAverage_const] at h3
  exact ((hb _ (hshr _ hz)).1.trans hle).trans h3

def PH {n : ℕ} (f : (Fin n → ℂ) → ℝ) (v : Fin n → ℂ) : Prop :=
  ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G v ∧ ∀ᶠ u in 𝓝 v, f u = (G u).re

theorem PH.add {n : ℕ} {f g : (Fin n → ℂ) → ℝ} {v : Fin n → ℂ} (hf : PH f v) (hg : PH g v) :
    PH (fun u => f u + g u) v := by
  obtain ⟨F, hF, h1⟩ := hf
  obtain ⟨G, hG, h2⟩ := hg
  refine ⟨fun u => F u + G u, hF.add hG, ?_⟩
  filter_upwards [h1, h2] with u a b
  rw [a, b, Complex.add_re]

theorem PH.const_mul {n : ℕ} {f : (Fin n → ℂ) → ℝ} {v : Fin n → ℂ} (hf : PH f v) (c : ℝ) :
    PH (fun u => c * f u) v := by
  obtain ⟨F, hF, h1⟩ := hf
  refine ⟨fun u => (c : ℂ) * F u, analyticAt_const.mul hF, ?_⟩
  filter_upwards [h1] with u a
  rw [a, Complex.re_ofReal_mul]

theorem PH.sum {n : ℕ} {σ : Type} (s : Finset σ) {f : σ → (Fin n → ℂ) → ℝ} {v : Fin n → ℂ}
    (hf : ∀ i ∈ s, PH (f i) v) : PH (fun u => ∑ i ∈ s, f i u) v := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, analyticAt_const, by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

theorem PH.log_norm {n : ℕ} {F : (Fin n → ℂ) → ℂ} {v : Fin n → ℂ} (hF : AnalyticAt ℂ F v) (h0 : F v ≠ 0) :
    PH (fun u => Real.log ‖F u‖) v := by
  have hH : AnalyticAt ℂ (fun t => F t / F v) v := hF.div analyticAt_const h0
  refine ⟨fun t => Complex.log (F t / F v) + (Real.log ‖F v‖ : ℝ),
    (hH.clog (by rw [div_self h0]; exact Complex.one_mem_slitPlane)).add analyticAt_const, ?_⟩
  filter_upwards [hF.continuousAt.eventually_ne h0] with t ht
  rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.2 ht) (norm_ne_zero_iff.2 h0)]
  ring

theorem local_psh {m n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) {φ : (Fin n → ℂ) → ℝ} (hc : ContinuousOn φ U)
    (hφ : IsPsh U φ) {F : (Fin m → ℂ) → Fin n → ℂ} {v : Fin m → ℂ} (hF : AnalyticAt ℂ F v) (hv : F v ∈ U)
    {f g : (Fin m → ℂ) → ℝ} (hf : PH f v) (hg : ∀ᶠ u in 𝓝 v, g u = φ (F u) + f u) :
    ContinuousAt g v ∧ ∃ V, IsOpen V ∧ v ∈ V ∧ IsPsh V g := by
  obtain ⟨G, hG, hfG⟩ := hf
  have he : ∀ᶠ u in 𝓝 v, g u = φ (F u) + (G u).re + 0 := by
    filter_upwards [hg, hfG] with u a b
    rw [a, b, add_zero]
  refine ⟨?_, ?_⟩
  · have h1 : ContinuousAt (fun u => φ (F u) + (G u).re + 0) v :=
      (((hc.continuousAt (hU.mem_nhds hv)).comp hF.continuousAt).add
        (Complex.continuous_re.continuousAt.comp hG.continuousAt)).add continuousAt_const
    exact h1.congr (he.mono fun u h => h.symm)
  · obtain ⟨V, hV, hVo, hvV⟩ := _root_.eventually_nhds_iff.1 ((he.and hF.eventually_analyticAt).and
      (hG.eventually_analyticAt.and (hF.continuousAt.eventually (hU.mem_nhds hv))))
    refine ⟨V, hVo, hvV, GroundTheory.Heights₂.Heights.Regular.isPsh_congr (fun u hu => (hV u hu).1.1.symm) ?_⟩
    exact GroundTheory.Heights₂.Heights.NineStatements.isPsh_add_re_add_const hVo
      (isPsh_comp hU hVo hc hφ (fun u hu => (hV u hu).1.2) fun u hu => (hV u hu).2.2)
      (fun u hu => (hV u hu).2.1.differentiableAt.differentiableWithinAt) 0

theorem limsup_add_tendsto {α : Type} {l : Filter α} [l.NeBot] {q g : α → ℝ} {a C : ℝ} (hq : Tendsto q l (𝓝 a))
    (hg : ∀ᶠ x in l, |g x| ≤ C) : limsup (fun x => q x + g x) l = a + limsup g l := by
  have g1 : IsBoundedUnder (· ≤ ·) l g := isBoundedUnder_of_eventually_le (hg.mono fun x h => (abs_le.1 h).2)
  have g2 : IsCoboundedUnder (· ≤ ·) l g :=
    isCoboundedUnder_le_of_eventually_le l (hg.mono fun x h => (abs_le.1 h).1)
  refine le_antisymm ?_ ?_
  · have := limsup_add_le hq.isBoundedUnder_ge hq.isBoundedUnder_le g2 g1
    rwa [hq.limsup_eq] at this
  · have := le_limsup_add g1 g2 hq.isBoundedUnder_le hq.isBoundedUnder_ge
    rw [hq.liminf_eq, add_comm, add_comm g q] at this
    exact this

theorem abs_limsup_le {α : Type} {l : Filter α} [l.NeBot] {g : α → ℝ} {C : ℝ}
    (hg : ∀ᶠ x in l, |g x| ≤ C) : |limsup g l| ≤ C :=
  abs_le.2 ⟨le_limsup_of_frequently_le (hg.mono fun _ h => (abs_le.1 h).1).frequently
      (isBoundedUnder_of_eventually_le (hg.mono fun _ h => (abs_le.1 h).2)),
    limsup_le_of_le (isCoboundedUnder_le_of_eventually_le l (hg.mono fun _ h => (abs_le.1 h).1))
      (hg.mono fun _ h => (abs_le.1 h).2)⟩

theorem isPsh_ext {n : ℕ} {T : Set (Fin n → ℂ)} (hT : IsOpen T) (hT1 : T ⊆ ball 0 1) (S : Finset (Fin n))
    {q g g' : (Fin n → ℂ) → ℝ} {C : ℝ} (hq : ContinuousOn q T) (hg : ∀ v ∈ T \ coordDiv S, |g v| ≤ C)
    (hc : ContinuousOn (fun v => q v + g v) (T \ coordDiv S)) (hp : IsPsh (T \ coordDiv S) fun v => q v + g v)
    (h1 : ∀ v ∈ T \ coordDiv S, g' v = g v)
    (h2 : ∀ v ∈ T, v ∈ coordDiv S → g' v = limsup g (𝓝[T \ coordDiv S] v)) :
    IsPsh T fun v => q v + g' v := by
  refine _root_.GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n T _ hT fun v₀ hv₀ => ?_
  obtain ⟨δ, hδ, hδT⟩ := nhds_basis_closedBall.mem_iff.1 (hT.mem_nhds hv₀)
  obtain ⟨Mq, hMq⟩ := (isCompact_closedBall v₀ δ).exists_bound_of_continuousOn (hq.mono hδT)
  have hUT : ball v₀ δ ⊆ T := ball_subset_closedBall.trans hδT
  have hD : ball v₀ δ \ coordDiv S ⊆ T \ coordDiv S := sdiff_subset_sdiff_left hUT
  have hab : ∀ v ∈ ball v₀ δ \ coordDiv S, |q v + g v| ≤ Mq + C := fun v hv =>
    (abs_add_le _ _).trans (add_le_add (hMq v (ball_subset_closedBall hv.1)) (hg v (hD hv)))
  have hext := (ReciprocityTheory.AnForm.A.pshExtension_thm n S (ball v₀ δ) (fun v => q v + g v) |Mq + C| isOpen_ball
    (hUT.trans hT1) (hc.mono hD) (GroundTheory.Heights₂.Heights.Regular.isPsh_mono hp hD) fun y hy => by
      have hy1 : ‖y‖ < 1 := by simpa using hT1 (hUT hy.1)
      have hs : 0 ≤ ∑ i ∈ S, Real.log ‖y i‖⁻¹ := Finset.sum_nonneg fun i _ => by
        rw [Real.log_inv]
        exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))
      have hL : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖y i‖⁻¹) := by
        have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))
        rwa [Real.log_exp] at this
      exact (((le_abs_self _).trans (hab y hy)).trans (le_abs_self _)).trans
        (le_mul_of_one_le_right (abs_nonneg _) hL)).2 (Mq + C)
  refine ⟨ball v₀ δ, isOpen_ball, mem_ball_self hδ, GroundTheory.Heights₂.Heights.Regular.isPsh_congr (fun v hv => ?_) hext⟩
  have hmax : ∀ y ∈ ball v₀ δ \ coordDiv S, max (q y + g y) (-(Mq + C)) = q y + g y := fun y hy =>
    max_eq_left (abs_le.1 (hab y hy)).1
  unfold limsupExt
  split_ifs with hS
  · have hf : 𝓝[ball v₀ δ \ coordDiv S] v = 𝓝[T \ coordDiv S] v :=
      nhdsWithin_eq_nhdsWithin' (isOpen_ball.mem_nhds hv) (Set.ext fun y =>
        ⟨fun h => ⟨hD h.1, h.2⟩, fun h => ⟨⟨h.2, h.1.2⟩, h.2⟩⟩)
    have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := S) hT (hUT hv)
    rw [limsup_congr (v := fun y => q y + g y) (eventually_nhdsWithin_of_forall hmax), hf]
    show _ = q v + g' v
    rw [h2 v (hUT hv) hS]
    exact limsup_add_tendsto ((hq.continuousAt (hT.mem_nhds (hUT hv))).tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall hg)
  · show max (q v + g v) (-(Mq + C)) = q v + g' v
    rw [hmax v ⟨hv, hS⟩, h1 v ⟨hUT hv, hS⟩]

end LevelTowerAlt.Bdd
end

