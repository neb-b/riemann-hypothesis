module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.HomCount
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem padic_hom_zero {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] (hM : ∀ y : M, l • y = 0)
    (φ : ℤ_[l] →+ M) (h1 : φ 1 = 0) (c : ℤ_[l]) : φ c = 0 := by
  have hn : ∀ n : ℕ, φ (n : ℤ_[l]) = 0 := fun n => by
    rw [← nsmul_one, map_nsmul, h1, smul_zero]
  have hmem := PadicInt.sub_zmodRepr_mem c
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
  obtain ⟨a, ha⟩ := hmem
  have hc : c = (c.zmodRepr : ℤ_[l]) + l • a := by
    rw [nsmul_eq_mul, mul_comm, ha]
    ring
  rw [hc, map_add (f := _), hn, map_nsmul, hM, add_zero]

private theorem free_hom_zero {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] (hM : ∀ y : M, l • y = 0)
    {d : ℕ} (f : ((Fin d → ℤ_[l]) × ℤ_[l]) →+ M) (h1 : ∀ i, f (Pi.single i 1, 0) = 0) (h2 : f (0, 1) = 0)
    (v : (Fin d → ℤ_[l]) × ℤ_[l]) : f v = 0 := by
  have e1 : ∀ i c, f (Pi.single i c, 0) = 0 := fun i c =>
    padic_hom_zero hM (f.comp ((AddMonoidHom.inl _ _).comp (AddMonoidHom.single (fun _ : Fin d => ℤ_[l]) i)))
      (h1 i) c
  have e2 : ∀ c, f (0, c) = 0 := fun c =>
    padic_hom_zero hM (f.comp (AddMonoidHom.inr _ _)) h2 c
  obtain ⟨u, w⟩ := v
  have hs : ((u, w) : (Fin d → ℤ_[l]) × ℤ_[l]) = (∑ i, ((Pi.single i (u i), 0) : (Fin d → ℤ_[l]) × ℤ_[l])) + (0, w) := by
    ext j
    · simp [Prod.fst_sum, Finset.univ_sum_single]
    · simp [Prod.snd_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, map_add (f := _), map_sum, e2, add_zero]
  exact Finset.sum_eq_zero fun i _ => e1 i (u i)

private theorem eq_zero_of_eq_self_add_self {M : Type} [AddCommGroup M] (a : M) (h : a = a + a) : a = 0 := by
  have := congrArg (fun x => x - a) h
  simpa using this.symm

private theorem char_zero {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M] [Finite M] (hM : ∀ y : M, l • y = 0)
    {D : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] {I : Subgroup D} {d : ℕ} (A : LocAb l D I d)
    (s : Fin d → D) (t : D) (hs : ∀ i, A.a (s i) = Multiplicative.ofAdd (Pi.single i 1, 0))
    (ht : A.a t = Multiplicative.ofAdd (0, 1))
    (z : D → M) (hz : IsLocallyConstant z) (hm : ∀ g h, z (g * h) = z g + z h) (hμ : ∀ g ∈ muG l D, z g = 0)
    (h1 : ∀ i, z (s i) = 0) (h2 : z t = 0) (g : D) : z g = 0 := by
  have hz1 : z 1 = 0 := by
    have := hm 1 1
    rw [one_mul] at this
    exact eq_zero_of_eq_self_add_self _ this
  let χ : D →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (z g)
      map_one' := by simp [hz1]
      map_mul' := fun g h => by simp [hm] }
  have hP : IsPGroup l (Multiplicative M) := fun g => ⟨1, by
    rw [pow_one]
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, hM]⟩
  have hχ : ∀ g, g ∈ χ.ker ↔ z g = 0 := fun g => by
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (z g) = 1 ↔ _
    exact ofAdd_eq_one
  have hopen : IsOpen (χ.ker : Set D) := by
    have : (χ.ker : Set D) = z ⁻¹' {0} := by
      ext g
      exact hχ g
    rw [this]
    exact hz.isOpen_fiber 0
  have hmu : muG l D ≤ χ.ker := fun g hg => (hχ g).mpr (hμ g hg)
  have hker := A.univ (Multiplicative M) hP χ hopen hmu
  have dep : ∀ g g', A.a g = A.a g' → z g = z g' := by
    intro g g' h
    have hk : g⁻¹ * g' ∈ A.a.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h0 := (hχ _).mp (hker hk)
    have := hm g (g⁻¹ * g')
    rw [mul_inv_cancel_left, h0, add_zero] at this
    exact this.symm
  let pre : (Fin d → ℤ_[l]) × ℤ_[l] → D := fun v => Classical.choose (A.surj (Multiplicative.ofAdd v))
  have hpre : ∀ v, A.a (pre v) = Multiplicative.ofAdd v := fun v => Classical.choose_spec (A.surj _)
  let φ : ((Fin d → ℤ_[l]) × ℤ_[l]) →+ M := AddMonoidHom.mk' (fun v => z (pre v)) (by
    intro v w
    rw [← hm]
    apply dep
    rw [map_mul, hpre, hpre, hpre]
    rfl)
  have hφ := free_hom_zero hM φ (fun i => by
      show z (pre _) = 0
      rw [dep _ (s i) (by rw [hpre, hs])]
      exact h1 i)
    (by
      show z (pre _) = 0
      rw [dep _ t (by rw [hpre, ht])]
      exact h2)
    (Multiplicative.toAdd (A.a g))
  have : φ (Multiplicative.toAdd (A.a g)) = z g := by
    show z (pre _) = z g
    apply dep
    rw [hpre]
    rfl
  rw [← this, hφ]

theorem UpperTheory.V.Pa.homCount :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] (I : Subgroup D) (d m : ℕ), LocAb l D I d → {z : D → x.Am m | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧ ∀ g ∈ muG l D, z g = 0}.Finite ∧ {z : D → x.Am m | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧ ∀ g ∈ muG l D, z g = 0}.ncard ≤ Nat.card x.K ^ (m * (d + 1)) := by
  intro l _ F n x D _ _ _ I d m A
  obtain ⟨hfin, hcard, -, hl, -⟩ := finAm l F n x m 0
  haveI := hfin
  have hs : ∀ i, A.a (Classical.choose (A.surj (Multiplicative.ofAdd ((Pi.single i 1, 0) : (Fin d → ℤ_[l]) × ℤ_[l])))) =
      Multiplicative.ofAdd ((Pi.single i 1, 0) : (Fin d → ℤ_[l]) × ℤ_[l]) :=
    fun i => Classical.choose_spec (A.surj _)
  have ht : A.a (Classical.choose (A.surj (Multiplicative.ofAdd ((0, 1) : (Fin d → ℤ_[l]) × ℤ_[l])))) =
      Multiplicative.ofAdd ((0, 1) : (Fin d → ℤ_[l]) × ℤ_[l]) :=
    Classical.choose_spec (A.surj _)
  set s : Fin d → D := fun i => Classical.choose (A.surj (Multiplicative.ofAdd ((Pi.single i 1, 0) : (Fin d → ℤ_[l]) × ℤ_[l]))) with hs_def
  set t : D := Classical.choose (A.surj (Multiplicative.ofAdd ((0, 1) : (Fin d → ℤ_[l]) × ℤ_[l]))) with ht_def
  set S := {z : D → x.Am m | IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + z h) ∧ ∀ g ∈ muG l D, z g = 0} with hS
  let ev : (D → x.Am m) → (Fin d → x.Am m) × x.Am m := fun z => (fun i => z (s i), z t)
  have hinj : Set.InjOn ev S := by
    intro z hz z' hz' he
    funext g
    have key := char_zero hl A s t hs ht (z - z') (hz.1.sub hz'.1)
      (fun g h => by
        simp only [Pi.sub_apply, hz.2.1, hz'.2.1]
        abel)
      (fun g hg => by simp [hz.2.2 g hg, hz'.2.2 g hg])
      (fun i => by
        simp only [Pi.sub_apply, sub_eq_zero]
        exact congrFun (congrArg Prod.fst he) i)
      (by
        simp only [Pi.sub_apply, sub_eq_zero]
        exact congrArg Prod.snd he) g
    exact sub_eq_zero.mp key
  refine ⟨Set.Finite.of_finite_image (Set.toFinite _) hinj, ?_⟩
  rw [← hinj.ncard_image]
  refine (Set.ncard_le_card _).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, hcard, ← pow_succ, ← pow_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem lc_of_open {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ))
    (h : ∀ m, IsLocallyConstant fun g : H => ρ g m) : LC ρ := by
  intro m
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hU : IsOpen ((Subtype.val : H → Γ) '' {z : H | ρ z m = m}) :=
    hH.isOpenMap_subtype_val _ ((h m).isOpen_fiber m)
  have h1 : (1 : Γ) ∈ (Subtype.val : H → Γ) '' {z : H | ρ z m = m} := ⟨1, by simp, rfl⟩
  have ht : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
    have h0 := (continuous_const_mul x⁻¹).tendsto x
    simpa using h0
  filter_upwards [ht (hU.mem_nhds h1)] with y hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hz' : ρ z m = m := hz
  have hy : y = x * z := by rw [hzy]; group
  rw [hy, map_mul]
  show ρ x (ρ z m) = ρ x m
  rw [hz']

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    intro i j
    exact (h i j).eventually_eq x
  filter_upwards [hev] with y hy
  exact Matrix.ext hy

private theorem lc_padic {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f : ℤ_[l] →+* R) (hl : (l : R) = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ‖y - x‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    simpa [dist_eq_norm] using hy
  filter_upwards [hev] with y hy
  obtain ⟨z, hz⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hy
  have hyz : y = x + (l : ℤ_[l]) * z := by rw [← hz]; ring
  rw [hyz, map_add (f := _), map_mul, map_natCast, hl, zero_mul, add_zero]

private theorem maximalIdeal_powerSeries_eq_span_X (K : Type) [Field K] :
    IsLocalRing.maximalIdeal (PowerSeries K) = Ideal.span {(PowerSeries.X : PowerSeries K)} := by
  ext φ
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
    PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]

private theorem isLocallyConstant_pi_of_forall_isLocallyConstant {Γ ι Y : Type} [TopologicalSpace Γ] [Finite ι] (f : Γ → ι → Y)
    (h : ∀ i, IsLocallyConstant fun g => f g i) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hev : ∀ᶠ y in nhds x, ∀ i, f y i = f x i :=
    Filter.eventually_all.2 fun i => (h i).eventually_eq x
  filter_upwards [hev] with y hy
  exact funext hy

private theorem isLocallyConstant_comp_of_adicCont_of_pow_eq_zero {Γ A B : Type} [TopologicalSpace Γ] [CommRing A] [CommRing B] (s : A) (N : ℕ)
    (φ : A →+* B) (hs : φ s ^ N = 0) (f : Γ → A) (hf : AdicCont (Ideal.span {s}) f) :
    IsLocallyConstant fun g => φ (f g) := by
  have hI : ∀ a ∈ Ideal.span {s} ^ N, φ a = 0 := by
    intro a ha
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, map_pow, hs, mul_zero]
  have h2 := (hf N).comp (Ideal.Quotient.lift (Ideal.span {s} ^ N) φ hI)
  convert h2 using 1
  funext g
  exact (Ideal.Quotient.lift_mk (Ideal.span {s} ^ N) φ hI).symm

theorem UpperTheory.V.Pa.lc1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), (IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g)) ∧ (IsLocallyConstant fun g : G.Γ => epsD k (x.Am m) (h.p g)) ∧ ∀ (χ : G.Γ → DD (x.Am m) k.g) (V : Submodule x.A (Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) (rep : Representation x.A G.Γ V), IsLocallyConstant χ → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) χ V rep → LC rep := by
  intro l _ L G G0 h n x k m
  obtain ⟨-, -, -, -, hlD, htA, htD, -, -⟩ := finAm l G0.frame n x m k.g
  have hM : IsLocalRing.maximalIdeal (PowerSeries x.K) = Ideal.span {x.t} := maximalIdeal_powerSeries_eq_span_X x.K
  have hp0 : Continuous h.p₀ := continuous_induced_rng.2 (h.cont.comp continuous_subtype_val)
  have hE : IsLocallyConstant fun g : G0.G₀ =>
      DD.epM (fun j => (k.κ j g).map (algebraMap x.A (x.Am m))) := by
    apply lc_mat
    intro a b
    have hv : IsLocallyConstant fun g : G0.G₀ => fun j => algebraMap x.A (x.Am m) (k.κ j g a b) := by
      apply isLocallyConstant_pi_of_forall_isLocallyConstant
      intro j
      exact isLocallyConstant_comp_of_adicCont_of_pow_eq_zero (algebraMap x.A x.A x.t) m (algebraMap x.A (x.Am m)) (by simpa using htA) _
        ((k.mem j).2.1 a b)
    exact hv.comp (fun v => ({ a := 0, ep := v, ep' := 0, eta := 0 } : DD (x.Am m) k.g))
  have hR : IsLocallyConstant fun g : G0.G₀ => x.ρX (DD (x.Am m) k.g) g := by
    apply lc_mat
    intro a b
    simp only [NP.ρX, Matrix.map_apply]
    exact isLocallyConstant_comp_of_adicCont_of_pow_eq_zero x.t m (algebraMap x.A (DD (x.Am m) k.g)) htD _ (by rw [← hM]; exact x.cont a b)
  have hρ : IsLocallyConstant fun g : G0.G₀ => k.ρ1 (x.Am m) g :=
    (hE.comp (fun M => 1 + M)).comp₂ hR (· * ·)
  have hρ' : IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g) := hρ.comp_continuous hp0
  refine ⟨hρ', ?_, ?_⟩
  · have hl' : ((l : ℕ) : DD (x.Am m) k.g) = 0 := by simpa using hlD 1
    exact (lc_padic ((algebraMap x.A (DD (x.Am m) k.g)).comp (algebraMap ℤ_[l] x.A)) hl').comp_continuous
      (Units.continuous_val.comp (G0.ε_cont.comp h.cont))
  · intro χ V rep hχ hAd
    apply lc_of_open rep G.η.ker G.η_open
    intro Z
    have hinv : IsLocallyConstant fun g : G.G₀ => k.ρ1 (x.Am m) (h.p₀ g⁻¹) :=
      hρ'.comp_continuous continuous_inv
    have hχ' : IsLocallyConstant fun g : G.G₀ => χ g := hχ.comp_continuous continuous_subtype_val
    have key : IsLocallyConstant fun g : G.G₀ => ((rep g Z : V) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) := by
      have e : (fun g : G.G₀ => ((rep g Z : V) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) =
          fun g : G.G₀ => χ g • (k.ρ1 (x.Am m) (h.p₀ g) * (Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) *
            k.ρ1 (x.Am m) (h.p₀ g⁻¹)) := by
        funext g
        exact hAd.1 g Z
      rw [e]
      exact hχ'.comp₂ (hρ'.comp₂ hinv fun A B => A * (Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * B)
        fun c M => c • M
    exact (IsLocallyConstant.iff_eventually_eq _).2 fun g =>
      (key.eventually_eq g).mono fun y hy => Subtype.ext hy
end

