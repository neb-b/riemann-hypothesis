module

public import Mathlib
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithful
section
open CompanionTheory.Rg.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeBasis

variable {G : Type} [Group G] (K : Subgroup G)

theorem lam_single (g : G) (y : G ⧸ K) (c : ℂ) :
    lam K g (Finsupp.single y c) = Finsupp.single (g • y) c := by
  simp [lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem lam_mul (g g' : G) (u : (G ⧸ K) →₀ ℂ) :
    lam K (g * g') u = lam K g (lam K g' u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y c => simp [lam_single, mul_smul]

theorem lam_one (u : (G ⧸ K) →₀ ℂ) : lam K 1 u = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y c => simp [lam_single]

theorem lam_apply_smul (g : G) (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) :
    lam K g u (g • y) = u y :=
  Finsupp.mapDomain_apply_of_injective (MulAction.injective g) u y

def IsFixed (u : (G ⧸ K) →₀ ℂ) : Prop := ∀ k ∈ K, lam K k u = u

variable {K}

theorem lam_congr {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x x' : G}
    (h : (x : G ⧸ K) = x') : lam K x u = lam K x' u := by
  have hk : x⁻¹ * x' ∈ K := QuotientGroup.eq.1 h
  have : x' = x * (x⁻¹ * x') := by group
  rw [this, lam_mul, hu _ hk]

variable (K)

def op (u : (G ⧸ K) →₀ ℂ) : Module.End ℂ ((G ⧸ K) →₀ ℂ) :=
  Finsupp.lsum ℂ fun y => LinearMap.toSpanSingleton ℂ _ (lam K (Quotient.out y) u)

theorem op_single_out (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) (c : ℂ) :
    op K u (Finsupp.single y c) = c • lam K (Quotient.out y) u := by
  simp [op, LinearMap.toSpanSingleton_apply]

variable {K}

theorem op_single {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) (x : G) (c : ℂ) :
    op K u (Finsupp.single (x : G ⧸ K) c) = c • lam K x u := by
  rw [op_single_out, lam_congr hu (QuotientGroup.out_eq' (x : G ⧸ K))]

theorem op_mem {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u ∈ Hk K := by
  rw [Hk, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hgx : g • (x : G ⧸ K) = ((g * x : G) : G ⧸ K) := rfl
    simp only [Finsupp.lsingle_apply, Module.End.mul_apply, LinearMap.comp_apply]
    rw [op_single hu, lam_single, hgx, op_single hu, lam_mul]
    simp

variable (K)

def delta : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1

theorem lam_delta (x : G) : lam K x (delta K) = Finsupp.single (x : G ⧸ K) 1 := by
  have : x • ((1 : G) : G ⧸ K) = (x : G ⧸ K) := by
    change ((x * 1 : G) : G ⧸ K) = x
    rw [mul_one]
  rw [delta, lam_single, this]

theorem delta_fixed_eval (h : Hk K) : IsFixed K ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) := by
  intro k hk
  have hc : lam K k * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K k :=
    (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨k, rfl⟩
  have hd : lam K k (delta K) = delta K := by
    have hk1 : (k : G ⧸ K) = ((1 : G) : G ⧸ K) :=
      QuotientGroup.eq.2 (by simpa using K.inv_mem hk)
    rw [lam_delta, delta, hk1]
  have := LinearMap.congr_fun hc (delta K)
  simp only [Module.End.mul_apply] at this
  rw [this, hd]

variable {K}

theorem op_delta {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u (delta K) = u := by
  rw [delta, op_single hu, lam_one, one_smul]

theorem eq_zero_of_delta (h : Hk K)
    (h0 : (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = 0) : h = 0 := by
  apply Subtype.ext
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hc : lam K x * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K x :=
      (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨x, rfl⟩
    have := LinearMap.congr_fun hc (delta K)
    simp only [Module.End.mul_apply] at this
    rw [h0, map_zero, lam_delta] at this
    simpa using this.symm

def orbitVec (hK : IsHeckePair K) (g : G) : (G ⧸ K) →₀ ℂ :=
  ∑ y ∈ (hK g).toFinset, Finsupp.single y (1 : ℂ)

open Classical in
theorem orbitVec_apply (hK : IsHeckePair K) (g : G) (z : G ⧸ K) :
    orbitVec hK g z = if z ∈ MulAction.orbit K (g : G ⧸ K) then 1 else 0 := by
  classical
  simp [orbitVec, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem lam_apply (k : G) (u : (G ⧸ K) →₀ ℂ) (z : G ⧸ K) :
    lam K k u z = u ((k⁻¹ : G) • z) := by
  have := lam_apply_smul K k u ((k⁻¹ : G) • z)
  rwa [smul_inv_smul] at this

theorem orbitVec_fixed (hK : IsHeckePair K) (g : G) : IsFixed K (orbitVec hK g) := by
  classical
  intro k hk
  ext z
  have hmem : ((k⁻¹ : G) • z ∈ MulAction.orbit K (g : G ⧸ K)) ↔
      z ∈ MulAction.orbit K (g : G ⧸ K) := by
    have e : (k⁻¹ : G) • z = (⟨k, hk⟩ : K)⁻¹ • z := rfl
    rw [e, ← MulAction.orbit_eq_iff, ← MulAction.orbit_eq_iff (a := z), MulAction.orbit_smul]
  rw [lam_apply, orbitVec_apply, orbitVec_apply]
  simp only [hmem]

theorem IsFixed.apply_of_mem_orbit {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x z : G ⧸ K}
    (hz : z ∈ MulAction.orbit K x) : u z = u x := by
  obtain ⟨k, rfl⟩ := hz
  have h := lam_apply_smul K (k : G) u x
  rw [hu _ k.2] at h
  exact h

def heckeOp (hK : IsHeckePair K) (g : G) : Hk K :=
  ⟨op K (orbitVec hK g), op_mem (orbitVec_fixed hK g)⟩

theorem heckeOp_delta (hK : IsHeckePair K) (g : G) :
    (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = orbitVec hK g :=
  op_delta (orbitVec_fixed hK g)

theorem exists_mem_span_delta (hK : IsHeckePair K) (n : ℕ) :
    ∀ u : (G ⧸ K) →₀ ℂ, IsFixed K u → u.support.card ≤ n →
      ∃ t ∈ Submodule.span ℂ (Set.range (heckeOp hK)),
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = u := by
  classical
  induction n with
  | zero =>
    intro u _ hc
    have : u = 0 := by simpa using hc
    exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
  | succ n ih =>
    intro u hu hc
    by_cases h0 : u = 0
    · exact ⟨0, Submodule.zero_mem _, by simp [h0]⟩
    obtain ⟨y, hy⟩ := Finsupp.support_nonempty_iff.2 h0
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    set c := u (g : G ⧸ K) with hcdef
    have hc0 : c ≠ 0 := Finsupp.mem_support_iff.1 hy
    have hfix : IsFixed K (u - c • orbitVec hK g) := by
      intro k hk
      rw [map_sub, map_smul, hu k hk, orbitVec_fixed hK g k hk]
    have hsub : (u - c • orbitVec hK g).support ⊆ u.support.erase (g : G ⧸ K) := by
      intro z hz
      have hz' := Finsupp.mem_support_iff.1 hz
      simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        orbitVec_apply] at hz'
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · rintro rfl
        apply hz'
        simp [MulAction.mem_orbit_self, ← hcdef]
      · refine Finsupp.mem_support_iff.2 fun hzu => hz' ?_
        have hno : z ∉ MulAction.orbit K (g : G ⧸ K) := fun hm =>
          hc0 (by rw [hcdef, ← hu.apply_of_mem_orbit hm, hzu])
        simp [hzu, hno]
    have hcard : (u - c • orbitVec hK g).support.card ≤ n := by
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hy] at this
      omega
    obtain ⟨t, ht, hte⟩ := ih _ hfix hcard
    refine ⟨t + c • heckeOp hK g,
      Submodule.add_mem _ ht (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)), ?_⟩
    have : ((t + c • heckeOp hK g : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) =
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) +
          c • (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) := rfl
    rw [this, hte, heckeOp_delta]
    abel

theorem heckeBasis : ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → ∃ T : G → Hk K, (∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) → (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) ∧ Submodule.span ℂ (Set.range T) = ⊤ ∧ ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0 := by
  intro G _ K hK
  refine ⟨heckeOp hK, ?_, ?_, fun h h0 => eq_zero_of_delta h h0⟩
  · intro g S hS
    have hSe : S = (hK g).toFinset := by
      ext z
      rw [Set.Finite.mem_toFinset, ← hS, Finset.mem_coe]
    have := heckeOp_delta hK g
    rw [orbitVec, ← hSe] at this
    exact this
  · rw [eq_top_iff]
    intro h _
    obtain ⟨t, ht, hte⟩ := exists_mem_span_delta hK _
      ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) (delta_fixed_eval K h) le_rfl
    have : h - t = 0 := eq_zero_of_delta (h - t) (by
      have e : ((h - t : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) =
          (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) -
            (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) := rfl
      rw [e, hte, sub_self])
    rw [sub_eq_zero.1 this]
    exact ht

end GlobalTheory.CompanionTheory.HeckeBasis
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsFibreFamilyLength
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LenFib

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, OneHerm.sigma_sigma hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem hR_self_fixed {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (x : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x x) = hR R σ J x x := by
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    have h := hJ.1 j i
    simp only [JR, Matrix.map_apply, inclR, sigR]
    simp [h]
  unfold hR hform
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, sigR_sigR R hσ, hJR]
  ring

def gramH {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    HermR R σ 1 :=
  ⟨gramR R σ J X, by
    intro a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    exact hR_self_fixed R hσ hJ (X 0)⟩

theorem qR_eq_hermHalf {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = OneHerm.hermHalf R σ (gramH R hσ hJ X) :=
  rfl

theorem hermScal_qR [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    ((hermScal R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0)) : HermR R σ 1) :
      Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = gramR R σ J X := by
  rw [qR_eq_hermHalf R hσ hJ X, OneHerm.hermScal_hermHalf R hσ]
  rfl

theorem qR_of_gram [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E} {c : R}
    (h : gramR R σ J X = ((hermScal R σ c : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = c := by
  have h' : gramH R hσ hJ X = hermScal R σ c := Subtype.ext h
  rw [qR_eq_hermHalf R hσ hJ X, h', OneHerm.hermHalf_hermScal R hσ]

theorem isUnit_det_hermScal (σ : E →ₐ[F] E) {c : R} (hc : IsUnit c) :
    IsUnit ((hermScal R σ c : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det := by
  rw [Matrix.det_fin_one]
  exact hc.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)

theorem isUnit_det_gramR [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E}
    (h : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0))) : IsUnit (gramR R σ J X).det := by
  rw [← hermScal_qR R hσ hJ X]
  exact isUnit_det_hermScal R σ h

theorem continuous_qR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) := by
  obtain ⟨-, -, -, -, -, htr, -, -, -, hgr⟩ := TopK.topTens_props F E σ hσ R
  have h := (hgr 1 M J).matrix_elem 0 0
  exact continuous_const.mul (htr.comp h)

theorem exists_bump [TopologicalSpace R] [LocallyCompactSpace R] [T2Space R]
    (hU : IsOpen {c : R | IsUnit c}) {c₀ : R} (hc₀ : IsUnit c₀) :
    ∃ χ : R → ℝ, Continuous χ ∧ tsupport χ ⊆ {c : R | IsUnit c} ∧ ∀ᶠ c in 𝓝 c₀, χ c = 1 := by
  obtain ⟨K, hK, hcK, hKU⟩ := exists_compact_subset hU hc₀
  obtain ⟨f, hf1, -, hfs, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  refine ⟨f, f.continuous, hfs, ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.mp hcK] with c hc using hf1 hc

end GlobalTheory.CompanionTheory.SW.LenFib


open GlobalTheory.CompanionTheory.SW.LenFib in
theorem GlobalTheory.CompanionTheory.SW.isFibreFamily_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 → μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) X)} = 0 → ∀ m, IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) id Set.univ ν {c | IsUnit c} (fun c => m (hermScal R σ c)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hLoc μ ν _ _ _ hμ0 m hm
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hOE, -⟩ := hLoc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  obtain ⟨hfib, hint, hcont⟩ := hm
  set q : (Fin 1 → Fin M → R ⊗[F] E) → R := fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) with hq
  have hqc : Continuous q := LenFib.continuous_qR R hσ J
  have hUo : IsOpen {c : R | IsUnit c} := by
    have h := hOE.isOpen_range
    have he : Set.range (Units.val : Rˣ → R) = {c : R | IsUnit c} := by
      ext c
      exact Iff.rfl
    rwa [he] at h
  have hemb : MeasurableEmbedding (hermScal R σ) := (OneHerm.hermHomeo R hσ).measurableEmbedding
  have hsub : ∀ X, IsUnit (q X) → IsUnit (gramR R σ J X).det := fun X h =>
    LenFib.isUnit_det_gramR R hσ hJ h
  have hres : μ.restrict {X | IsUnit (gramR R σ J X).det} = μ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    refine measure_mono_null ?_ hμ0
    intro X hX hXq
    exact hX (hsub X hXq)
  have hae : ∀ c, ∀ᵐ X ∂(m (hermScal R σ c)), q X = c := by
    intro c
    refine measure_mono_null ?_ (hfib (hermScal R σ c))
    intro X hX hXm
    exact hX (LenFib.qR_of_gram R hσ hJ hXm.1)
  refine ⟨?_, ?_, ?_⟩
  · intro c
    refine measure_mono_null ?_ (hae c)
    intro X hX hXq
    exact hX ⟨hXq, Set.mem_univ X⟩
  · intro φ hφ
    have h := hint φ hφ
    rw [hres, hemb.lintegral_map] at h
    rw [Measure.restrict_univ, h]
  · intro φ hφc hφs _
    have key : ∀ c₀, IsUnit c₀ → Integrable φ (m (hermScal R σ c₀)) ∧
        ContinuousWithinAt (fun c => ∫ v, φ v ∂(m (hermScal R σ c))) {c | IsUnit c} c₀ := by
      intro c₀ hc₀
      obtain ⟨χ, hχc, hχs, hχ1⟩ := LenFib.exists_bump R hUo hc₀
      have hφ'c : Continuous fun X => φ X * χ (q X) := hφc.mul (hχc.comp hqc)
      have hφ's : HasCompactSupport fun X => φ X * χ (q X) := HasCompactSupport.mul_right hφs
      have hφ't : tsupport (fun X => φ X * χ (q X)) ⊆ {X | IsUnit (gramR R σ J X).det} := by
        intro X hX
        have h1 : X ∈ tsupport (χ ∘ q) := tsupport_mul_subset_right hX
        exact hsub X (hχs (tsupport_comp_subset_preimage χ hqc h1))
      obtain ⟨hI, hC⟩ := hcont _ hφ'c hφ's hφ't
      have heq : ∀ c, χ c = 1 → (fun X => φ X * χ (q X)) =ᵐ[m (hermScal R σ c)] φ := by
        intro c hc
        filter_upwards [hae c] with X hX
        rw [hX, hc, mul_one]
      have hmaps : Set.MapsTo (hermScal R σ) {c : R | IsUnit c}
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} :=
        fun c hc => LenFib.isUnit_det_hermScal R σ hc
      have hC' : ContinuousOn (fun c => ∫ v, φ v * χ (q v) ∂(m (hermScal R σ c))) {c | IsUnit c} :=
        hC.comp (OneHerm.continuous_hermScal R σ).continuousOn hmaps
      refine ⟨(hI _ (hmaps hc₀)).congr (heq c₀ hχ1.self_of_nhds), ?_⟩
      refine (hC' c₀ hc₀).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [mem_nhdsWithin_of_mem_nhds hχ1] with c hc
        exact (integral_congr_ae (heq c hc)).symm
      · exact (integral_congr_ae (heq c₀ hχ1.self_of_nhds)).symm
    exact ⟨fun c hc => (key c hc).1, fun c hc => (key c hc).2⟩
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MovingStatement
section
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.CartanMove

variable {G G' : Type} [Group G] [Group G']

theorem closure_symm_eq (e : G ≃* G') {l : ℕ} (t' : Fin l → G') :
    Submonoid.closure (Set.range fun j => e.symm (t' j)) =
      (Submonoid.closure (Set.range t')).map e.symm.toMonoidHom := by
  rw [MonoidHom.map_mclosure, ← Set.range_comp]
  rfl

theorem apply_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G}
    (hs : s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j))) :
    e s ∈ Submonoid.closure (Set.range t') := by
  rw [closure_symm_eq] at hs
  obtain ⟨x, hx, rfl⟩ := hs
  simpa using hx

theorem symm_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G'}
    (hs : s ∈ Submonoid.closure (Set.range t')) :
    e.symm s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j)) := by
  rw [closure_symm_eq]
  exact ⟨s, hs, rfl⟩

theorem isCartan_comap (e : G ≃* G') {K' : Subgroup G'} {d l : ℕ} (h : IsCartan K' d l) :
    IsCartan (K'.comap e.toMonoidHom) d l := by
  obtain ⟨c', t', h1, h2, h3, h4⟩ := h
  have hmem : ∀ {x : G'}, x ∈ K' → e.symm x ∈ K'.comap e.toMonoidHom := fun {x} hx => by
    simpa [Subgroup.mem_comap] using hx
  refine ⟨fun i => e.symm (c' i), fun j => e.symm (t' j), ?_, ?_, ?_, ?_⟩
  · intro i k
    simpa [Subgroup.mem_comap] using h1 i (e k)
  · intro i j
    exact (h2 i j).map e.symm
  · intro g
    obtain ⟨i, j, s, hs, k, hk, k', hk', hg⟩ := h3 (e g)
    refine ⟨i, j, e.symm s, symm_mem_closure e t' hs, e.symm k, hmem hk, e.symm k', hmem hk', ?_⟩
    apply e.injective
    simpa [map_mul] using hg
  · intro s hs s' hs' k hk
    obtain ⟨a, ha, b, hb, hab⟩ := h4 (e s) (apply_mem_closure e t' hs) (e s')
      (apply_mem_closure e t' hs') (e k) hk
    refine ⟨e.symm a, hmem ha, e.symm b, hmem hb, ?_⟩
    apply e.injective
    simpa [map_mul] using hab

theorem stMove : StMove := by
  intro G G' _ _ _ _ e h U hU
  have hopen : IsOpen ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') := by
    have : ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') = e.toHomeomorph '' (U : Set G) := rfl
    rw [this]
    exact e.toHomeomorph.isOpenMap _ hU
  obtain ⟨K', hK'U, hoK', hcK', d, l, hC⟩ := h _ hopen
  refine ⟨K'.comap e.toMulEquiv.toMonoidHom, ?_, ?_, ?_, d, l, isCartan_comap _ hC⟩
  · intro x hx
    obtain ⟨u, hu, hux⟩ := hK'U hx
    have : u = x := e.toMulEquiv.injective hux
    exact this ▸ hu
  · exact hoK'.preimage e.toHomeomorph.continuous
  · exact e.toHomeomorph.isCompact_preimage.2 hcK'

end GlobalTheory.CompanionTheory.CartanMove
end

