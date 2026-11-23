module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsDomainAway
section
open AlgebraicGeometry

private lemma exists_kill {A : Type*} [CommRing A] [IsNoetherianRing A] (M : Submonoid A)
    (I : Ideal A) (h : ∀ a ∈ I, ∃ m ∈ M, m * a = 0) :
    ∃ s ∈ M, ∀ a ∈ I, s * a = 0 := by
  classical
  obtain ⟨t, rfl⟩ := (IsNoetherian.noetherian I : I.FG)
  induction t using Finset.induction_on with
  | empty => exact ⟨1, M.one_mem, by simp⟩
  | insert x t _ ih =>
    obtain ⟨s, hs, hs'⟩ := ih fun a ha => h a (Ideal.span_mono (by simp) ha)
    obtain ⟨m, hm, hm'⟩ := h x (Ideal.subset_span (by simp))
    refine ⟨m * s, M.mul_mem hm hs, fun a ha => ?_⟩
    rw [Finset.coe_insert, Submodule.mem_span_insert] at ha
    obtain ⟨c, z, hz, rfl⟩ := ha
    have h2 := hs' z hz
    rw [smul_eq_mul]
    linear_combination (s * c) * hm' + m * h2

private lemma isDomain_away {A L B : Type*} [CommRing A] [CommRing L] [IsDomain L]
    [CommRing B] [Algebra A L] [Algebra A B] (M : Submonoid A) [IsLocalization M L]
    (s : A) (hs : s ∈ M) (hk : ∀ a, algebraMap A L a = 0 → s * a = 0)
    [IsLocalization.Away s B] : IsDomain B := by
  have hu : IsUnit (algebraMap A L s) := IsLocalization.map_units L (⟨s, hs⟩ : M)
  let φ : B →+* L := IsLocalization.Away.lift s hu
  have hφ : ∀ a, φ (algebraMap A B a) = algebraMap A L a := fun a =>
    IsLocalization.Away.lift_eq s hu a
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) b
    have h0 : algebraMap A L a = 0 := by
      rw [← hφ, ← hm, map_mul, hb, zero_mul]
    have h1 : algebraMap A B s * algebraMap A B a = 0 := by
      rw [← map_mul, hk a h0, map_zero]
    have hsu : IsUnit (algebraMap A B s) := IsLocalization.Away.algebraMap_isUnit s
    have h2 : algebraMap A B a = 0 := (hsu.mul_right_eq_zero).mp h1
    have hmu : IsUnit (algebraMap A B (m : A)) :=
      IsLocalization.map_units B m
    simp only at hm
    rw [h2] at hm
    exact (hmu.mul_left_eq_zero).mp hm
  exact hinj.isDomain φ

theorem UpperTheory.Reformulated.B.DYde8.main :
    ∀ {X : AlgebraicGeometry.Scheme} {V : X.Opens},
      AlgebraicGeometry.IsAffineOpen V →
        ∀ [IsNoetherianRing (↑(X.presheaf.obj (Opposite.op V)) : Type)],
          ∀ ξ ∈ V,
            ∀ [IsDomain (↑(X.presheaf.stalk ξ) : Type)],
              ∃ (f : (↑(X.presheaf.obj (Opposite.op V)) : Type)),
                ξ ∈ X.basicOpen f ∧ IsDomain (↑(X.presheaf.obj (Opposite.op (X.basicOpen f))) : Type) := by
  intro X V hV _ ξ hξ _
  letI alg : Algebra Γ(X, V) (X.presheaf.stalk ξ) :=
    X.presheaf.algebra_section_stalk (⟨ξ, hξ⟩ : V)
  let P := (hV.primeIdealOf ⟨ξ, hξ⟩).asIdeal
  have hloc : IsLocalization P.primeCompl (X.presheaf.stalk ξ) :=
    hV.isLocalization_stalk ⟨ξ, hξ⟩
  obtain ⟨s, hs, hk⟩ := exists_kill P.primeCompl
    (RingHom.ker (algebraMap Γ(X, V) (X.presheaf.stalk ξ)))
    (fun a ha => by
      obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl (X.presheaf.stalk ξ) a).mp ha
      exact ⟨m, m.2, hm⟩)
  refine ⟨s, ?_, ?_⟩
  · have hu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk ξ) s) :=
      IsLocalization.map_units (X.presheaf.stalk ξ) (⟨s, hs⟩ : P.primeCompl)
    exact (X.mem_basicOpen s ξ hξ).mpr hu
  · have := hV.isLocalization_basicOpen s
    exact isDomain_away (L := X.presheaf.stalk ξ) P.primeCompl s hs (fun a ha => hk a ha)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh26.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F

noncomputable def UpperTheory.Reformulated.B.Qh26.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qh26.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))

theorem UpperTheory.Reformulated.B.Qh26.isInfEmb_unique :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] (τ : E →+* ℂ)
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ _ τ θ θ' h h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ x : F, (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F) x) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] (algebraMap F E x) := by
    intro x
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h1 : (fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h.2 h'.2 ?_
    funext x
    simp only [Function.comp_apply]
    rw [key, h.1, h'.1]
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e =>
    have hs : a ⊗ₜ[F] e = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] e) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hs, map_mul, map_mul, h.1, h'.1, congrFun h1 a]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralDetOfIsIntegral
section
open Polynomial in
private theorem UpperTheory.Reformulated.B.Ybf4.isIntegral_det_of_isIntegral {R E : Type} [CommRing R] [Field E]
    [Algebra R E] {N : ℕ} (γ : Matrix (Fin N) (Fin N) E) (h : IsIntegral R γ) :
    IsIntegral R γ.det := by
  let K := AlgebraicClosure E
  let φ : Matrix (Fin N) (Fin N) E →ₐ[R] Matrix (Fin N) (Fin N) K :=
    (IsScalarTower.toAlgHom R E K).mapMatrix
  have hφ : IsIntegral R (φ γ) := h.map φ
  have hdet : algebraMap E K γ.det = (φ γ).det := RingHom.map_det (algebraMap E K) γ
  rw [← isIntegral_algebraMap_iff (B := K) , hdet,
    Matrix.det_eq_prod_roots_charpoly]
  refine IsIntegral.multiset_prod fun μ hμ => ?_
  have hspec : μ ∈ spectrum K (φ γ) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots hμ)
  obtain ⟨p, hp, hp0⟩ := hφ
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (φ γ) (p.map (algebraMap R K)) ⟨μ, hspec, rfl⟩
  rw [aeval_map_algebraMap, aeval_def, hp0] at h1
  simp only [eval_map] at h1
  by_contra hne
  apply h1
  rw [spectrum.mem_resolventSet_iff, sub_zero]
  exact (IsUnit.mk0 _ hne).map _

open Polynomial in
theorem UpperTheory.Reformulated.B.Ybf4.isIntegral_det :
    ∀ {E : Type} [inst : Field E] [NumberField E] {N : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)),
      L.FG →
        Submodule.span E (↑L : Set (Fin N → E)) = ⊤ →
          ∀ (γ : Matrix (Fin N) (Fin N) E), (∀ v ∈ L, γ.mulVec v ∈ L) → IsIntegral ℤ γ.det := by
  intro E _ _ N L hfg hspan γ hγ
  refine isIntegral_trans (A := NumberField.RingOfIntegers E) _
    (UpperTheory.Reformulated.B.Ybf4.isIntegral_det_of_isIntegral γ ?_)
  haveI : Module.Finite (NumberField.RingOfIntegers E) L := Module.Finite.iff_fg.2 hfg
  let g : (Fin N → E) →ₗ[NumberField.RingOfIntegers E] (Fin N → E) :=
    (Matrix.mulVecLin γ).restrictScalars _
  let f : Module.End (NumberField.RingOfIntegers E) L := g.restrict (p := L) (q := L) hγ
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (NumberField.RingOfIntegers E) f
  refine ⟨p, hp, ?_⟩
  have hpow : ∀ (n : ℕ) (v : L), ((f ^ n) v : Fin N → E) = (γ ^ n).mulVec v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ, Module.End.mul_apply, ih, ← Matrix.mulVec_mulVec]
      rfl
  have key : ∀ (q : (NumberField.RingOfIntegers E)[X]) (v : L),
      ((aeval f q) v : Fin N → E) = (aeval γ q).mulVec v := by
    intro q v
    induction q using Polynomial.induction_on' with
    | add a b ha hb => simp [ha, hb, Matrix.add_mulVec]
    | monomial n a =>
      rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
        LinearMap.smul_apply, Submodule.coe_smul, hpow]
      ext i
      change a • (∑ j, (γ ^ n) i j * (v : Fin N → E) j) = ∑ j, (a • (γ ^ n) i j) * (v : Fin N → E) j
      simp only [Algebra.smul_def, mul_assoc, Finset.mul_sum]
  have hz : Matrix.mulVecLin (aeval γ p) = 0 := by
    refine LinearMap.ext_on hspan fun v hv => ?_
    have := key p ⟨v, hv⟩
    rw [hp0] at this
    simpa using this.symm
  rw [← aeval_def]
  apply Matrix.toLin'.injective
  rw [map_zero]
  exact hz
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralOfNormLeOne
section
theorem UpperTheory.padicAlgCl_isIntegral_of_norm_le_one :
    ∀ {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l), ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x := by
  intro l _ x hx
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hint
  have hs : spectralValue (minpoly ℚ_[l] x) ≤ 1 := hx
  have hc : ∀ n : ℕ, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hs
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq]
  exact minpoly.aeval _ _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsLCProd
section
theorem UpperTheory.Reformulated.B.Qf48.isLC_prod {X : Type*} {ι : Type*} [TopologicalSpace X] (T : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ T, IsLocallyConstant (f i)) : IsLocallyConstant fun x ↦ ∏ i ∈ T, f i x := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenRightInvariance
section
theorem UpperTheory.isOpen_right_invariance :
    ∀ {H F G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group F] [TopologicalSpace F] [Group G]
        (ι : H →* F) (f : F →* G) (U : Subgroup F) (φ : G → ℂ), Continuous ι → IsOpen (U : Set F) →
        (∀ u ∈ U, ∀ g, φ (g * f u) = φ g) → IsOpen {h : H | (fun x => φ (x * f (ι h))) = φ} := by
  intro H F G _ _ _ _ _ _ ι f U φ hι hU hφ
  let S : Subgroup H :=
    { carrier := {h : H | (fun x => φ (x * f (ι h))) = φ}
      one_mem' := by
        funext x
        simp
      mul_mem' := by
        intro a b ha hb
        funext x
        have h1 : φ (x * f (ι a) * f (ι b)) = φ (x * f (ι a)) := congrFun hb (x * f (ι a))
        have h2 : φ (x * f (ι a)) = φ x := congrFun ha x
        rw [map_mul, map_mul, ← mul_assoc, h1, h2]
      inv_mem' := by
        intro a ha
        funext x
        have h1 : φ (x * f (ι a⁻¹) * f (ι a)) = φ (x * f (ι a⁻¹)) := congrFun ha (x * f (ι a⁻¹))
        rw [← h1]
        simp }
  have hle : U.comap ι ≤ S := by
    intro h hh
    funext x
    exact hφ (ι h) hh x
  have hopen : IsOpen ((U.comap ι : Subgroup H) : Set H) := hU.preimage hι
  exact Subgroup.isOpen_mono hle hopen
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenStabilizer
section
theorem UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by
  intro G _ _ _ V _ _ ρ v h
  let H : Subgroup G :=
    { carrier := {g : G | ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        have ha' : ρ a v = v := ha
        have hb' : ρ b v = v := hb
        change ρ (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb', ha']
      inv_mem' := by
        intro a ha
        have ha' : ρ a v = v := ha
        change ρ a⁻¹ v = v
        calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha']
          _ = ρ (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
          _ = v := by simp }
  exact H.isOpen_of_mem_nhds (g := 1) h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenStabilizerAddSmul
section
theorem UpperTheory.isOpen_stabilizer_add_smul :
    ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V) (a b : V) (z : ℂ),
        IsOpen {g : G | ρ g a = a} → IsOpen {g : G | ρ g b = b} → IsOpen {g : G | ρ g (a + z • b) = a + z • b} := by
  intro G V _ _ _ _ _ ρ a b z ha hb
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hg' : ρ g (a + z • b) = a + z • b := hg
  have hc : Continuous fun x : G => g⁻¹ * x := continuous_const.mul continuous_id
  have hU : IsOpen ((fun x : G => g⁻¹ * x) ⁻¹' ({g : G | ρ g a = a} ∩ {g : G | ρ g b = b})) :=
    (ha.inter hb).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · simp
  · intro x hx
    have h1 : ρ (g⁻¹ * x) a = a := hx.1
    have h2 : ρ (g⁻¹ * x) b = b := hx.2
    have h3 : ρ (g⁻¹ * x) (a + z • b) = a + z • b := by
      rw [map_add (f := _), map_smul, h1, h2]
    have h4 : x = g * (g⁻¹ * x) := by group
    show ρ x (a + z • b) = a + z • b
    rw [h4, map_mul, Module.End.mul_apply, h3, hg']
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenStabilizerLinearMap
section
theorem UpperTheory.isOpen_stabilizer_linear_map :
    ∀ {G V M : Type} [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup M] [Module ℂ M] (R : G → M →ₗ[ℂ] M) (f : V →ₗ[ℂ] M), (∀ v : V, IsOpen {g : G | R g (f v) = f v}) → IsOpen {g : G | R g ∘ₗ f = f} := by
  intro G V M _ _ _ _ _ _ R f h
  let b := Module.finBasis ℂ V
  have key : {g : G | R g ∘ₗ f = f} = ⋂ i, {g : G | R g (f (b i)) = f (b i)} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hg i
      exact LinearMap.congr_fun hg (b i)
    · intro hg
      exact b.ext fun i => hg i
  rw [key]
  exact isOpen_iInter_of_finite fun i => h (b i)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenValuationLtOne
section
open ValuativeRel

private lemma UpperTheory.isOpen_of_add_small {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] (s : Set k)
    (hs : ∀ x ∈ s, ∀ z, valuation k z < 1 → x + z ∈ s) : IsOpen s := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨1, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hs x hx z (by simpa using hz)

private lemma UpperTheory.isOpen_valuation_le_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsOpen {x : k | valuation k x ≤ 1} :=
  UpperTheory.isOpen_of_add_small _ fun _ hx _ hz => (valuation k).map_add_le hx hz.le

private lemma UpperTheory.isOpen_setOf_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsOpen {x : k | valuation k x < 1} :=
  UpperTheory.isOpen_of_add_small _ fun _ hx _ hz => (valuation k).map_add_lt hx hz

private lemma UpperTheory.isClosed_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsValuativeTopology k] : IsClosed {x : k | valuation k x < 1} := by
  rw [← isOpen_compl_iff]
  refine UpperTheory.isOpen_of_add_small _ fun x hx z hz h => hx ?_
  have h' : valuation k (x + z - z) < 1 := (valuation k).map_sub_lt h hz
  simpa using h'

theorem UpperTheory.iwahori_subgroup_open :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
        (S : Set (Matrix.GeneralLinearGroup (Fin n) k)),
        (∀ g : Matrix.GeneralLinearGroup (Fin n) k, g ∈ S ↔
          (∀ i j, ValuativeRel.valuation k (g.val i j) ≤ 1) ∧ (∀ i j, ValuativeRel.valuation k ((g⁻¹).val i j) ≤ 1) ∧
            ∀ i j, j < i → ValuativeRel.valuation k (g.val i j) < 1) →
        IsOpen S ∧ IsCompact S := by
  intro k _ _ _ _ n S hS
  have c1 : ∀ i j, Continuous fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have c2 : ∀ i j, Continuous fun g : Matrix.GeneralLinearGroup (Fin n) k => (g⁻¹).val i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  constructor
  · have e : S = (⋂ i, ⋂ j, (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x ≤ 1}) ∩
        ((⋂ i, ⋂ j, (fun g : Matrix.GeneralLinearGroup (Fin n) k => (g⁻¹).val i j) ⁻¹'
          {x : k | valuation k x ≤ 1}) ∩
        ⋂ i, ⋂ j, ⋂ (_ : j < i), (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x < 1}) := by
      ext g
      rw [hS]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (UpperTheory.isOpen_valuation_le_one k).preimage (c1 i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        (UpperTheory.isOpen_valuation_le_one k).preimage (c2 i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun _ => (UpperTheory.isOpen_setOf_valuation_lt_one k).preimage (c1 i j)
  · let M : Set (Matrix (Fin n) (Fin n) k) :=
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : k | valuation k x ≤ 1}
    have hM : IsCompact M := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      IsNonarchimedeanLocalField.isCompact_closedBall k 1
    have hP : IsCompact (M ×ˢ (MulOpposite.op '' M)) :=
      hM.prod (hM.image MulOpposite.continuous_op)
    have hK := (Units.isClosedEmbedding_embedProduct
      (α := Matrix (Fin n) (Fin n) k)).isCompact_preimage hP
    have hC : IsClosed (⋂ i, ⋂ j, ⋂ (_ : j < i),
        (fun g : Matrix.GeneralLinearGroup (Fin n) k => g.val i j) ⁻¹'
          {x : k | valuation k x < 1}) :=
      isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
        (UpperTheory.isClosed_valuation_lt_one k).preimage (c1 i j)
    convert hK.inter_right hC using 1
    ext g
    rw [hS]
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_prod]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun i _ j _ => h1 i j, (g⁻¹).val, fun i _ j _ => h2 i j, rfl⟩, h3⟩
    · rintro ⟨⟨h1, m, hm, hme⟩, h3⟩
      have hm' : m = (g⁻¹).val := MulOpposite.op_injective hme
      subst hm'
      exact ⟨fun i j => h1 i trivial j trivial, fun i j => hm i trivial j trivial, h3⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPrecompleteFiniteModule
section
private theorem UpperTheory.Reformulated.B.Qk17.pi_precomplete {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → Type*) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] [∀ i, IsPrecomplete I (N i)] : IsPrecomplete I (∀ i, N i) := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  choose r hr using fun j : ι =>
    AdicCompletion.of_surjective I (N j) (AdicCompletion.pi I N y j)
  refine ⟨r, (AdicCompletion.piEquivOfFintype I N).injective ?_⟩
  rw [AdicCompletion.piEquivOfFintype_apply, AdicCompletion.piEquivOfFintype_apply]
  funext j
  rw [← hr j]
  exact AdicCompletion.map_of I (LinearMap.proj (R := R) (φ := N) j) r

theorem UpperTheory.Reformulated.B.Qk17.isPrecomplete_finite_module.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) [IsAdicComplete I R] (M : Type u_2)
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] [Module.Finite R M], IsPrecomplete I M := by
  intro R _ I _ M _ _ _
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have := UpperTheory.Reformulated.B.Qk17.pi_precomplete I (fun _ : Fin n => R)
  rw [← AdicCompletion.of_surjective_iff]
  intro x
  obtain ⟨y, rfl⟩ := AdicCompletion.map_surjective I hf x
  obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I (Fin n → R) y
  exact ⟨f r, (AdicCompletion.map_of I f r).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Killed
section
theorem UpperTheory.Reformulated.B.Qe12.killed :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (M : Type)
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module ℤ_[l] M] [Finite M],
    ∃ (r : ℕ), (0 : ℕ) < r ∧ ∀ (x : M), (↑l : ℤ_[l]) ^ r • x = (0 : M) := by
  intro l _ M _ _ _
  have hN : ((Nat.card M : ℕ) : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨((Nat.card M : ℕ) : ℤ_[l]).valuation + 1, Nat.succ_pos _, fun x => ?_⟩
  have h1 : ((Nat.card M : ℕ) : ℤ_[l]) • x = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact card_nsmul_eq_zero'
  have h2 : ((PadicInt.unitCoeff hN : ℤ_[l]ˣ) : ℤ_[l]) •
      ((l : ℤ_[l]) ^ ((Nat.card M : ℕ) : ℤ_[l]).valuation • x) = 0 := by
    rw [← mul_smul, ← PadicInt.unitCoeff_spec hN]
    exact h1
  have h3 : (l : ℤ_[l]) ^ ((Nat.card M : ℕ) : ℤ_[l]).valuation • x = 0 :=
    ((PadicInt.unitCoeff hN).isUnit.smul_eq_zero).mp h2
  rw [pow_succ', mul_smul, h3, smul_zero]
end

