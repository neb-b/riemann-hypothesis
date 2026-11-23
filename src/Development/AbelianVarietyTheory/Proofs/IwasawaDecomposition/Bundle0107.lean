module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AutCongrContinuousCycInertia

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstFaithful

theorem exists_idem {LL U D R : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D]
    (m : U →+* End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F)
    [CommRing R] [IsSemisimpleRing R] (α : R →+* End LL D) (π : R →+* F) (iL : LL → R) (iU : U → R)
    (h1 : ∀ a, α (iL a) = algebraMap LL (End LL D) a) (h2 : ∀ c, α (iU c) = m c)
    (h3 : ∀ a, π (iL a) = algebraMap LL F a) (h4 : ∀ c, π (iU c) = τ c) :
    ∃ e : R, π e = 1 ∧ ∀ x, letterMk m F τ x = 0 → α e x = 0 := by
  let : Algebra R F := π.toAlgebra
  obtain ⟨q, hq⟩ := exists_isCompl (RingHom.ker π)
  have h1q : (1 : R) ∈ RingHom.ker π ⊔ q := by rw [hq.sup_eq_top]; trivial
  obtain ⟨a, ha, e, he, hae⟩ := Submodule.mem_sup.1 h1q
  have hπe : π e = 1 := by
    have := congrArg π hae
    rwa [map_add, RingHom.mem_ker.1 ha, zero_add, map_one] at this
  have hinj : Function.Injective ((Algebra.linearMap R F) ∘ₗ q.subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have : (y : R) ∈ RingHom.ker π ⊓ q := ⟨hy, y.2⟩
    rw [hq.inf_eq_bot] at this
    exact Subtype.ext this
  obtain ⟨Λ, hΛ⟩ := IsSemisimpleModule.extension_property _ hinj q.subtype
  have hΛ1 : Λ 1 = e := by
    rw [← hπe]; exact LinearMap.congr_fun hΛ ⟨e, he⟩
  have hΛm : ∀ r f, Λ (π r * f) = r * Λ f := fun r f => Λ.map_smul r f
  let β : F →ₗ[LL] End LL D :=
    { toFun := fun f => α (Λ f)
      map_add' := fun f g => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun a f => by
        rw [Algebra.smul_def, ← h3, hΛm, map_mul, h1, ← Algebra.smul_def]; rfl }
  have hβ : ∀ f x, TensorProduct.lift β (f ⊗ₜ x) = α (Λ f) x := fun _ _ => rfl
  have hker : ∀ y ∈ letterKer m F τ, TensorProduct.lift β y = 0 := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => TensorProduct.lift β y = 0) hy ?_ ?_ ?_
    · rintro c _ ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        rw [LinearMap.sub_apply, map_sub, LinearMap.baseChange_tmul, LinearMap.smul_apply,
          LinearMap.id_apply, smul_tmul', hβ, hβ, smul_eq_mul, ← h4, hΛm, mul_comm, map_mul, h2,
          End.mul_apply, sub_self]
      | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, add_zero]
    · exact map_zero _
    · intro y z hy hz
      rw [map_add (f := _), hy, hz, add_zero]
  refine ⟨e, hπe, fun x hx => ?_⟩
  rw [letterMk, ← LinearMap.mem_ker, ker_letterQ] at hx
  rw [← hΛ1, ← hβ]
  exact hker _ hx

variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)

theorem exists_level_tensor (r : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧
    ∀ f : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l), (∀ c : ↥(MaximalUnramifiedExtension l), c ^ m = 1 → f c = c) →
      Algebra.TensorProduct.map f (AlgHom.id ℚ_[l] ↥LL.1) r = r := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, hl.out.not_dvd_one, fun f _ => map_zero _⟩
  | tmul c a =>
    obtain ⟨m, hm, hlm, H⟩ := MemLoc.FrobLaws.exists_level c.2
    refine ⟨m, hm, hlm, fun f hf => ?_⟩
    obtain ⟨g, hg⟩ := MemLoc.FrobLaws.exists_ext f
    have h := H g 1 fun ζ hζ => by
      let z : ↥(MaximalUnramifiedExtension l) := ⟨ζ, IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩⟩
      exact (hg z).trans (congrArg Subtype.val (hf z (Subtype.ext hζ)))
    have h' : f c = c := Subtype.ext ((hg c).symm.trans h)
    rw [Algebra.TensorProduct.map_tmul, h', AlgHom.id_apply]
  | add x y hx hy =>
    obtain ⟨m, hm, hlm, ha⟩ := hx
    obtain ⟨n, hn, hln, hb⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, fun hd => ((hl.out.dvd_mul).1 hd).elim hlm hln, fun f H => ?_⟩
    rw [map_add (f := _), ha f fun ζ hζ => H ζ (by rw [pow_mul, hζ, one_pow]),
      hb f fun ζ hζ => H ζ (by rw [mul_comm, pow_mul, hζ, one_pow])]

theorem exists_algHom_ker (U R Ω : Type) [Field U] [CommRing R] [Algebra U R] [Module.Finite U R] [Field Ω]
    [IsAlgClosed Ω] [Algebra U Ω] (I : Ideal R) (hI : I ≠ ⊤) : ∃ ψ : R →ₐ[U] Ω, ∀ r ∈ I, ψ r = 0 := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  let := Ideal.Quotient.field M
  let ψ₀ : (R ⧸ M) →ₐ[U] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ₀.comp (Ideal.Quotient.mkₐ _ M), fun r hr => ?_⟩
  have : Ideal.Quotient.mkₐ U M r = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hIM hr)
  rw [AlgHom.comp_apply, this, map_zero]

theorem exists_restrict (g : GQ l) : ∃ t : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l), ∀ c, (t c : Om l) = g c := by
  have hle : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  exact ⟨((g : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict
    (MaximalUnramifiedExtension l).toSubalgebra (fun x => hle ⟨x, x.2, rfl⟩), fun _ => rfl⟩

theorem exists_extend (f : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ∃ g : GQ l, ∀ a : ↥LL.1, g a = f a :=
  ⟨AlgEquiv.ofBijective (f.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _),
    fun a => f.liftNormal_commutes (Om l) a⟩

theorem exists_translate (I : Ideal (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1)) (hI : I ≠ ⊤)
    (e : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) (he : Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val e ≠ 0) :
    ∃ (n : ℕ) (r : ↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1), r ∉ I ∧
      Algebra.TensorProduct.map (frobUr l ^ n) (AlgHom.id ℚ_[l] ↥LL.1) r = e := by
  have := LL.2
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker ↥(MaximalUnramifiedExtension l) _ (Om l) I hI
  obtain ⟨g, hg'⟩ := exists_extend LL
    ((ψ.restrictScalars ℚ_[l]).comp Algebra.TensorProduct.includeRight)
  have hg : ∀ a : ↥LL.1, g a = ψ (1 ⊗ₜ a) := hg'
  obtain ⟨t, ht⟩ := exists_restrict g
  have key : ∀ r, ψ (Algebra.TensorProduct.map t (AlgHom.id ℚ_[l] ↥LL.1) r) =
      g (Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val r) := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c a =>
      have e1 : t c ⊗ₜ[ℚ_[l]] a = t c • ((1 : ↥(MaximalUnramifiedExtension l)) ⊗ₜ[ℚ_[l]] a) := by
        rw [smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, e1, map_smul, ← hg,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      exact congrArg (· * g a) (ht c)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨m, hm, hlm, H⟩ := exists_level_tensor LL e
  obtain ⟨n, hn⟩ := MemLoc.FrobLaws.gal_root g⁻¹ hm hlm
  refine ⟨n, Algebra.TensorProduct.map t (AlgHom.id ℚ_[l] ↥LL.1) e, fun h => he ?_, ?_⟩
  · have h0 := hψ _ h
    rw [key] at h0
    exact g.injective (h0.trans (map_zero g).symm)
  · rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.id_comp]
    refine H _ fun c hc => ?_
    have hc' : t c ^ m = 1 := by rw [← map_pow, hc, map_one]
    rw [AlgHom.comp_apply, frobUr_pow_root n _ m hm hlm hc', ← map_pow]
    apply Subtype.ext
    rw [ht]
    have := hn c (congrArg Subtype.val hc)
    rw [SubmonoidClass.coe_pow, ← this, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem exists_action {k L U D : Type} [Field k] [Field L] [Field U] [Algebra k L] [Algebra k U]
    [AddCommGroup D] [Module L D] (m : U →+* End L D)
    (hm : ∀ c : k, m (algebraMap k U c) = algebraMap L _ (algebraMap k L c)) :
    ∃ α : U ⊗[k] L →+* End L D, ∀ c a, α (c ⊗ₜ a) = m c * algebraMap L _ a := by
  let : Module k D := Module.compHom D (algebraMap k L)
  have : IsScalarTower k L D := .of_algebraMap_smul fun _ _ => rfl
  let mU : U →ₐ[k] End L D := { m with commutes' := hm }
  exact ⟨(Algebra.TensorProduct.lift mU (IsScalarTower.toAlgHom k L (End L D))
    fun c a => (Algebra.commutes a (m c)).symm).toRingHom, fun _ _ => rfl⟩

theorem eq_zero_of_translate {k L U D : Type} [Field k] [Field L] [Field U] [Algebra k L] [Algebra k U]
    [AddCommGroup D] [Module L D] {m : U →+* End L D} (α : U ⊗[k] L →+* End L D)
    (hα : ∀ c a, α (c ⊗ₜ a) = m c * algebraMap L _ a) (σ : ℕ → U →ₐ[k] U) (φ : ℕ → End L D)
    (hinj : ∀ n, Function.Injective (φ n)) (hφ : ∀ n c, φ n * m c = m (σ n c) * φ n) (e : U ⊗[k] L) (x : D)
    (hx : ∀ n, α e (φ n x) = 0)
    (he : ∀ I : Ideal (U ⊗[k] L), I ≠ ⊤ →
      ∃ n r, r ∉ I ∧ Algebra.TensorProduct.map (σ n) (AlgHom.id k L) r = e) : x = 0 := by
  let I : Ideal (U ⊗[k] L) :=
    { carrier := {r | α r x = 0}
      add_mem' := fun {a b} (ha : α a x = 0) (hb : α b x = 0) => show α (a + b) x = 0 by
        rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
      zero_mem' := show α 0 x = 0 by rw [map_zero, LinearMap.zero_apply]
      smul_mem' := fun a b (hb : α b x = 0) => show α (a * b) x = 0 by
        rw [map_mul, End.mul_apply, hb, map_zero] }
  by_contra h0
  have hI : I ≠ ⊤ := fun h => h0 (by
    have : α 1 x = 0 := (Ideal.eq_top_iff_one I).1 h
    rwa [map_one] at this)
  obtain ⟨n, r, hr, hre⟩ := he I hI
  have semi : ∀ s, φ n * α s = α (Algebra.TensorProduct.map (σ n) (AlgHom.id k L) s) * φ n := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hα, hα, ← mul_assoc, hφ, mul_assoc,
        mul_assoc, Algebra.commutes]
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), mul_add, add_mul, hy, hz]
  refine hr (?_ : α r x = 0)
  have h1 := LinearMap.congr_fun (semi r) x
  rw [End.mul_apply, End.mul_apply, hre] at h1
  exact hinj n (h1.trans ((hx n).trans (map_zero _).symm))

theorem isSemisimpleRing_tensor : IsSemisimpleRing (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) := by
  have := LL.2
  have : Algebra.FormallyUnramified ℚ_[l] ↥LL.1 := Algebra.FormallyUnramified.of_isSeparable _ _
  have : IsReduced (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) :=
    Algebra.FormallyUnramified.isReduced_of_field ↥(MaximalUnramifiedExtension l) _
  have : IsArtinianRing (↥(MaximalUnramifiedExtension l) ⊗[ℚ_[l]] ↥LL.1) := IsArtinianRing.of_finite ↥(MaximalUnramifiedExtension l) _
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem eq_zero_of_wdMk_phiD_pow (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) (K LL : FinExt l)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V) (x : ↥(Dpst P ρ))
    (hx : ∀ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x) = 0) : x = 0 := by
  have := isSemisimpleRing_tensor LL
  obtain ⟨α, hα⟩ := exists_action (k := ℚ_[l]) (mulD P ρ) fun c =>
    LinearMap.ext fun y => Subtype.ext (by
      have : mulV P ↥LL.1 V (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) =
          algebraMap ↥LL.1 _ (algebraMap ℚ_[l] ↥LL.1 c) :=
        end_ext P fun v b => by
          rw [mulV_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul,
            Module.algebraMap_end_apply, algebraMap_smul]
      exact LinearMap.congr_fun this y.1)
  let π₀ := Algebra.TensorProduct.productMap (MaximalUnramifiedExtension l).val LL.1.val
  have hπ₀ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (a : ↥LL.1), π₀ (c ⊗ₜ a) = (c : Om l) * a := fun _ _ => rfl
  let := algC ι LL
  obtain ⟨e, he, hk⟩ := exists_idem (mulD P ρ) ℂ (urC ι) α (ι.toRingHom.comp π₀.toRingHom)
    (fun a => 1 ⊗ₜ a) (fun c => c ⊗ₜ 1) (fun a => (hα 1 a).trans (by rw [map_one, one_mul]))
    (fun c => (hα c 1).trans (by rw [map_one, mul_one]))
    (fun a => congrArg ι ((hπ₀ 1 a).trans (one_mul (a : Om l))))
    (fun c => congrArg ι ((hπ₀ c 1).trans (mul_one (c : Om l))))
  have he0 : π₀ e ≠ 0 := fun h => by
    have h' : ι (π₀ e) = 1 := he
    rw [h, map_zero] at h'
    exact zero_ne_one h'
  refine eq_zero_of_translate α hα (fun n => frobUr l ^ n) (fun n => phiD P ρ ^ n) (fun n => ?_)
    (phiD_pow_mulD P ρ) e x (fun n => hk _ (hx n)) fun I hI => exists_translate LL I hI e he0
  rw [End.coe_pow]
  exact (phiD_injective P ρ).iterate n

end GlobalTheory.PstFaithful
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexLinearExtensionOfTraceIsometry
section
open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

namespace GlobalTheory

theorem exists_complexLinear_extension_of_traceIsometry : ∀ (K E : Type) [Field K] [Field E] [Algebra K E] (cj : E → E) (ι : Type) [Fintype ι] (φ : E →+* ℂ) (emb : ι → E →+* ℂ), (∀ y, φ (cj y) = starRingEnd ℂ (φ y)) → (∀ τ y, emb τ (cj y) = starRingEnd ℂ (emb τ y)) → (∀ τ (x : K), emb τ (algebraMap K E x) = φ (algebraMap K E x)) → (∀ y, ∑ τ, emb τ y = φ (algebraMap K E (Algebra.trace K E y))) → ∀ γ : IsoKG K E cj ι, ∃ gC : (Fin 4 × ι → ℂ) ≃ₗ[ℂ] (Fin 4 × ι → ℂ), ∀ x : Fin 4 → E, gC (fun w => emb w.2 (x w.1)) = fun w => φ (algebraMap K E (γ.g x w)) := by
  intro K E _ _ _ cj ι _ φ emb hφ hemb hK htr γ
  classical
  let b : Fin 4 × ι → Fin 4 → E := fun w => γ.g.symm (Pi.single w 1)
  let B : Matrix (Fin 4 × ι) (Fin 4 × ι) ℂ := fun v w => emb v.2 (b w v.1)
  have hB : Bᴴ * B = 1 := by
    ext w' w
    have h := congrArg φ (γ.isom (b w) (b w'))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [b, LinearEquiv.apply_symm_apply, map_sum, map_mul, hφ, ← htr, hemb] at h
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have h2 : ∑ a, ∑ τ, Bᴴ w' (a, τ) * B (a, τ) w
        = ∑ a, ∑ τ, emb τ (b w a) * starRingEnd ℂ (emb τ (b w' a)) := by
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun τ _ => ?_
      rw [Matrix.conjTranspose_apply, mul_comm]
      rfl
    rw [h2, ← h, Finset.sum_eq_single w]
    · by_cases hw : w' = w
      · subst hw; simp
      · simp [Matrix.one_apply_ne hw, Pi.single_eq_of_ne (Ne.symm hw)]
    · intro u _ hu
      simp [Pi.single_eq_of_ne hu]
    · simp
  have hB' : B * Bᴴ = 1 := mul_eq_one_comm.mp hB
  refine ⟨Matrix.toLin'OfInv hB' hB, fun x => ?_⟩
  have hx : x = ∑ w, γ.g x w • b w := by
    apply γ.g.injective
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [b, map_sum, map_smul, LinearEquiv.apply_symm_apply]
    ext u
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : (fun w : Fin 4 × ι => emb w.2 (x w.1))
      = B *ᵥ (fun w => φ (algebraMap K E (γ.g x w))) := by
    ext v
    have := congrArg (fun y => emb v.2 (y v.1)) hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, map_sum, map_mul, hK] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct, B, mul_comm, hK]
  rw [hv]
  change Bᴴ *ᵥ (B *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalGaloisDataShaLengthEq
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace GlobalTheory.ShaTransport

section General

variable {R : Type*} [CommRing R] {G G' : Type*} [Group G] [TopologicalSpace G] [Group G']
  [TopologicalSpace G'] {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem pairH1_id_bijective (rho : Representation R G M) (rho' : Representation R G' M)
    (e : G' →* G) (he : Continuous e) (e' : G →* G') (he' : Continuous e')
    (h1 : ∀ g, e (e' g) = g) (h2 : ∀ g, e' (e g) = g)
    (hc : ∀ g m, (LinearMap.id : M →ₗ[R] M) (rho (e g) m) = rho' g ((LinearMap.id : M →ₗ[R] M) m)) :
    Function.Bijective (pairH1DecompositionMap rho rho' e he LinearMap.id continuous_id hc) := by
  have hc' : ∀ g m, (LinearMap.id : M →ₗ[R] M) (rho' (e' g) m) = rho g ((LinearMap.id : M →ₗ[R] M) m) := by
    intro g m
    have := hc (e' g) m
    simp only [LinearMap.id_apply, h1] at this ⊢
    exact this.symm
  refine Function.bijective_iff_has_inverse.2
    ⟨pairH1DecompositionMap rho' rho e' he' LinearMap.id continuous_id hc', fun x => ?_, fun x => ?_⟩
  · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (funext fun g => by simp [compatiblePairCocycles1, h1])
  · obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext (funext fun g => by simp [compatiblePairCocycles1, h2])

end General

section Field

variable {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω']

theorem autCongr_mem_Dec (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω} {A₁ : ValuationSubring Ω'}
    (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) {g : G F Ω} (hg : g ∈ Dec (F := F) A) :
    (AlgEquiv.autCongr σ g : G F Ω') ∈ Dec (F := F) A₁ := by
  rw [mem_Dec]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  obtain ⟨z, rfl⟩ := σ.surjective y
  have : (AlgEquiv.autCongr σ g)⁻¹ • σ z = σ ((g⁻¹ : G F Ω) z) := by
    rw [← map_inv]
    show σ ((g⁻¹ : G F Ω) (σ.symm (σ z))) = _
    rw [σ.symm_apply_apply]
  rw [this, hA, hA]
  exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A).inv_mem hg) z

theorem isPlaceOver_transport (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω}
    {A₁ : ValuationSubring Ω'} (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) {v : HeightOneSpectrum (𝓞 F)}
    (h : IsPlaceOver A v) : IsPlaceOver A₁ v := by
  intro x
  rw [← h x, valuation_lt_one_iff', valuation_lt_one_iff', ← σ.commutes, hA, ← map_inv₀, hA,
    map_eq_zero_iff _ σ.injective]

theorem NS_le_comap (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S ≤ (NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom := by
  have hcont := GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω Ω' σ
  have hN : ((NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom).Normal :=
    Subgroup.Normal.comap inferInstance _
  have hcl : IsClosed (((NS Ω' S).comap (AlgEquiv.autCongr σ).toMonoidHom : Subgroup (G F Ω)) :
      Set (G F Ω)) := (isClosed_NS Ω' S).preimage hcont.1
  unfold NS
  apply Subgroup.topologicalClosure_minimal _ _ hcl
  apply Subgroup.normalClosure_le_normal
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨v, hv, A, hA, hg⟩ := hg
  show AlgEquiv.autCongr σ g ∈ NS Ω' S
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  have hA₁ : ∀ y, σ y ∈ A.comap (σ.symm : Ω' →+* Ω) ↔ y ∈ A := fun y => by
    rw [ValuationSubring.mem_comap]
    simp
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A.comap (σ.symm : Ω' →+* Ω), isPlaceOver_transport σ hA₁ hA,
    hcont.2.2 A _ hA₁ g hg⟩

def gsMap (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) : GS Ω' S →* GS Ω S :=
  QuotientGroup.map (NS Ω' S) (NS Ω S) (AlgEquiv.autCongr σ.symm).toMonoidHom (NS_le_comap σ.symm S)

theorem gsMap_mk (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) (g : G F Ω') :
    gsMap σ S (toGS Ω' S g) = toGS Ω S (AlgEquiv.autCongr σ.symm g) := rfl

theorem continuous_gsMap (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) :
    Continuous (gsMap σ S) :=
  (QuotientGroup.isQuotientMap_mk (NS Ω' S)).continuous_iff.2
    ((continuous_toGS Ω S).comp (GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω' Ω σ.symm).1)

theorem gsMap_gsMap_symm (σ : Ω ≃ₐ[F] Ω') (S : Set (HeightOneSpectrum (𝓞 F))) (x : GS Ω S) :
    gsMap σ S (gsMap σ.symm S x) = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  show toGS Ω S (AlgEquiv.autCongr σ.symm (AlgEquiv.autCongr σ.symm.symm g)) = toGS Ω S g
  congr 1
  ext y
  simp [AlgEquiv.autCongr_apply]

def transport {l : ℕ} [Fact l.Prime] (σ : Ω ≃ₐ[F] Ω') (D : LData F Ω l) : LData F Ω' l where
  S := D.S
  hS := D.hS
  A v := (D.A v).comap (σ.symm : Ω' →+* Ω)
  hA v := isPlaceOver_transport σ (fun y => by rw [ValuationSubring.mem_comap]; simp) (D.hA v)
  chi := D.chi.comp (gsMap σ _)
  hchi := by
    ext g
    have h1 := congrArg (fun f => ((f (AlgEquiv.autCongr σ.symm g) : ℤ_[l]ˣ) : ℤ_[l])) D.hchi
    have h2 := (GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω' Ω σ.symm).2.1 l g
    simp only [MonoidHom.comp_apply] at h1
    simp only [MonoidHom.comp_apply, gsMap_mk]
    rw [h1, h2]

end Field

section Sha

variable {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω'] {l : ℕ} [Fact l.Prime]

def decMap (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω} {A₁ : ValuationSubring Ω'}
    (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) : Dec (F := F) A →* Dec (F := F) A₁ :=
  ((AlgEquiv.autCongr σ).toMonoidHom.comp (Dec (F := F) A).subtype).codRestrict _
    (fun g => autCongr_mem_Dec σ hA g.2)

theorem continuous_decMap (σ : Ω ≃ₐ[F] Ω') {A : ValuationSubring Ω} {A₁ : ValuationSubring Ω'}
    (hA : ∀ y, σ y ∈ A₁ ↔ y ∈ A) : Continuous (decMap σ hA) :=
  Continuous.subtype_mk ((GlobalTheory.ConsCompare.autCongr_continuous_cyc_inertia F Ω Ω' σ).1.comp
    continuous_subtype_val) _

theorem shaLen_transport (σ : Ω ≃ₐ[F] Ω') (D : LData F Ω l) (e : ℤ) :
    shaLen (transport σ D) e = shaLen D e := by
  have hc : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D e (gsMap σ _ g) m) =
      qzTw (transport σ D) e g ((LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) m) := fun _ _ => rfl
  have hΦ := pairH1_id_bijective (qzTw D e) (qzTw (transport σ D) e) (gsMap σ _)
    (continuous_gsMap σ _) (gsMap σ.symm _) (continuous_gsMap σ.symm _)
    (gsMap_gsMap_symm σ _) (gsMap_gsMap_symm σ.symm _) hc
  set Φ := pairH1DecompositionMap (qzTw D e) (qzTw (transport σ D) e) (gsMap σ _) (continuous_gsMap σ _)
    LinearMap.id continuous_id hc with hΦdef
  have key : ∀ x, x ∈ Sha D e ↔ Φ x ∈ Sha (transport σ D) e := by
    intro x
    simp only [Sha, Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
    refine forall_congr' fun v => ?_
    have hA₁ : ∀ y, σ.symm y ∈ D.A v ↔ y ∈ (transport σ D).A v := fun y => by
      show _ ↔ y ∈ (D.A v).comap (σ.symm : Ω' →+* Ω)
      rw [ValuationSubring.mem_comap]
      rfl
    have hA : ∀ y, σ y ∈ (transport σ D).A v ↔ y ∈ D.A v := fun y => by
      rw [← hA₁, σ.symm_apply_apply]
    have hcv : ∀ k m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l)
        ((qzTw D e).comp (locFam D.S D.A v) (decMap σ.symm hA₁ k) m) =
        ((qzTw (transport σ D) e).comp (locFam (transport σ D).S (transport σ D).A v)) k
          ((LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) m) := fun _ _ => rfl
    have hΔ := pairH1_id_bijective ((qzTw D e).comp (locFam D.S D.A v))
      ((qzTw (transport σ D) e).comp (locFam (transport σ D).S (transport σ D).A v))
      (decMap σ.symm hA₁) (continuous_decMap σ.symm hA₁) (decMap σ hA) (continuous_decMap σ hA)
      (fun g => Subtype.ext (by ext y; simp [decMap, AlgEquiv.autCongr_apply]))
      (fun g => Subtype.ext (by ext y; simp [decMap, AlgEquiv.autCongr_apply])) hcv
    have hres : resH1 (qzTw (transport σ D) e) (locFam (transport σ D).S (transport σ D).A v)
        (continuous_locFam _ _ v) (Φ x) =
        pairH1DecompositionMap _ _ (decMap σ.symm hA₁) (continuous_decMap σ.symm hA₁) LinearMap.id continuous_id hcv
          (resH1 (qzTw D e) (locFam D.S D.A v) (continuous_locFam _ _ v) x) := by
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    constructor
    · intro h
      exact hres.trans (by rw [h, map_zero])
    · intro h
      exact hΔ.1 (by rw [map_zero]; exact hres.symm.trans h)
  let Φe := LinearEquiv.ofBijective Φ hΦ
  have hmap : (Sha D e).map Φe.toLinearMap =
      Sha (transport σ D) e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (key x).1 hx
    · intro hy
      refine ⟨Φe.symm y, (key _).2 ?_, Φe.apply_symm_apply y⟩
      have : Φ (Φe.symm y) = y := Φe.apply_symm_apply y
      rw [this]
      exact hy
  exact (LinearEquiv.ofSubmodules Φe _ _ hmap).length_eq.symm

theorem exists_lData_shaLen_eq : ∀ {F Ω Ω' : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] [Field Ω'] [Algebra F Ω'] [IsAlgClosure F Ω'] (l : ℕ)
    [Fact l.Prime] (D : Formalism.GaloisCohomology.LData F Ω l),
    ∃ D' : Formalism.GaloisCohomology.LData F Ω' l, ∀ e : ℤ, Formalism.GaloisCohomology.shaLen D' e = Formalism.GaloisCohomology.shaLen D e := by
  intro F Ω Ω' _ _ _ _ _ _ _ _ l _ D
  exact ⟨transport (IsAlgClosure.equiv F Ω Ω') D, shaLen_transport _ D⟩

end Sha

end GlobalTheory.ShaTransport
end
end

