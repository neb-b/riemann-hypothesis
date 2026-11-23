module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelBaseEig

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem cont_smul (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (Γ : Type) [Group Γ]
    [TopologicalSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (hχ : Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l])) (m : QO l O) :
    Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m := by
  refine (QO.isBaseChange l O).inductionOn m
    (motive := fun m => Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m) ?_ ?_ ?_
  · intro x
    have h1 : Continuous fun g => ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x :=
      Continuous.comp (LDataCardLeFinrank.contScal l Γ χ hχ) (Continuous.prodMk_left x)
    have h2 : Continuous (QO.incl l O) := continuous_of_discreteTopology
    refine (h2.comp h1).congr fun g => ?_
    exact map_smul (QO.incl l O) _ x
  · intro s x hx
    have h2 : Continuous fun y : QO l O => s • y := continuous_of_discreteTopology
    exact (h2.comp hx).congr fun g => smul_comm _ _ _
  · intro x y hx hy
    exact (hx.add hy).congr fun g => (smul_add _ _ _).symm

private theorem locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantFunctions.locConst ψ h

theorem UpperTheory.V.Base.contTw :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime],
      Continuous (cycZ k Ω l) ∧ (∀ e : ℤ, ContAction (UpperTheory.V.LDataCardLeFinrank.qzG k Ω l e)) ∧
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ψ : G k Ω →* Oˣ) (n : ℤ), IsOpen (ψ.ker : Set (G k Ω)) →
        ContAction (twist₂ l (ψ * chiO (k := k) (Ω := Ω) l O ^ n)) := by
  intro k Ω _ _ _ _ _ l _
  have hc := ReciprocityTheory.Gal.continuous_cycZ k Ω l
  have hcPow (n : ℤ) : Continuous fun g : G k Ω => (((cycZ k Ω l ^ n) g : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp
      (show Continuous fun g : G k Ω => cycZ k Ω l g ^ n from hc.zpow n)
  refine ⟨hc, fun e => LDataCardLeFinrank.contScal l _ (cycZ k Ω l ^ (-e)) (hcPow (-e)),
    fun O _ _ ψ n hψ => ?_⟩
  refine continuous_prod_of_discrete_right.2 fun m => ?_
  have h1 := cont_smul l O _ (cycZ k Ω l ^ n) (hcPow n) m
  have h2 := ((locConst ψ hψ).prodMk ((IsLocallyConstant.iff_continuous _).2 h1)).comp
    fun p : Oˣ × QO l O => (p.1 : O) • p.2
  refine h2.continuous.congr fun g => ?_
  show (ψ g : O) • (((cycZ k Ω l g ^ n : ℤ_[l]ˣ) : ℤ_[l]) • m) =
    ((ψ g * chiO (k := k) (Ω := Ω) l O g ^ n : Oˣ) : O) • m
  have e : chiO (k := k) (Ω := Ω) l O g ^ n = Units.map (algebraMap ℤ_[l] O).toMonoidHom (cycZ k Ω l g ^ n) :=
    (map_zpow (Units.map (algebraMap ℤ_[l] O).toMonoidHom) (cycZ k Ω l g) n).symm
  rw [Units.val_mul, mul_smul, e]
  exact congrArg _ (algebraMap_smul O _ m).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DecInf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem exists_unit (l : ℕ) [hl : Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl2 := hl.out.two_le
  have hnorm : ‖((1 + l : ℕ) : ℤ_[l])‖ = 1 := by
    push_cast
    rw [PadicInt.norm_add_eq_max_of_ne, norm_one, PadicInt.norm_p]
    · exact max_eq_left (inv_le_one_of_one_le₀ hl1.le)
    · rw [norm_one, PadicInt.norm_p]
      exact (inv_lt_one_of_one_lt₀ hl1).ne'
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.2 hnorm
  refine ⟨u, fun h => ?_⟩
  rw [← Units.isOfFinOrder_val, hu, isOfFinOrder_iff_pow_eq_one] at h
  obtain ⟨n, hn, h⟩ := h
  rw [← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h
  omega

theorem UpperTheory.V.Base.decInf :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsOpen (U : Set (G k Ω)) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      ∃ g ∈ U ⊓ Dec (F := k) A, ¬ IsOfFinOrder (cycZ k Ω l g) := by
  intro k Ω _ _ _ _ _ l _ U hU A hlt
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨u, hu⟩ := exists_unit l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hlt u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ k Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ k Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G k Ω := { (σ ^ n).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hg : g ∈ Dec (F := k) A := (Dec (F := ℚ) A).pow_mem (Ine_le_Dec A hσ) n
  have hgu : cycZ k Ω l g = u ^ n := by
    change cycZ ℚ Ω l (σ ^ n) = u ^ n
    rw [map_pow, hσu]
  haveI : Finite (G k Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI := Subgroup.finiteIndex_normalCore U
  haveI := Subgroup.normalCore_normal U
  have hN : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hgU : g ^ U.normalCore.index ∈ U := U.normalCore_le (Subgroup.pow_index_mem _ g)
  refine ⟨g ^ U.normalCore.index, ⟨hgU, Subgroup.pow_mem (Dec (F := k) A) hg _⟩, ?_⟩
  rw [map_pow, hgu, ← pow_mul, isOfFinOrder_pow]
  rintro (h | h)
  · exact hu h
  · exact mul_ne_zero hn.ne' hN h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.InflUnique
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

set_option maxHeartbeats 200000 in
theorem UpperTheory.V.Base.inflUnique :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ),
      (∀ x, ∃ y, Infl k D e x y) ∧ ∀ x x' y y', Infl k D e x y → Infl k D e x' y' → (x = x' ↔ y = y') := by
  intro k E Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e
  obtain ⟨hemb, -, -⟩ := galEmbTop k E Ω
  let ψ : G E Ω →* galOf k E Ω := (galEmb k E Ω).codRestrict _ (galEmb_mem k E Ω)
  have hsurj : Function.Surjective ψ := by
    rintro ⟨τ, hτ⟩
    refine ⟨AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) (fun x => hτ x), ?_⟩
    apply Subtype.ext
    ext x
    rfl
  let Ψ : G E Ω ≃* galOf k E Ω :=
    MulEquiv.ofBijective ψ ⟨fun a b h => hemb.injective (congrArg Subtype.val h), hsurj⟩
  have hΨ : ∀ σ, Ψ σ = ⟨galEmb k E Ω σ, galEmb_mem k E Ω σ⟩ := fun _ => rfl
  have hcont : Continuous (fun u : galOf k E Ω => Ψ.symm u) := by
    rw [hemb.continuous_iff]
    have hc : (galEmb k E Ω) ∘ (fun u : galOf k E Ω => Ψ.symm u) = Subtype.val := by
      funext u
      show ((Ψ (Ψ.symm u) : galOf k E Ω) : G k Ω) = u
      rw [Ψ.apply_symm_apply]
    rw [hc]
    exact continuous_subtype_val
  have hEk : ∀ σ : G E Ω, LDataCardLeFinrank.qzG k Ω l e (galEmb k E Ω σ) = LDataCardLeFinrank.qzG E Ω l e σ := by
    intro σ
    have hχ : (cycZ k Ω l ^ (-e)).comp (galEmb k E Ω) = cycZ E Ω l ^ (-e) := by
      refine MonoidHom.ext fun τ => ?_
      rw [MonoidHom.comp_apply]
      simp only [MonoidHom.zpow_apply]
      rfl
    show scalRep (QZ l) (cycZ k Ω l ^ (-e)) (galEmb k E Ω σ) = scalRep (QZ l) (cycZ E Ω l ^ (-e)) σ
    rw [← hχ]
    rfl
  have hrep : ∀ σ : G E Ω, LDataCardLeFinrank.qzG k Ω l e (galEmb k E Ω σ) = qzTw D e (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) σ) := by
    intro σ
    have h := DFunLike.congr_fun (LDataCardLeFinrank.qzTw_comp_toGS D e) σ
    rw [MonoidHom.comp_apply] at h
    rw [hEk]
    exact h.symm
  have hu : ∀ u : galOf k E Ω, (u : G k Ω) = galEmb k E Ω (Ψ.symm u) := by
    intro u
    conv_lhs => rw [← Ψ.apply_symm_apply u]
    rfl
  have hTs : Function.Surjective (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))) :=
    QuotientGroup.mk'_surjective _
  constructor
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    let f : galOf k E Ω → QZ l := fun u => (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm u))
    have hf : f ∈ Z1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω) := by
      refine ⟨z.2.1.comp ((continuous_toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E)))).comp hcont), ?_⟩
      intro u v
      show (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm (u * v))) =
        (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm u)) +
          ((LDataCardLeFinrank.qzG k Ω l e).comp (galOf k E Ω).subtype u) ((z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm v)))
      rw [map_mul, map_mul, z.2.2, MonoidHom.comp_apply, Subgroup.coe_subtype, hu u, hrep]
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, z, ⟨f, hf⟩, rfl, rfl, ?_⟩
    intro σ
    show (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) → QZ l) (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (Ψ.symm ⟨galEmb k E Ω σ, _⟩)) = _
    rw [← hΨ, Ψ.symm_apply_apply]
  · rintro x x' y y' ⟨z1, w1, rfl, rfl, h1⟩ ⟨z2, w2, rfl, rfl, h2⟩
    rw [mk_eq_mk, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    apply exists_congr
    intro m
    constructor
    · intro h u
      obtain ⟨σ, rfl⟩ := Ψ.surjective u
      have h3 := h (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) σ)
      rw [Submodule.coe_sub, Pi.sub_apply] at h3
      rw [hΨ, h1, h2, h3]
      exact congrArg (fun T => T m - m) (hrep σ).symm
    · intro h g
      obtain ⟨σ, rfl⟩ := hTs g
      have h3 := h (Ψ σ)
      rw [hΨ, h1, h2] at h3
      rw [Submodule.coe_sub, Pi.sub_apply, h3]
      exact congrArg (fun T => T m - m) (hrep σ)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoBase
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

theorem UpperTheory.V.Base.qoBase :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (χ : G →* ℤ_[l]ˣ) (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U 𝒟) = Module.length ℤ_[l] (LocSel (scalRep (QZ l) χ) U 𝒟) * eO l O ∧
      ∀ [U.Normal] (h𝒟 : ConjStable 𝒟) (g : G) (s : ℤ_[l]),
        Module.length O (Module.End.eigenspace (selRep (twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ)) U h𝒟 g) (algebraMap ℤ_[l] O s)) =
          Module.length ℤ_[l] (Module.End.eigenspace (selRep (scalRep (QZ l) χ) U h𝒟 g) s) * eO l O := by
  intro l _ G _ _ _ O _ _ _ _ _ χ U 𝒟
  obtain ⟨-, hfree, hloc, -, he, -⟩ := dvrFacts l O
  have hj : ∀ g m, QO.incl l O (scalRep (QZ l) χ g m) =
      twist₂ l ((Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp χ) g (QO.incl l O m) := fun g m => by
    show QO.incl l O (((χ g : ℤ_[l]ˣ) : ℤ_[l]) • m) = algebraMap ℤ_[l] O (χ g : ℤ_[l]ˣ) • QO.incl l O m
    rw [map_smul, algebraMap_smul]
  rw [he]
  exact ⟨selBase ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O) (QO.isBaseChange l O) hj U 𝒟,
    fun h𝒟 g s => (selBaseEig ℤ_[l] G (QZ l) (scalRep (QZ l) χ) O (QO l O) _ (QO.incl l O)
      (QO.isBaseChange l O) hj U 𝒟 h𝒟).2 g s⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base TensorProduct

private theorem length_quotient_span_eq_addVal (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (x : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span {x}) = IsDiscreteValuationRing.addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [IsDiscreteValuationRing.addVal_def _ u hϖ m rfl, Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

theorem UpperTheory.V.Base.qoExt :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra ℤ_[l] O'] [Module.Finite ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] (θ : G →* Oˣ)
      (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O' (LocSel (twist₂ l ((Units.map (algebraMap O O').toMonoidHom).comp θ)) U 𝒟) * eO l O = Module.length O (LocSel (twist₂ l θ) U 𝒟) * eO l O' ∧
      ∀ [U.Normal] (h𝒟 : ConjStable 𝒟) (W : Subgroup G) (ψ : W →* Oˣ),
        Module.length O' (selEig (twist₂ l ((Units.map (algebraMap O O').toMonoidHom).comp θ)) U h𝒟 W ((Units.map (algebraMap O O').toMonoidHom).comp ψ)) * eO l O =
          Module.length O (selEig (twist₂ l θ) U h𝒟 W ψ) * eO l O' := by
  intro l _ G _ _ _ O _ _ _ _ _ O' _ _ _ _ _ _ _ θ U 𝒟
  obtain ⟨hiO, -, hlocO, -, -, -, -, hvO, -⟩ := dvrFacts l O
  obtain ⟨hiO', -, -, -, -, -, -, hvO', -⟩ := dvrFacts l O'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hlO : (l : O) ≠ 0 := by
    intro h
    apply hl0
    apply hiO
    rw [map_natCast, h, map_zero]
  have hlmax : (l : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] O),
      isUnit_map_iff]
    exact PadicInt.p_nonunit
  have hdvd : ϖ ∣ (l : O) := by
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hlmax
  have hϖ' : algebraMap O O' ϖ ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := hdvd
    apply hl0
    apply hiO'
    rw [map_zero, IsScalarTower.algebraMap_apply ℤ_[l] O O', map_natCast, hc, map_mul, h, zero_mul]
  have hinj : Function.Injective (algebraMap O O') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    rw [map_mul, map_pow] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact (u.isUnit.map (algebraMap O O')).ne_zero h
    · exact hϖ' (pow_eq_zero_iff'.mp h).1
  haveI : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').mpr hinj
  haveI : Module.Finite O O' := Module.Finite.of_restrictScalars_finite ℤ_[l] O O'
  haveI : Module.Free O O' := Module.free_of_finite_type_torsion_free'
  haveI : IsLocalHom (algebraMap O O') := inferInstance
  have hf : Module.length O' (O' ⧸ Ideal.map (algebraMap O O') (IsLocalRing.maximalIdeal O)) * eO l O =
      eO l O' := by
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hlO hϖ
    have hlO' : ((l : O') ) = algebraMap O O' u * (algebraMap O O' ϖ) ^ n := by
      rw [← map_natCast (algebraMap O O'), hu, map_mul, map_pow]
    rw [hvO, hvO', hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, length_quotient_span_eq_addVal O' _ hϖ',
      IsDiscreteValuationRing.addVal_def _ u hϖ n hu, hlO', IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow,
      (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr (u.isUnit.map _), zero_add, nsmul_eq_mul,
      mul_comm]
  letI : Module O (QO l O') := TensorProduct.leftModule
  haveI : IsScalarTower O O' (QO l O') :=
    (inferInstance : IsScalarTower O O' (TensorProduct ℤ_[l] O' (QZ l)))
  haveI : IsScalarTower ℤ_[l] O (QO l O') :=
    (inferInstance : IsScalarTower ℤ_[l] O (TensorProduct ℤ_[l] O' (QZ l)))
  let j : QO l O →ₗ[O] QO l O' :=
    TensorProduct.AlgebraTensorModule.map (Algebra.linearMap O O') LinearMap.id
  have hj : IsBaseChange O' j := by
    refine (QO.isBaseChange l O).of_comp ?_
    convert QO.isBaseChange l O' using 1
    apply LinearMap.ext
    intro m
    change TensorProduct.AlgebraTensorModule.map (Algebra.linearMap O O') LinearMap.id
        ((1 : O) ⊗ₜ[ℤ_[l]] m) = (1 : O') ⊗ₜ[ℤ_[l]] m
    rw [TensorProduct.AlgebraTensorModule.map_tmul, Algebra.linearMap_apply, map_one,
      LinearMap.id_apply]
  have hcomp : ∀ (g : G) (m : QO l O), j ((twist₂ l θ) g m) =
      (twist₂ l ((Units.map (algebraMap O O').toMonoidHom).comp θ)) g (j m) := by
    intro g m
    simp only [twist₂, scalRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_coe,
      id_eq, map_smul, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [algebraMap_smul]
  refine ⟨?_, ?_⟩
  · rw [selBase O G (QO l O) (twist₂ l θ) O' (QO l O') _ j hj hcomp U 𝒟, mul_assoc, hf]
  · intro _ h𝒟 W ψ
    rw [(selBaseEig O G (QO l O) (twist₂ l θ) O' (QO l O') _ j hj hcomp U 𝒟 h𝒟).1 W ψ, mul_assoc, hf]
end

