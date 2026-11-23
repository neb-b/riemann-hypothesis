module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0042
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasUEigenvalueOfLocIsotypic
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dc_common {G : Type} [Group G] (K K' : Subgroup G) (x : G) :
    ∃ s : Finset (MulAction.orbit K (x : G ⧸ K')), ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
      (ρ : Representation ℂ G M) (v : M), Hi.dc ρ K K' x v = ∑ q ∈ s, ρ (q : G ⧸ K').out v := by
  by_cases h : Finite (MulAction.orbit K (x : G ⧸ K'))
  · letI := Fintype.ofFinite (MulAction.orbit K (x : G ⧸ K'))
    refine ⟨Finset.univ, fun M _ _ ρ v => ?_⟩
    rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  · refine ⟨∅, fun M _ _ ρ v => ?_⟩
    rcases subsingleton_or_nontrivial M with hM | hM
    · exact Subsingleton.elim _ _
    have hs : (Function.support fun q : MulAction.orbit K (x : G ⧸ K') => ρ (q : G ⧸ K').out) = Set.univ := by
      refine Set.eq_univ_of_forall fun q hq => ?_
      have h1 : ρ ((q : G ⧸ K').out⁻¹ * (q : G ⧸ K').out) = 0 := by rw [map_mul, show ρ (q : G ⧸ K').out = 0 from hq, mul_zero]
      rw [inv_mul_cancel, map_one] at h1
      exact one_ne_zero h1
    rw [Hi.dc, finsum_of_infinite_support, Finset.sum_empty, LinearMap.zero_apply]
    rw [hs]
    exact fun hf => h (Set.finite_univ_iff.1 hf)

private theorem killed_of_mem_iSup {G V U ι J : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (T : J → V →ₗ[ℂ] V) (S : J → U →ₗ[ℂ] U)
    (hTS : ∀ j i u, f i (S j u) = T j (f i u))
    (hT : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → ∀ j, ∀ x ∈ W, T j x ∈ W)
    (φ : V) (h0 : φ ≠ 0) (hK : ∀ j, T j φ = 0)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun j => ?_⟩
        have h4 : S j v ∈ W.comap (f i) := by
          have h5 := hK j
          rw [← e, map_add (f := _)] at h5
          rw [Submodule.mem_comap, hTS, eq_neg_of_add_eq_zero_right h5]
          exact neg_mem (hT W hW j x hx)
        rwa [hc, Submodule.mem_bot] at h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _), ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

private theorem dc_eigen_descend {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Subgroup G) (x : G) (lam : ℂ)
    (φ : V) (h0 : φ ≠ 0) (hK : φ ∈ Hi.fixd ρ K) (hl : Hi.dc ρ K K x φ = lam • φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) :
    ∃ v : U, v ≠ 0 ∧ v ∈ Hi.fixd σ K ∧ Hi.dc σ K K x v = lam • v := by
  obtain ⟨s, hs⟩ := dc_common K K x
  obtain ⟨v, hv0, hv⟩ := killed_of_mem_iSup ρ σ hσ f hf
    (fun j : Option K => j.elim (Hi.dc ρ K K x - lam • LinearMap.id) fun k => ρ k - LinearMap.id)
    (fun j : Option K => j.elim (Hi.dc σ K K x - lam • LinearMap.id) fun k => σ k - LinearMap.id)
    (by
      rintro (_ | k) i u
      set_option synthInstance.maxHeartbeats 100000 in
        · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, hs,
          map_sum, hf]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hf])
    (by
      rintro W hW (_ | k) y hy
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hs]
        exact sub_mem (Submodule.sum_mem _ fun q _ => hW _ _ hy) (W.smul_mem _ hy)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_mem (hW _ _ hy) hy)
    φ h0
    (by
      rintro (_ | k)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hl, sub_self]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_eq_zero.2 (hK k k.2))
    hφ
  exact ⟨v, hv0, fun k hk => sub_eq_zero.1 (hv (some ⟨k, hk⟩)), sub_eq_zero.1 (hv none)⟩

theorem UpperTheory.hasUEigenvalue_of_locIsotypic :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), LocIsotypic ρ w σ → ∀ (c : ℕ) (lam : ℂ), HasU w (ρ.comp (locGL F 2 w)) c lam → HasU w σ.ρ c lam := by
  intro F _ _ w V _ _ ρ σ ⟨_, htop⟩ c lam ⟨φ, h0, hK, hl⟩
  exact dc_eigen_descend (ρ.comp (locGL F 2 w)) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F 2 w g) (f v)} => f.1) (fun f => f.2)
    (K1 w c) _ lam φ h0 hK hl (htop ▸ Submodule.mem_top)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharLocalArtinEqCyclotomicTwist
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.heckeChar_localArtin_eq_cyclotomic_twist :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (χ : HChar F) (ξ : G F Ω →* (Qbar l)ˣ) (t : ℤ), IsOpen (ξ.ker : Set (G F Ω)) → IsCharOf ι χ (cycBar F Ω l ^ t * ξ) → ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ s : Weil h, ((χ.loc w (a s) : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ (t * deg s) * ι (ξ (s : G F Ω) : Qbar l) := by
  intro N F Ω _ _ _ _ _ l _ ι χ ξ t hξ ⟨hc, art, n, hart, _, hL⟩ w hw A h a ha s
  haveI : Finite (G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen hξ
  have hN : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 := UpperTheory.V.Loc.laHecke h art hart ι χ n _ hL ⟨a, ha⟩
  have h2 := UpperTheory.V.Loc.laArith N.aut.art h hw ((cycBar F Ω l ^ t * ξ).comp (Dec (F := F) A).subtype)
    (hc.comp continuous_subtype_val) t ξ.ker.index (Nat.pos_of_ne_zero hN) fun g _ => by
      have e : ((cycBar F Ω l ^ t * ξ).comp (Dec (F := F) A).subtype) g * cycBar F Ω l g ^ (-t) = ξ g := by
        show cycBar F Ω l g ^ t * ξ g * cycBar F Ω l g ^ (-t) = ξ g
        rw [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      rw [e, ← map_pow]
      exact ξ.ker.pow_index_mem _
  have h3 := UpperTheory.V.Loc.laUnique h ⟨a, ha⟩ _ _ _ h1 h2
  haveI : Fintype {j : w.adicCompletion F →+* Qbar l // Continuous j} := @Fintype.ofFinite _ (finite_contEmb w)
  have h4 : locPow ι n w (a s : w.adicCompletion F) = Hi.algPow w (fun _ => 1) (a s : w.adicCompletion F) ^ t := by
    unfold locPow Hi.algPow
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [neg_injective (congrFun h3 j), zpow_one]
  have h0 : Hi.algPow w (fun _ : F →+* Qbar l => 1) (a s : w.adicCompletion F) ^ t ≠ 0 := by
    refine zpow_ne_zero _ ?_
    unfold Hi.algPow
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 (a s).ne_zero)
  have h5 := hL.loc (a s) s (ha.glob art hart s)
  have h6 := UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s
  have h7 : (((cycBar F Ω l ^ t * ξ) (s : G F Ω) : (Qbar l)ˣ) : Qbar l) =
      (cycBar F Ω l (s : G F Ω) : Qbar l) ^ t * (ξ (s : G F Ω) : Qbar l) := by
    rw [← Units.val_zpow_eq_zpow_val, ← Units.val_mul]
    rfl
  rw [h7, h6, h4, mul_zpow, mul_right_comm, mul_left_inj' h0, eq_comm, RingEquiv.symm_apply_eq] at h5
  rw [h5, map_mul, map_zpow₀, map_zpow₀, map_natCast, ← zpow_mul, mul_comm t]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeOperatorsCommuteOnAutomorphicForms
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private theorem finite_translation_mul (g h : GL (Fin a) (Af F)) (φ : TR.Sm F a) :
    TR.finRep F a (g * h) φ = TR.finRep F a g (TR.finRep F a h φ) := by
  rw [map_mul]; rfl

private theorem center_algebra_translation_comm (g : GL (Fin a) (Af F)) {z : Module.End ℂ (TR.Sm F a)} (hz : z ∈ TR.Zalg F a) :
    TR.finRep F a g * z = z * TR.finRep F a g := by
  have key : TR.Zalg F a ≤ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, u, rfl⟩
    have hE : ∀ i j, TR.Eop v i j ∈ Subalgebra.centralizer ℂ {TR.finRep F a g} := by
      intro i j
      rw [Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (TR.lie_rt_fin _ g).symm
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.list_prod_mem _ fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine Subalgebra.add_mem _ ?_ (hE _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 (key hz) _ rfl

private theorem compact_finite_translation_comm (g : GL (Fin a) (Af F)) (k : TR.Kinf F a) (φ : TR.Sm F a) :
    TR.cptRep F a k (TR.finRep F a g φ) = TR.finRep F a g (TR.cptRep F a k φ) := by
  refine Subtype.ext (funext fun x => ?_)
  change φ.1 (x * TR.infGL F a (Unitary.toUnits k) * finGL F a g) =
    φ.1 (x * finGL F a g * TR.infGL F a (Unitary.toUnits k))
  rw [mul_assoc, mul_assoc, TR.infGL_comm]

private theorem automorphic_form_translate (φ : TR.Sm F a) (g : GL (Fin a) (Af F)) (h : TR.IsAutForm φ) :
    TR.IsAutForm (TR.finRep F a g φ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 (ratGL F a γ * x * finGL F a g) = φ.1 (x * finGL F a g)
    rw [mul_assoc, h.left]
  · have e : {k | TR.finRep F a k (TR.finRep F a g φ) = TR.finRep F a g φ} =
        (fun k => g⁻¹ * k * g) ⁻¹' {k | TR.finRep F a k φ = φ} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro hk
        rw [finite_translation_mul, finite_translation_mul, hk, ← finite_translation_mul, inv_mul_cancel, map_one]
        rfl
      · intro hk
        have := congrArg (TR.finRep F a g) hk
        rwa [← finite_translation_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, finite_translation_mul] at this
    rw [e]
    exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ)).map (TR.finRep F a g)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (compact_finite_translation_comm g k φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a)).map (TR.finRep F a g))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨z, hz, rfl⟩, LinearMap.congr_fun (center_algebra_translation_comm g hz) φ⟩
  · obtain ⟨C, N, hC⟩ := h.growth (x * finGL F a g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (x * TR.infGL F a y * finGL F a g)‖ ≤ _
    rw [mul_assoc, TR.infGL_comm, ← mul_assoc]
    exact hC y

private theorem automorphic_form_linear_combination (φ ψ : TR.Sm F a) (c : ℂ) (h : TR.IsAutForm φ) (h' : TR.IsAutForm ψ) :
    TR.IsAutForm (φ + c • ψ) := by
  refine ⟨fun γ x => ?_, ?_, ?_, ?_, fun x => ?_⟩
  · change φ.1 _ + c * ψ.1 _ = φ.1 _ + c * ψ.1 _
    rw [h.left, h'.left]
  · rw [isOpen_iff_mem_nhds]
    intro k₀ hk₀
    have hO : IsOpen ((fun k => k₀⁻¹ * k) ⁻¹' ({k | TR.finRep F a k φ = φ} ∩ {k | TR.finRep F a k ψ = ψ})) :=
      (h.level.inter h'.level).preimage (continuous_const.mul continuous_id)
    refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
    · simp
    · rintro k ⟨h1, h2⟩
      have h1' : TR.finRep F a (k₀⁻¹ * k) φ = φ := h1
      have h2' : TR.finRep F a (k₀⁻¹ * k) ψ = ψ := h2
      have h3 : TR.finRep F a (k₀⁻¹ * k) (φ + c • ψ) = φ + c • ψ := by rw [map_add (f := _), map_smul, h1', h2']
      have h4 : TR.finRep F a k₀ (φ + c • ψ) = φ + c • ψ := hk₀
      change TR.finRep F a k (φ + c • ψ) = φ + c • ψ
      rw [← mul_inv_cancel_left k₀ k, finite_translation_mul, h3, h4]
  · have := h.kfin
    have := h'.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ (Set.range fun k => TR.cptRep F a k φ) ⊔
        Submodule.span ℂ (Set.range fun k => TR.cptRep F a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    simp only [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · have := h.zfin
    have := h'.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z φ) '' TR.Zalg F a) ⊔
        Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z ψ) '' TR.Zalg F a)) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    simp only [map_add (f := _), map_smul]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z, hz, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨z, hz, rfl⟩))
  · obtain ⟨C, N, hC⟩ := h.growth x
    obtain ⟨D, M, hD⟩ := h'.growth x
    refine ⟨|C| + ‖c‖ * |D|, N + M, fun y => ?_⟩
    have h1 : 1 ≤ TR.height y := by
      unfold TR.height
      have := norm_nonneg (TR.toL y.val)
      have := norm_nonneg (TR.toL (y⁻¹).val)
      linarith
    have bound : ∀ (B : ℝ) (n : ℕ), n ≤ N + M → B * TR.height y ^ n ≤ |B| * TR.height y ^ (N + M) := fun B n hn =>
      mul_le_mul (le_abs_self B) (pow_le_pow_right₀ h1 hn) (pow_nonneg (zero_le_one.trans h1) n) (abs_nonneg B)
    have b1 := (hC y).trans (bound C N (Nat.le_add_right _ _))
    have b2 := (hD y).trans (bound D M (Nat.le_add_left _ _))
    change ‖φ.1 _ + c * ψ.1 _‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, add_mul, mul_assoc]
    exact add_le_add b1 (mul_le_mul_of_nonneg_left b2 (norm_nonneg c))

end SlopeTestRemainingChoices

theorem UpperTheory.hecke_operators_commute_on_automorphic_forms :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), TR.IsAutForm (0 : TR.Sm F a) ∧ (∀ (φ : TR.Sm F a) (g : GL (Fin a) (Af F)), TR.IsAutForm φ → TR.IsAutForm (TR.finRep F a g φ)) ∧ ∀ (φ ψ : TR.Sm F a) (z : ℂ), TR.IsAutForm φ → TR.IsAutForm ψ → TR.IsAutForm (φ + z • ψ) := by
  intro F _ _ _ a
  exact ⟨TR.isAutForm_const (Submodule.zero_mem _), automorphic_form_translate, automorphic_form_linear_combination⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HilbertHolomorphicInvariantIntegralTranslation
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open scoped Matrix

private theorem map_aff' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map f (aff 1 x) = aff 1 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_zero' {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_mirab' {R : Type} [CommRing R] (x : R) : aff (1 : Rˣ) x ∈ mirab R := by
  change _ = _
  simp [funext_iff, Fin.forall_fin_two, Matrix.vecMul, dotProduct, aff]

open UpperTheory.V.Af.GlobalFixedVectors in
theorem UpperTheory.hilbertHolomorphic_invariant_integralTranslation :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) (φ : TR.Sm F 2), IsHol k c ω φ → ∀ o : Af F, (∀ v : Pl F, Valued.v (pLoc F v o) ≤ 1) → TR.finRep F 2 (aff 1 o) φ = φ := by
  classical
  intro F _ _ _ k c ω φ hφ o ho
  have key : ∀ S : Finset (Pl F),
      (∀ x ∈ Ohat F, (∀ w ∈ S, pLoc F w x = 0) → TR.finRep F 2 (aff 1 x) φ = φ) →
      ∀ x ∈ Ohat F, TR.finRep F 2 (aff 1 x) φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun h x hx => h x hx (by simp)
    | insert w S hw ih =>
      intro h
      refine ih fun x hx hS => ?_
      have e : aff 1 x = aff 1 (x - sLoc F w (pLoc F w x)) * locGL F 2 w (aff 1 (pLoc F w x)) := gl_ext fun u => by
        rw [map_mul, map_aff', map_aff', map_sub]
        by_cases hu : u = w
        · subst hu
          rw [pLoc_locGL, pLoc_sLoc, sub_self, aff_zero', one_mul]
        · rw [pLoc_locGL_of_ne hu, pLoc_sLoc_of_ne hu, sub_zero, mul_one]
      have hK : aff 1 (pLoc F w x) ∈ K1 w (c w) := by
        refine ⟨aff 1 ⟨pLoc F w x, mem_Ohat.1 hx w⟩, ?_, map_aff' _ _⟩
        change Matrix.GeneralLinearGroup.map _ _ ∈ mirab _
        rw [map_aff']
        exact aff_mirab' _
      have h1 : TR.finRep F 2 (locGL F 2 w (aff 1 (pLoc F w x))) φ = φ := hφ.level w _ hK
      rw [e, map_mul, Module.End.mul_apply, h1]
      refine h _ (sub_mem hx (sLoc_mem w hx)) fun u hu => ?_
      rw [map_sub]
      by_cases huw : u = w
      · subst huw
        rw [pLoc_sLoc, sub_self]
      · rw [pLoc_sLoc_of_ne huw, sub_zero]
        exact hS u ((Finset.mem_insert.1 hu).resolve_left huw)
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (hφ.aut.level.mem_nhds (show (1 : GL (Fin 2) (Af F)) ∈ _ by simp))
  refine key S (fun x hx h0 => hS (mem_KAway.2 ⟨⟨aff 1 ⟨x, hx⟩, ?_, map_aff' _ _⟩, fun w hw => ?_⟩)) o (mem_Ohat.2 ho)
  · haveI : Subsingleton (Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · rw [map_aff', h0 w hw, aff_zero']
end

