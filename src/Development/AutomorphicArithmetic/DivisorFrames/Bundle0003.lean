module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsIsOpenIsCompactSubgroupFiniteAdelicUnitary
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) ∧ IsCompact (K : Set (finU (E := E) (n := n))) := by
  intro E _ _ _ n
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hKo : IsOpen (U0.comap p : Set (finU (E := E) (n := n))) := hU0o.preimage hp
  have hfin : ∀ x : UA E n, x ∈ finU (E := E) (n := n) ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  exact ⟨U0.comap p, hKo, IsCompact.of_isClosed_subset
    (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen _ hKo) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalAutomorphicFormsUnitaryOfTypeLe
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem UpperTheory.finiteDimensional_automorphicForms_unitary_of_type_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : infU E n → Module.End ℂ S)
        (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)),
        (∀ f ∈ M, (∀ v, ∀ γ ∈ ratU E n, ∀ g, f v (γ * g) = f v g) ∧ (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) ∧
          ∀ k ∈ K, ∀ v, RU E n (k : finU (E := E) (n := n)) (f v) = f v) → FiniteDimensional ℂ M := by
  intro E _ _ _ n S _ _ _ ρ K hK M hM
  obtain ⟨R, hR⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hK
  let T : M →ₗ[ℂ] (R → Module.Dual ℂ S) :=
    { toFun := fun f s => (LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) (s : UA E n)).comp f.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have h0 : ∀ s ∈ R, ∀ v, f.1 v s = 0 := fun s hs v =>
      LinearMap.congr_fun (congrFun hf ⟨s, hs⟩) v
    obtain ⟨h1, h2, h3⟩ := hM f.1 f.2
    refine Subtype.ext (LinearMap.ext fun v => funext fun g => ?_)
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hR g
    have e1 : f.1 v (γ * s * x * (k : UA E n)) = f.1 v (γ * s * x) := congrFun (h3 k hk v) (γ * s * x)
    have e2 : f.1 (ρ ⟨x, hx⟩ v) s = f.1 v (s * x) := congrFun (h2 ⟨x, hx⟩ v) s
    show f.1 v (γ * s * x * (k : UA E n)) = 0
    rw [e1, mul_assoc γ s x, h1 v γ hγ, ← e2, h0 s hs]
  exact Module.Finite.of_injective T hT
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.HasWeightAtOfNeZeroIntertwining
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

private theorem cEmb_of_mem_embU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {τ σ : E →+* ℂ}
    (h : InfinitePlace.mk σ ≠ InfinitePlace.mk τ) {x : UA E n} (hx : x ∈ embU n τ) : cEmb σ x = 1 := by
  have h1 := (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_iInf] at h1
  have h2 := h1 σ
  rw [Subgroup.mem_iInf] at h2
  exact h2 h

theorem UpperTheory.hasWeightAt_of_ne_zero_intertwining :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] (emb : ι → (E →+* ℂ)), Function.Injective (fun τ => InfinitePlace.mk (emb τ)) →
        ∀ (lam : ι → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)) (f : Formalism.L2.DIV.VV ℂ lam →ₗ[ℂ] (UA E n → ℂ)), f ≠ 0 → (∀ v, f v ∈ π) →
        (∀ x ∈ infU E n, ∀ v, f (Formalism.L2.DIV.rhoK lam (fun τ => cEmb (emb τ) x) v) = RU E n x (f v)) →
        ∀ τ, HasWeightAt π (emb τ) (lam τ) := by
  intro E _ _ _ n ι _ emb hinj lam π f hf0 hf heq τ
  classical
  obtain ⟨e, he⟩ : ∃ e, f (GlobalTheory.CoefIrred.tenMul lam e) ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hf0
    apply (Formalism.L2.DIV.bVV ℂ lam).ext
    intro i
    have hB : Formalism.L2.DIV.bVV ℂ lam i = GlobalTheory.CoefIrred.tenMul lam
        (fun τ => GlobalTheory.CoefIrred.ssBasis ℂ (lam τ) (i τ)) := by
      apply Subtype.ext
      rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.bVVfun]
      simp only [GlobalTheory.CoefIrred.ssBasis_coe]
    rw [hB]
    exact hc _
  refine ⟨isIrreducible_sqRep n (lam τ), f ∘ₗ (GlobalTheory.CoefIrred.tenMul lam).toLinearMap e τ, fun h0 => he ?_,
    fun a => hf _, fun x a => ?_⟩
  · have := LinearMap.congr_fun h0 (e τ)
    simpa [MultilinearMap.toLinearMap] using this
  · have hx : x.1 ∈ infU E n := embU_le_infU _ x.2
    have h2 := heq x.1 hx (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ a))
    have h3 : Formalism.L2.DIV.rhoK lam (fun σ => cEmb (emb σ) x.1) (GlobalTheory.CoefIrred.tenMul lam (Function.update e τ a)) =
        GlobalTheory.CoefIrred.tenMul lam
          (Function.update e τ (GlobalTheory.Branching.sqRep ℂ n (lam τ) (cEmb (emb τ) x.1) a)) := by
      rw [rhoK_tenMul]
      congr 1
      funext σ
      by_cases h : σ = τ
      · subst h
        simp only [Function.update_self]
      · have h4 : cEmb (emb σ) x.1 = 1 := cEmb_of_mem_embU (fun h5 => h (hinj h5)) x.2
        simp only [Function.update_of_ne h, h4, map_one, Module.End.one_apply]
    rw [h3] at h2
    exact h2
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.SpanHighestWeightRepUnitaryGroupRealPointsImageE
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

private theorem UpperTheory.exists_infinite_unitary_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]
    (emb : ι → (E →+* ℂ)) (hinj : Function.Injective (fun τ => InfinitePlace.mk (emb τ)))
    (g : ι → GL (Fin n) ℂ)
    (hg : ∀ v, (g v : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ y : infU E n, (MonoidHom.pi fun τ => cEmb (E := E) (n := n) (emb τ)) y.1 = g := by
  classical
  let J : Subgroup (ι → GL (Fin n) ℂ) :=
    ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (emb τ)).comp (infU E n).subtype).range
  let Hs : ι → Subgroup (GL (Fin n) ℂ) := fun _ => (GlobalTheory.Branching.unitaryIncl n).range
  have hle : Subgroup.pi Set.univ Hs ≤ J := by
    rw [Subgroup.pi_le_iff]
    intro v
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := _root_.GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n (emb v)
    let x := e.symm u
    have hx := Subgroup.mem_inf.1 x.2
    refine ⟨⟨x.1, hx.1⟩, ?_⟩
    funext v'
    by_cases h : v' = v
    · subst h
      change cEmb (emb v') x.1 = _
      rw [← he, e.apply_symm_apply]
      simp
    · have h5 : x.1 ∈ (cEmb (E := E) (n := n) (emb v')).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 (emb v')) (fun h' => h (hinj h'))
      change cEmb (emb v') x.1 = _
      rw [MonoidHom.mem_ker.1 h5]
      simp [h]
  obtain ⟨y, hy⟩ : g ∈ J := hle fun v _ => ⟨⟨(g v).val, hg v⟩, Units.ext rfl⟩
  exact ⟨y, hy⟩

theorem UpperTheory.span_highestWeightRep_unitaryGroup_realPoints_image_eq_top :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι] (emb : ι → (E →+* ℂ)), Function.Injective (fun τ => InfinitePlace.mk (emb τ)) →
        ∀ (lam : ι → DomWeight n) [Nontrivial (Formalism.L2.DIV.VV ℂ lam)],
        Submodule.span ℂ (Set.range ((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp
          ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (emb τ)).comp (infU E n).subtype))) = ⊤ := by
  intro E _ _ _ n ι _ emb hinj lam _
  haveI : ∀ v, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (lam v).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  exact GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ ((GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨inferInstance, fun U hU =>
    GlobalTheory.CoefIrred.vv_irreducible_unitary ι n lam U fun g hg x hx => by
      obtain ⟨y, rfl⟩ := UpperTheory.exists_infinite_unitary_lift emb hinj g hg
      exact hU y x hx⟩)
end

