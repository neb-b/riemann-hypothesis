module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Wold
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.SafeUGap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PiPtsHecke

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleRankThreeStrengthen
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

namespace UpperTheory.GalN.V

section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

structure AdmKN [IsCMField F] (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : IsAutCsdN ι r
  level : Level l M m r
  odd : Keep.OddU l r

end

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

variable {K : Type} [Field K] [NumberField K] [Algebra K Ω] [IsScalarTower ℚ K Ω]


omit [IsAlgClosure ℚ Ω] [Algebra ℚ Ω] [IsScalarTower ℚ K Ω] in
structure Adm3N [IsCMField K] (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop where
  irr : IsIrr ρ
  aut : IsAutCsdN ι (tw ρ (cycBar K Ω l)⁻¹)
  level : Level l N ![(e : ℤ), 0, -(e : ℤ)] ρ
  unl : Keep.OddU l ρ


omit [IsAlgClosure ℚ Ω] in
def Adm2N (ι : Qbar l ≃+* ℂ) (e M : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop :=
  ∃ W : G ℚ Ω →* GL (Fin 2) (Qbar l), IsIrr W ∧
    ((∃ f : Newform (2 * e + 1), f.Att ι (tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitQ ι W) ∧
    Level l M ![(e : ℤ), -(e : ℤ)] W ∧ IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W) ∧
    ∃ g : GL (Fin 3) (Qbar l), ∀ s : G K Ω, ((g * ρ s * g⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l)) =
      !![W (s.restrictScalars ℚ) 0 0, 0, W (s.restrictScalars ℚ) 0 1; 0, 1, 0;
         W (s.restrictScalars ℚ) 1 0, 0, W (s.restrictScalars ℚ) 1 1]

end

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsoPick
section
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Hi

private theorem isoPick_mod {R M : Type} {I : Type 1} [Ring R] [AddCommGroup M] [Module R M]
    (S : I → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)] [∀ i, IsSimpleModule R (S i)]
    (y : M) (hy : y ≠ 0) (hmem : y ∈ ⨆ i, isotypicComponent R M (S i)) :
    ∃ i₀, y ∉ ⨆ i : {i // IsEmpty (S i₀ ≃ₗ[R] S i)}, isotypicComponent R M (S i.1) := by
  classical
  have hA : ∀ i, isotypicComponent R M (S i) = ⊥ ∨ isotypicComponent R M (S i) ∈ isotypicComponents R M := by
    intro i
    by_cases h : isotypicComponent R M (S i) = ⊥
    · exact Or.inl h
    · right
      obtain ⟨m, ⟨e⟩⟩ : ∃ m : Submodule R M, Nonempty (m ≃ₗ[R] S i) := by
        by_contra hcon
        push Not at hcon
        exact h (sSup_eq_bot.2 fun m ⟨e⟩ => ((hcon m).false e).elim)
      haveI : IsSimpleModule R m := IsSimpleModule.congr e
      exact ⟨m, ‹_›, (LinearEquiv.isotypicComponent_eq e).symm⟩
  let T : Set (Submodule R M) := isotypicComponents R M ∩ Set.range fun i => isotypicComponent R M (S i)
  have hind : iSupIndep (Subtype.val : T → Submodule R M) :=
    (sSupIndep_iff _).1 ((sSupIndep_isotypicComponents R M).mono Set.inter_subset_left)
  have hT : y ∈ ⨆ c : T, (c : Submodule R M) := by
    refine (show (⨆ i, isotypicComponent R M (S i)) ≤ _ from iSup_le fun i => ?_) hmem
    rcases hA i with h | h
    · rw [h]; exact bot_le
    · exact le_iSup (fun c : T => (c : Submodule R M)) ⟨_, h, i, rfl⟩
  obtain ⟨f, hf, hs⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hT
  obtain ⟨c, hc⟩ : f.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    exact hy (by simpa using hs.symm)
  obtain ⟨⟨m, hm, hcm⟩, i₀, hi₀⟩ := c.2
  refine ⟨i₀, fun hyC => ?_⟩
  have hCD : (⨆ i : {i // IsEmpty (S i₀ ≃ₗ[R] S i)}, isotypicComponent R M (S i.1)) ≤
      ⨆ (j : T) (_ : j ≠ c), (j : Submodule R M) := iSup_le fun ⟨i, hi⟩ => by
    rcases hA i with h | h
    · change isotypicComponent R M (S i) ≤ _
      rw [h]; exact bot_le
    · refine le_iSup₂_of_le (f := fun (j : T) (_ : j ≠ c) => (j : Submodule R M)) ⟨_, h, i, rfl⟩ (fun e => ?_) le_rfl
      have he : isotypicComponent R M (S i) = c.1 := congrArg Subtype.val e
      have hle : m ≤ c.1 := hcm ▸ m.le_isotypicComponent
      obtain ⟨e₁⟩ := isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R M (S i₀)) m (hle.trans hi₀.ge)
      obtain ⟨e₂⟩ := isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R M (S i)) m (hle.trans he.ge)
      exact hi.false (e₁.symm.trans e₂)
  rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hc] at hs
  have h2 : ∑ j ∈ f.support.erase c, f j ∈ ⨆ (j : T) (_ : j ≠ c), (j : Submodule R M) :=
    Submodule.sum_mem _ fun j hj =>
      (le_iSup₂_of_le (f := fun (j : T) (_ : j ≠ c) => (j : Submodule R M)) j (Finset.ne_of_mem_erase hj) le_rfl) (hf j)
  have h3 : f c ∈ ⨆ (j : T) (_ : j ≠ c), (j : Submodule R M) := by
    rw [eq_sub_of_add_eq hs]
    exact sub_mem (hCD hyC) h2
  exact Finsupp.mem_support_iff.1 hc (Submodule.disjoint_def.1 (hind c) _ (hf c) h3)

private theorem isoPick_range {H S Y : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ H S) (π : Representation ℂ H Y) (hσ : σ.IsIrreducible)
    (f : S →ₗ[ℂ] Y) (hf : ∀ g v, f (σ g v) = π g (f v)) (s : S) :
    π.asModuleEquiv.symm (f s) ∈ isotypicComponent (MonoidAlgebra ℂ H) π.asModule σ.asModule := by
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  let F : σ.asModule →ₗ[MonoidAlgebra ℂ H] π.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule σ π ⟨f, fun g => LinearMap.ext (hf g)⟩
  have : LinearMap.range F ≤ isotypicComponent (MonoidAlgebra ℂ H) π.asModule σ.asModule := by
    rcases LinearMap.injective_or_eq_zero F with hi | hz
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [hz, LinearMap.range_zero]; exact bot_le
  exact this ⟨σ.asModuleEquiv.symm s, rfl⟩

private theorem isoPick_sup {H Y : Type} {J : Sort*} [Group H] [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ H Y)
    (P : Submodule (MonoidAlgebra ℂ H) π.asModule) (A : J → Submodule ℂ Y)
    (h : ∀ j, ∀ v ∈ A j, π.asModuleEquiv.symm v ∈ P) (v : Y) (hv : v ∈ ⨆ j, A j) :
    π.asModuleEquiv.symm v ∈ P := by
  refine Submodule.iSup_induction _ (motive := fun z => π.asModuleEquiv.symm z ∈ P) hv h ?_ ?_
  · rw [map_zero]; exact zero_mem _
  · intro a b ha hb
    rw [map_add]; exact add_mem ha hb

private theorem isoPick_equiv {H S S' : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup S'] [Module ℂ S']
    (σ : Representation ℂ H S) (σ' : Representation ℂ H S')
    (e : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ'.asModule) : Nonempty (σ.Equiv σ') := by
  let F := (Representation.IntertwiningMap.equivLinearMapAsModule σ σ').symm e.toLinearMap
  let F' := (Representation.IntertwiningMap.equivLinearMapAsModule σ' σ).symm e.symm.toLinearMap
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear F.toLinearMap F'.toLinearMap ?_ ?_) fun g => ?_⟩
  · ext v
    exact e.apply_symm_apply (σ'.asModuleEquiv.symm v)
  · ext v
    exact e.symm_apply_apply (σ.asModuleEquiv.symm v)
  · exact LinearMap.ext fun v => F.isIntertwining _ _ g v

private theorem isoPick_hr {H S Y : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ H S) (π : Representation ℂ H Y) (hσ : σ.IsIrreducible)
    (P : Submodule (MonoidAlgebra ℂ H) π.asModule)
    (hP : isotypicComponent (MonoidAlgebra ℂ H) π.asModule σ.asModule ≤ P) (v : Y)
    (hv : v ∈ ⨆ f : {f : S →ₗ[ℂ] Y // ∀ g v, f (σ g v) = π g (f v)}, LinearMap.range f.1) :
    π.asModuleEquiv.symm v ∈ P := by
  refine isoPick_sup π P _ (fun f w hw => ?_) v hv
  obtain ⟨s, rfl⟩ := hw
  exact hP (isoPick_range σ π hσ f.1 f.2 s)

private theorem mem_iSup_isotypicComponent_of_span {H Y : Type} {I : Type 1} [Group H] [AddCommGroup Y] [Module ℂ Y] (V : I → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ H (V i)) (hρ : ∀ i, (ρ i).IsIrreducible)
    (π : Representation ℂ H Y)
    (hspan : ∀ y, y ∈ ⨆ (i : I) (f : {f : V i →ₗ[ℂ] Y // ∀ g v, f (ρ i g v) = π g (f v)}), LinearMap.range f.1)
    (y : Y) : π.asModuleEquiv.symm y ∈ ⨆ i, isotypicComponent (MonoidAlgebra ℂ H) π.asModule (ρ i).asModule :=
  isoPick_sup π _ _ (fun i v hv => isoPick_hr (ρ i) π (hρ i) _
    (le_iSup (fun i => isotypicComponent (MonoidAlgebra ℂ H) π.asModule (ρ i).asModule) i) v hv) y (hspan y)

private theorem mem_iSup_isotypic_of_not_iso {H Y : Type} {I : Type 1} [Group H] [AddCommGroup Y] [Module ℂ Y] (V : I → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ H (V i)) (hρ : ∀ i, (ρ i).IsIrreducible)
    (π : Representation ℂ H Y) (i₀ : I) (y : Y)
    (hy : y ∈ ⨆ (i : {i : I // IsEmpty ((ρ i₀).Equiv (ρ i))}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ g v, f (ρ i.1 g v) = π g (f v)}), LinearMap.range f.1) :
    π.asModuleEquiv.symm y ∈ ⨆ i : {i // IsEmpty ((ρ i₀).asModule ≃ₗ[MonoidAlgebra ℂ H] (ρ i).asModule)},
      isotypicComponent (MonoidAlgebra ℂ H) π.asModule (ρ i.1).asModule := by
  refine isoPick_sup π _ _ (fun i v hv => isoPick_hr (ρ i.1) π (hρ i.1) _ ?_ v hv) y hy
  refine le_iSup (fun i : {i // IsEmpty ((ρ i₀).asModule ≃ₗ[MonoidAlgebra ℂ H] (ρ i).asModule)} =>
    isotypicComponent (MonoidAlgebra ℂ H) π.asModule (ρ i.1).asModule) ⟨i.1, ⟨fun e => ?_⟩⟩
  obtain ⟨e'⟩ := isoPick_equiv _ _ e
  exact i.2.false e'

private theorem isoPick_gen {H Y : Type} {I : Type 1} [Group H] [AddCommGroup Y] [Module ℂ Y] (V : I → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (ρ : ∀ i, Representation ℂ H (V i)) (hρ : ∀ i, (ρ i).IsIrreducible)
    (π : Representation ℂ H Y)
    (hspan : ∀ y, y ∈ ⨆ (i : I) (f : {f : V i →ₗ[ℂ] Y // ∀ g v, f (ρ i g v) = π g (f v)}), LinearMap.range f.1)
    (y : Y) (hy : y ≠ 0) :
    ∃ i₀ : I, y ∉ ⨆ (i : {i : I // IsEmpty ((ρ i₀).Equiv (ρ i))}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ g v, f (ρ i.1 g v) = π g (f v)}), LinearMap.range f.1 := by
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra ℂ H) (ρ i).asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp (hρ i)
  have hne : π.asModuleEquiv.symm y ≠ 0 := fun h => hy (by simpa using congrArg π.asModuleEquiv h)
  obtain ⟨i₀, h⟩ := isoPick_mod (fun i => (ρ i).asModule) (π.asModuleEquiv.symm y) hne (mem_iSup_isotypicComponent_of_span V ρ hρ π hspan y)
  exact ⟨i₀, fun hy' => h (mem_iSup_isotypic_of_not_iso V ρ hρ π i₀ y hy')⟩

theorem UpperTheory.GalN.V.isoPick :
    ∀ (H Y : Type) (I : Type 1) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup Y] [Module ℂ Y] (σ : I → SmIrr H) (π : Representation ℂ H Y), (∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) → ∀ y : Y, y ≠ 0 → ∃ i₀ : I, y ∉ ⨆ (i : {i : I // IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)}) (f : {f : (σ i.1).V →ₗ[ℂ] Y // ∀ g v, f ((σ i.1).ρ g v) = π g (f v)}), LinearMap.range f.1 := by
  intro H Y I _ _ _ _ _ σ π hspan y hy
  exact isoPick_gen (fun i => (σ i).V) (fun i => (σ i).ρ) (fun i => (σ i).irred) π hspan y hy
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsoRefine
section
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Hi

section
variable {H Y Z : Type} {I : Type 1} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]

private theorem span_push (σ : I → SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H Z)
    (p : Y →ₗ[ℂ] Z) (hp : Function.Surjective p) (he : ∀ g v, p (π g v) = ρ g (p v))
    (hs : ∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) :
    ∀ z, z ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1 := by
  intro z
  obtain ⟨y, rfl⟩ := hp z
  have hle : (⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) ≤
      (⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1).comap p := by
    refine iSup_le fun i => iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    have h : LinearMap.range (p ∘ₗ f.1) ≤
        ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1 :=
      le_iSup_of_le i (le_iSup_of_le
        (⟨p ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply]; rw [f.2 g v, he]⟩ :
          {f : (σ i).V →ₗ[ℂ] Z // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}) le_rfl)
    exact h ⟨v, rfl⟩
  exact hle (hs y)

private theorem iso_push (τ : SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H Z)
    (p : Y →ₗ[ℂ] Z) (hp : Function.Surjective p) (he : ∀ g v, p (π g v) = ρ g (p v))
    (h : IsoSum π ⊤ τ) : IsoSum ρ ⊤ τ := by
  intro z _
  obtain ⟨y, rfl⟩ := hp z
  have hle : (⨆ f : {f : τ.V →ₗ[ℂ] Y // (∀ g v, f (τ.ρ g v) = π g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1) ≤
      (⨆ f : {f : τ.V →ₗ[ℂ] Z // (∀ g v, f (τ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1).comap p := by
    refine iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    have h' : LinearMap.range (p ∘ₗ f.1) ≤
        ⨆ f : {f : τ.V →ₗ[ℂ] Z // (∀ g v, f (τ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1 :=
      le_iSup_of_le
        (⟨p ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply]; rw [f.2.1 g v, he], le_top⟩ :
          {f : τ.V →ₗ[ℂ] Z // (∀ g v, f (τ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}) le_rfl
    exact h' ⟨v, rfl⟩
  exact hle (h Submodule.mem_top)

private theorem iso_quot (σ : I → SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H Z)
    (p : Y →ₗ[ℂ] Z) (hp : Function.Surjective p) (he : ∀ g v, p (π g v) = ρ g (p v))
    (hs : ∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1)
    (i₀ : I)
    (hk : (⨆ (i : {i : I // IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)})
      (f : {f : (σ i.1).V →ₗ[ℂ] Y // ∀ g v, f ((σ i.1).ρ g v) = π g (f v)}), LinearMap.range f.1) ≤ LinearMap.ker p) :
    IsoSum ρ ⊤ (σ i₀) := by
  intro z _
  obtain ⟨y, rfl⟩ := hp z
  have hle : (⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) ≤
      (⨆ f : {f : (σ i₀).V →ₗ[ℂ] Z // (∀ g v, f ((σ i₀).ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1).comap p := by
    refine iSup_le fun i => iSup_le fun f => ?_
    rintro _ ⟨v, rfl⟩
    by_cases hi : IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)
    · have h0 : f.1 v ∈ LinearMap.ker p :=
        hk (Submodule.mem_iSup_of_mem ⟨i, hi⟩ (Submodule.mem_iSup_of_mem ⟨f.1, f.2⟩ ⟨v, rfl⟩))
      rw [Submodule.mem_comap, LinearMap.mem_ker.1 h0]
      exact Submodule.zero_mem _
    · obtain ⟨e⟩ := not_isEmpty_iff.1 hi
      have h' : LinearMap.range (p ∘ₗ f.1 ∘ₗ e.toLinearEquiv.toLinearMap) ≤
          ⨆ f : {f : (σ i₀).V →ₗ[ℂ] Z // (∀ g v, f ((σ i₀).ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}, LinearMap.range f.1 :=
        le_iSup_of_le
          (⟨p ∘ₗ f.1 ∘ₗ e.toLinearEquiv.toLinearMap, fun g v => by
            have h1 := (congrArg f.1 (e.toIntertwiningMap.isIntertwining _ _ g v)).trans (f.2 g _)
            exact (congrArg p h1).trans (he g _), le_top⟩ :
            {f : (σ i₀).V →ₗ[ℂ] Z // (∀ g v, f ((σ i₀).ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ ⊤}) le_rfl
      refine h' ⟨e.toLinearEquiv.symm v, ?_⟩
      exact congrArg (fun w => p (f.1 w)) (e.toLinearEquiv.apply_symm_apply v)
  exact hle (hs y)

end

private theorem stab_N {Q : Type} [Finite Q] [DecidableEq Q] {H : Q → Type} [∀ q, Group (H q)]
    {Y : Type} {I : Type 1} [AddCommGroup Y] [Module ℂ Y] (q : Q) (V : I → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (τ : ∀ i, Representation ℂ (H q) (V i))
    (π : Representation ℂ (∀ q, H q) Y) (P : I → Prop) (g : ∀ q, H q) :
    (⨆ (i : {i : I // P i}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ h v, f (τ i.1 h v) = π (Pi.mulSingle q h) (f v)}),
      LinearMap.range f.1) ≤
    (⨆ (i : {i : I // P i}) (f : {f : V i.1 →ₗ[ℂ] Y // ∀ h v, f (τ i.1 h v) = π (Pi.mulSingle q h) (f v)}),
      LinearMap.range f.1).comap (π g) := by
  set N : Submodule ℂ Y := ⨆ (i : {i : I // P i})
    (f : {f : V i.1 →ₗ[ℂ] Y // ∀ h v, f (τ i.1 h v) = π (Pi.mulSingle q h) (f v)}), LinearMap.range f.1 with hN
  let S : Submonoid (∀ q, H q) :=
    { carrier := {g | N ≤ N.comap (π g)}
      one_mem' := fun n hn => by simpa using hn
      mul_mem' := fun {a b} ha hb n hn => by
        have : π (a * b) n = π a (π b n) := by rw [map_mul]; rfl
        rw [Submodule.mem_comap, this]
        exact ha (hb hn) }
  refine Submonoid.pi_mem_of_mulSingle_mem (H := S) g fun q' => ?_
  show N ≤ N.comap (π (Pi.mulSingle q' (g q')))
  refine iSup_le fun i => iSup_le fun f => ?_
  rintro _ ⟨v, rfl⟩
  by_cases hq : q' = q
  · subst hq
    rw [Submodule.mem_comap, ← f.2 (g q') v]
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem f ⟨_, rfl⟩)
  · have hc : ∀ (h : H q) (x : Y), π (Pi.mulSingle q' (g q')) (π (Pi.mulSingle q h) x) =
        π (Pi.mulSingle q h) (π (Pi.mulSingle q' (g q')) x) := fun h x => by
      have h1 : π (Pi.mulSingle q' (g q') * Pi.mulSingle q h) x = π (Pi.mulSingle q h * Pi.mulSingle q' (g q')) x := by
        rw [(Pi.mulSingle_commute hq (g q') h).eq]
      rw [map_mul, map_mul] at h1
      exact h1
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem
      ⟨π (Pi.mulSingle q' (g q')) ∘ₗ f.1, fun h w => by
        simp only [LinearMap.comp_apply]
        rw [f.2 h w, hc]⟩ ⟨v, rfl⟩)

theorem UpperTheory.GalN.V.isoRefine :
        (∀ (H Y : Type) (I : Type 1) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup Y] [Module ℂ Y] (σ : I → SmIrr H) (π : Representation ℂ H Y), (∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1) → ∀ y : Y, y ≠ 0 → ∃ i₀ : I, y ∉ ⨆ (i : {i : I // IsEmpty ((σ i₀).ρ.Equiv (σ i).ρ)}) (f : {f : (σ i.1).V →ₗ[ℂ] Y // ∀ g v, f ((σ i.1).ρ g v) = π g (f v)}), LinearMap.range f.1) → ∀ (Q : Type) [Finite Q] [DecidableEq Q] (H : Q → Type) [∀ q, Group (H q)] [∀ q, TopologicalSpace (H q)] [∀ q, IsTopologicalGroup (H q)] (Y : Type) (I : Type 1) [AddCommGroup Y] [Module ℂ Y] (σ : I → ∀ q, SmIrr (H q)) (π : Representation ℂ (∀ q, H q) Y), (∀ q y, y ∈ ⨆ (i : I) (f : {f : (σ i q).V →ₗ[ℂ] Y // ∀ g v, f ((σ i q).ρ g v) = π (Pi.mulSingle q g) (f v)}), LinearMap.range f.1) → ∀ y : Y, y ≠ 0 → ∃ (Y' : Type) (_ : AddCommGroup Y') (_ : Module ℂ Y') (π' : Representation ℂ (∀ q, H q) Y') (p : Y →ₗ[ℂ] Y') (c : Q → I), p y ≠ 0 ∧ (∀ g v, p (π g v) = π' g (p v)) ∧ ∀ q, IsoSum (π'.comp (MonoidHom.mulSingle H q)) ⊤ (σ (c q) q) := by
  intro hPick Q _ _ H _ _ _ Y I _ _ σ π hs y hy
  haveI := Fintype.ofFinite Q
  have key : ∀ T : Finset Q, ∃ (Y' : Type) (_ : AddCommGroup Y') (_ : Module ℂ Y')
      (π' : Representation ℂ (∀ q, H q) Y') (p : Y →ₗ[ℂ] Y') (c : Q → I),
      Function.Surjective p ∧ p y ≠ 0 ∧ (∀ g v, p (π g v) = π' g (p v)) ∧
      (∀ q ∈ T, IsoSum (π'.comp (MonoidHom.mulSingle H q)) ⊤ (σ (c q) q)) ∧
      (∀ q y, y ∈ ⨆ (i : I) (f : {f : (σ i q).V →ₗ[ℂ] Y' // ∀ g v, f ((σ i q).ρ g v) = π' (Pi.mulSingle q g) (f v)}), LinearMap.range f.1) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      exact ⟨Y, _, _, π, LinearMap.id,
        fun q => (hPick (H q) Y I (fun i => σ i q) (π.comp (MonoidHom.mulSingle H q)) (hs q) y hy).choose,
        Function.surjective_id, hy, fun _ _ => rfl, by simp, hs⟩
    | insert q T hq ih =>
      obtain ⟨Y', _, _, π', p, c, hsurj, hpy, he, hiso, hsp⟩ := ih
      obtain ⟨i₀, hi₀⟩ := hPick (H q) Y' I (fun i => σ i q) (π'.comp (MonoidHom.mulSingle H q)) (hsp q) (p y) hpy
      set N : Submodule ℂ Y' := ⨆ (i : {i : I // IsEmpty ((σ i₀ q).ρ.Equiv (σ i q).ρ)})
        (f : {f : (σ i.1 q).V →ₗ[ℂ] Y' // ∀ g v, f ((σ i.1 q).ρ g v) = π' (Pi.mulSingle q g) (f v)}),
        LinearMap.range f.1 with hNdef
      have hi₀' : p y ∉ N := hi₀
      have hN : ∀ g, N ≤ N.comap (π' g) := fun g =>
        stab_N q (fun i => (σ i q).V) (fun i => (σ i q).ρ) π' (fun i => IsEmpty ((σ i₀ q).ρ.Equiv (σ i q).ρ)) g
      have hmk : ∀ g v, N.mkQ (π' g v) = π'.quotient N hN g (N.mkQ v) := fun g v => rfl
      refine ⟨Y' ⧸ N, inferInstance, inferInstance, π'.quotient N hN, N.mkQ ∘ₗ p, Function.update c q i₀,
        (N.mkQ_surjective).comp hsurj, ?_, ?_, ?_, ?_⟩
      · simpa using hi₀'
      · intro g v
        simp only [LinearMap.comp_apply]
        rw [he, hmk]
      · intro q' hq'
        rcases Finset.mem_insert.1 hq' with rfl | hq'
        · rw [Function.update_self]
          exact iso_quot (fun i => σ i q') (π'.comp (MonoidHom.mulSingle H q'))
            ((π'.quotient N hN).comp (MonoidHom.mulSingle H q')) N.mkQ N.mkQ_surjective
            (fun g v => hmk _ v) (hsp q') i₀ (by rw [Submodule.ker_mkQ]; exact le_rfl)
        · have hne : q' ≠ q := fun h => hq (h ▸ hq')
          rw [Function.update_of_ne hne]
          exact iso_push _ (π'.comp (MonoidHom.mulSingle H q'))
            ((π'.quotient N hN).comp (MonoidHom.mulSingle H q')) N.mkQ N.mkQ_surjective
            (fun g v => hmk _ v) (hiso q' hq')
      · intro q'
        exact span_push (fun i => σ i q') (π'.comp (MonoidHom.mulSingle H q'))
          ((π'.quotient N hN).comp (MonoidHom.mulSingle H q')) N.mkQ N.mkQ_surjective
          (fun g v => hmk _ v) (hsp q')
  obtain ⟨Y', i1, i2, π', p, c, -, hpy, he, hiso, -⟩ := key Finset.univ
  exact ⟨Y', i1, i2, π', p, c, hpy, he, fun q => hiso q (Finset.mem_univ q)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsoSub
section
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Hi

private theorem irreducible_subrep_isotypic {H Y V : Type} {I : Type 1} {S : I → Type} [Group H] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup V] [Module ℂ V] [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
    (σ : ∀ i, Representation ℂ H (S i)) (hσ : ∀ i, (σ i).IsIrreducible)
    (π : Representation ℂ H Y) (ρ : Representation ℂ H V) (j : Y →ₗ[ℂ] V) (hj : Function.Injective j)
    (he : ∀ g y, j (π g y) = ρ g (j y))
    (h : ∀ y, j y ∈ ⨆ (i : I) (f : {f : S i →ₗ[ℂ] V // ∀ g v, f (σ i g v) = ρ g (f v)}), LinearMap.range f.1)
    (y : Y) :
    y ∈ ⨆ (i : I) (f : {f : S i →ₗ[ℂ] Y // ∀ g v, f (σ i g v) = π g (f v)}), LinearMap.range f.1 := by
  let R := MonoidAlgebra ℂ H
  haveI hsim : ∀ i, IsSimpleModule R (σ i).asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule (σ i)).mp (hσ i)
  let J : π.asModule →ₗ[R] ρ.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule π ρ ⟨j, fun g => LinearMap.ext (he g)⟩
  let s : Set (Submodule R ρ.asModule) := {m | ∃ i, Nonempty (m ≃ₗ[R] (σ i).asModule)}
  haveI hs : ∀ m : s, IsSimpleModule R m := by
    rintro ⟨m, i, ⟨e⟩⟩
    exact IsSimpleModule.congr e
  have h1 : ∀ v ∈ ⨆ (i : I) (f : {f : S i →ₗ[ℂ] V // ∀ g v, f (σ i g v) = ρ g (f v)}), LinearMap.range f.1,
      ρ.asModuleEquiv.symm v ∈ sSup s := by
    intro v hv
    refine Submodule.iSup_induction _ (motive := fun z => ρ.asModuleEquiv.symm z ∈ sSup s) hv ?_ ?_ ?_
    · intro i v hv
      refine Submodule.iSup_induction _ (motive := fun z => ρ.asModuleEquiv.symm z ∈ sSup s) hv ?_ ?_ ?_
      · rintro f _ ⟨t, rfl⟩
        let F : (σ i).asModule →ₗ[R] ρ.asModule :=
          Representation.IntertwiningMap.equivLinearMapAsModule (σ i) ρ ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩
        have : LinearMap.range F ≤ sSup s := by
          rcases LinearMap.injective_or_eq_zero F with hi | hz
          · exact le_sSup ⟨i, ⟨(LinearEquiv.ofInjective _ hi).symm⟩⟩
          · rw [hz, LinearMap.range_zero]; exact bot_le
        exact this ⟨(σ i).asModuleEquiv.symm t, rfl⟩
      · rw [map_zero]; exact zero_mem _
      · intro a b ha hb
        rw [map_add]; exact add_mem ha hb
    · rw [map_zero]; exact zero_mem _
    · intro a b ha hb
      rw [map_add]; exact add_mem ha hb
  have hJ : ∀ x, J x ∈ sSup s := fun x => h1 _ (h (π.asModuleEquiv x))
  have hJi : Function.Injective J := hj
  haveI : IsSemisimpleModule R (sSup s : Submodule R ρ.asModule) := by
    rw [sSup_eq_iSup]
    exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm =>
      haveI := hs ⟨m, hm⟩
      inferInstance
  let J' : π.asModule →ₗ[R] (sSup s : Submodule R ρ.asModule) := J.codRestrict _ hJ
  have hJ' : Function.Injective J' := fun a b hab => hJi (congrArg Subtype.val hab)
  haveI : IsSemisimpleModule R π.asModule := IsSemisimpleModule.of_injective J' hJ'
  have h3 : π.asModuleEquiv.symm y ∈ sSup {m : Submodule R π.asModule | IsSimpleModule R m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]; trivial
  rw [sSup_eq_iSup'] at h3
  rw [← π.asModuleEquiv.apply_symm_apply y]
  refine Submodule.iSup_induction _ (motive := fun z => π.asModuleEquiv z ∈ _) h3 ?_ ?_ ?_
  · rintro ⟨m, hm⟩ z hz
    haveI : IsSimpleModule R m := hm
    let e0 : m ≃ₗ[R] m.map J := Submodule.equivMapOfInjective J hJi m
    haveI : IsSimpleModule R (m.map J) := IsSimpleModule.congr e0.symm
    have hle : m.map J ≤ sSup s := by
      rintro _ ⟨x, -, rfl⟩
      exact hJ x
    obtain ⟨n, ⟨i, ⟨e2⟩⟩, ⟨e1⟩⟩ := (m.map J).linearEquiv_of_le_sSup s hle
    let e : m ≃ₗ[R] (σ i).asModule := (e0.trans e1).trans e2
    let F := (Representation.IntertwiningMap.equivLinearMapAsModule (σ i) π).symm (m.subtype ∘ₗ e.symm.toLinearMap)
    refine Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem ⟨F.toLinearMap, F.isIntertwining⟩ ⟨(σ i).asModuleEquiv (e ⟨z, hz⟩), ?_⟩)
    exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)
  · rw [map_zero]; exact zero_mem _
  · intro a b ha hb
    rw [map_add]; exact add_mem ha hb

theorem UpperTheory.GalN.V.isoSub :
    ∀ (H Y V : Type) (I : Type 1) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup V] [Module ℂ V] (σ : I → SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H V) (j : Y →ₗ[ℂ] V), Function.Injective j → (∀ g y, j (π g y) = ρ g (j y)) → (∀ y, j y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] V // ∀ g v, f ((σ i).ρ g v) = ρ g (f v)}), LinearMap.range f.1) → ∀ y, y ∈ ⨆ (i : I) (f : {f : (σ i).V →ₗ[ℂ] Y // ∀ g v, f ((σ i).ρ g v) = π g (f v)}), LinearMap.range f.1 := by
  intro H Y V I _ _ _ _ _ _ _ σ π ρ j hj he h y
  exact irreducible_subrep_isotypic (fun i => (σ i).ρ) (fun i => (σ i).irred) π ρ j hj he h y
end

