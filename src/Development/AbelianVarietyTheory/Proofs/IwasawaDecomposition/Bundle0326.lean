module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInner
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0110
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicModularFormsIrreducibleDecomposition
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutReps

variable {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem comap_ne_bot_iff {f : M →ₗ[ℂ] N} (hf : Function.Injective f) (A : Submodule ℂ N) :
    A.comap f ≠ ⊥ ↔ A ⊓ LinearMap.range f ≠ ⊥ := by
  rw [inf_comm, ← Submodule.map_comap_eq, not_iff_not]
  constructor
  · intro h; rw [h, Submodule.map_bot]
  · intro h
    exact Submodule.map_injective_of_injective hf (by rw [h, Submodule.map_bot])

theorem iSupIndep_comap {ι : Type} {f : M →ₗ[ℂ] N} (hf : Function.Injective f) {A : ι → Submodule ℂ N}
    (hA : iSupIndep A) : iSupIndep (fun i => (A i).comap f) := by
  intro i
  rw [disjoint_iff]
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
  have h3 : f x ∈ ⨆ j, ⨆ (_ : j ≠ i), A j := by
    have hle : (⨆ j, ⨆ (_ : j ≠ i), (A j).comap f) ≤ (⨆ j, ⨆ (_ : j ≠ i), A j).comap f := by
      apply iSup_le; intro j; apply iSup_le; intro hj
      exact Submodule.comap_mono (le_iSup₂_of_le j hj le_rfl)
    exact hle h2
  have h4 : f x ∈ A i ⊓ ⨆ j, ⨆ (_ : j ≠ i), A j := Submodule.mem_inf.mpr ⟨h1, h3⟩
  rw [disjoint_iff.mp (hA i)] at h4
  have : f x = 0 := (Submodule.mem_bot ℂ).mp h4
  exact (Submodule.mem_bot ℂ).mpr (hf (this.trans (map_zero f).symm))

theorem iSup_comap_eq_top {ι : Type} {f : M →ₗ[ℂ] N} (hf : Function.Injective f) {A : ι → Submodule ℂ N}
    (hA : ⨆ i, A i ⊓ LinearMap.range f = LinearMap.range f) : ⨆ i, (A i).comap f = ⊤ := by
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_iSup, Submodule.map_top]
  simp_rw [Submodule.map_comap_eq]
  simpa only [inf_comm] using hA

end GlobalTheory.AutReps

theorem GlobalTheory.AutReps.mtReal_decomp : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j), ∃ (ι : Type) (_ : Finite ι) (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), (∀ P, NG.IsIrrRep Mr.wt.ρ (F P)) ∧ (∀ P P', NG.IsoRep (F P) (F P') → P = P') ∧ (∀ S', NG.IsIrrRep Mr.wt.ρ S' → (NG.isoTyp Mr.wt.ρ S').comap Mr.real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') ∧ (∀ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real ≠ ⊥) ∧ iSupIndep (fun P => (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real) ∧ ⨆ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real = ⊤ := by
  intro D μ j Mr
  obtain ⟨_, ι, hι, S, hirr, hinj, hsurj, hne, hind, hsup⟩ :=
    _root_.GlobalTheory.CompRed.typeSp_decomp D.host.E D.R.nV Mr.wt Mr.J Mr.χ Mr.J_open
  have hR := Mr.real_range
  refine ⟨ι, hι, S, hirr, hinj, ?_, ?_, ?_, ?_⟩
  · intro S' h1 h2
    apply hsurj S' h1
    rw [← hR]; exact (GlobalTheory.AutReps.comap_ne_bot_iff Mr.real_inj _).mp h2
  · intro P
    rw [GlobalTheory.AutReps.comap_ne_bot_iff Mr.real_inj, hR]; exact hne P
  · exact GlobalTheory.AutReps.iSupIndep_comap Mr.real_inj hind
  · apply GlobalTheory.AutReps.iSup_comap_eq_top Mr.real_inj
    rw [hR]; exact hsup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicMultiplicityEqOfIso
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MultIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem mem_AFall_iff {ρ : Representation ℂ (GQ L n) W} {f : GAf L n → W} :
    f ∈ NG.AFall L n ρ ↔ (∀ (γ : GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
      ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g := Iff.rfl

theorem mem_HomG_iff {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    {Φ : S →ₗ[ℂ] (GAf L n → W)} :
    Φ ∈ NG.HomG ρ S ↔ (∀ f, Φ f ∈ NG.AFall L n ρ) ∧ ∀ (h : GAf L n) (f f' : S),
      (f' : GAf L n → W) = NG.rt L n h (f : GAf L n → W) → Φ f' = NG.rt L n h (Φ f) := Iff.rfl

theorem comp_mem_AFall {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x)) {f : GAf L n → W} (hf : f ∈ NG.AFall L n ρ) :
    (fun g => A (f g)) ∈ NG.AFall L n ρ' := by
  obtain ⟨h1, N, hN, h2⟩ := mem_AFall_iff.1 hf
  exact mem_AFall_iff.2 ⟨fun γ g => by simp only [h1 γ g, hA], N, hN, fun κ hκ g => by simp only [h2 κ hκ g]⟩

def transport {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x))
    (T : S' →ₗ[ℂ] S) (hT : ∀ (h : GAf L n) (f f' : S'), (f' : GAf L n → W') = NG.rt L n h (f : GAf L n → W') →
      ((T f' : S) : GAf L n → W) = NG.rt L n h ((T f : S) : GAf L n → W)) :
    NG.HomG ρ S →ₗ[ℂ] NG.HomG ρ' S' where
  toFun Φ := ⟨(LinearMap.compLeft A (GAf L n)).comp ((Φ : S →ₗ[ℂ] (GAf L n → W)).comp T), mem_HomG_iff.2
     ⟨fun f => comp_mem_AFall A hA ((mem_HomG_iff.1 Φ.2).1 (T f)),
      fun h f f' e => by
        have := (mem_HomG_iff.1 Φ.2).2 h (T f) (T f') (hT h f f' e)
        simp only [LinearMap.comp_apply]
        rw [this]
        rfl⟩⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    apply LinearMap.ext; intro x; funext g
    simp
  map_smul' c Φ := by
    apply Subtype.ext
    apply LinearMap.ext; intro x; funext g
    simp

theorem transport_apply {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x))
    (T : S' →ₗ[ℂ] S) (hT : ∀ (h : GAf L n) (f f' : S'), (f' : GAf L n → W') = NG.rt L n h (f : GAf L n → W') →
      ((T f' : S) : GAf L n → W) = NG.rt L n h ((T f : S) : GAf L n → W)) (Φ : NG.HomG ρ S) (x : S') (g : GAf L n) :
    ((transport A hA T hT Φ : S' →ₗ[ℂ] (GAf L n → W')) x) g = A ((Φ : S →ₗ[ℂ] (GAf L n → W)) (T x) g) := rfl

theorem mult_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n),
    π.Iso π' → π.mult = π'.mult := by
  rintro L _ _ _ n π π' ⟨⟨A, hA⟩, ⟨T, hT⟩⟩
  have hTs : ∀ (h : GAf L n) (g g' : π'.S), (g' : GAf L n → π'.W) = NG.rt L n h (g : GAf L n → π'.W) →
      ((T.symm g' : π.S) : GAf L n → π.W) = NG.rt L n h ((T.symm g : π.S) : GAf L n → π.W) := by
    intro h g g' hg
    have key := hT h (T.symm g) ⟨NG.rt L n h (T.symm g : GAf L n → π.W), π.irrS.1.stable h _ (T.symm g).2⟩ rfl
    rw [LinearEquiv.apply_symm_apply, ← hg] at key
    have e2 : T ⟨NG.rt L n h (T.symm g : GAf L n → π.W), π.irrS.1.stable h _ (T.symm g).2⟩ = g' := Subtype.ext key
    rw [← e2, LinearEquiv.symm_apply_apply]
  have hAs : ∀ γ x, A.symm (π'.ρ γ x) = π.ρ γ (A.symm x) := by
    intro γ x
    apply A.injective
    rw [LinearEquiv.apply_symm_apply, hA, LinearEquiv.apply_symm_apply]
  let F := transport (ρ := π.ρ) (ρ' := π'.ρ) A.toLinearMap hA T.symm.toLinearMap hTs
  let G := transport (ρ := π'.ρ) (ρ' := π.ρ) A.symm.toLinearMap hAs T.toLinearMap hT
  let e : NG.HomG π.ρ π.S ≃ₗ[ℂ] NG.HomG π'.ρ π'.S := LinearEquiv.ofLinear F G
    (by
      apply LinearMap.ext; intro Ψ
      apply Subtype.ext; apply LinearMap.ext; intro x; funext g
      simp [F, G, transport_apply])
    (by
      apply LinearMap.ext; intro Ψ
      apply Subtype.ext; apply LinearMap.ext; intro x; funext g
      simp [F, G, transport_apply])
  exact e.finrank_eq

end GlobalTheory.MultIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicRepCmQuotientModel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.AutModel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def compE (e : W ≃ₗ[ℂ] W') : (GAf L n → W) ≃ₗ[ℂ] (GAf L n → W') :=
  LinearEquiv.piCongrRight fun _ => e

theorem compE_symm (e : W ≃ₗ[ℂ] W') : compE (L := L) (n := n) e.symm = (compE e).symm :=
  LinearEquiv.ext fun _ => rfl

theorem rt_compE (e : W ≃ₗ[ℂ] W') (h : GAf L n) (f : GAf L n → W) :
    NG.rt L n h (compE e f) = compE e (NG.rt L n h f) := rfl

def conjRep (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) : Representation ℂ (GQ L n) W' where
  toFun γ := e.toLinearMap ∘ₗ ρ γ ∘ₗ e.symm.toLinearMap
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

theorem conjRep_apply (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W') :
    conjRep e ρ γ x = e (ρ γ (e.symm x)) := rfl

theorem conjRep_inter (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W) :
    e (ρ γ x) = conjRep e ρ γ (e x) := by simp [conjRep_apply]

theorem isSubrep_map (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (he : ∀ γ x, e (ρ γ x) = ρ' γ (e x)) {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S) :
    NG.IsSubrep ρ' (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨h1, N, hN, h2⟩ := hS.le hf
    refine ⟨fun γ g => ?_, N, hN, fun κ hκ g => ?_⟩
    · change e (f (γ * g)) = ρ' γ (e (f g))
      rw [h1 γ g, he]
    · change e (f (g * κ)) = e (f g)
      rw [h2 κ hκ g]
  · rintro h _ ⟨f, hf, rfl⟩
    exact ⟨NG.rt L n h f, hS.stable h f hf, rfl⟩

theorem isIrrRep_map (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (he : ∀ γ x, e (ρ γ x) = ρ' γ (e x)) {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S) :
    NG.IsIrrRep ρ' (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  have he' : ∀ γ y, e.symm (ρ' γ y) = ρ γ (e.symm y) := fun γ y => by
    apply e.injective; rw [he]; simp
  obtain ⟨hsub, hne, hmin⟩ := hS
  refine ⟨isSubrep_map e he hsub, ?_, fun S' hS' hle => ?_⟩
  · intro h0
    apply hne
    have := congrArg (Submodule.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) h0
    rwa [Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective, Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr (compE (L := L) (n := n) e).injective] at this
  · set T := S'.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) with hT
    have hTm : T = S'.map (compE (L := L) (n := n) e.symm : (GAf L n → W') →ₗ[ℂ] (GAf L n → W)) := by
      rw [compE_symm, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm]
    have hTs : NG.IsSubrep ρ T := hTm ▸ isSubrep_map e.symm he' hS'
    have hTle : T ≤ S := by
      have := Submodule.comap_mono (f := (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) hle
      rwa [Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective] at this
    have hS'eq : S' = T.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) := by
      rw [hT, Submodule.map_comap_eq_of_surjective (compE (L := L) (n := n) e).surjective]
    rcases hmin T hTs hTle with h | h
    · left; rw [hS'eq, h, Submodule.map_bot]
    · right; rw [hS'eq, h]

theorem isoRep_map (e : W ≃ₗ[ℂ] W') (S : Submodule ℂ (GAf L n → W)) :
    NG.IsoRep S (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  refine ⟨(compE e).submoduleMap S, fun h f f' hf => ?_⟩
  simp only [LinearEquiv.submoduleMap_apply]
  rw [hf, rt_compE]

omit [Field L] [NumberField L] [IsCMField L] in
theorem irr_iff {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SubrepTopBot.main
  | exact _root_.GlobalTheory.SubrepTopBot.main
  | (apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubrepTopBot.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubrepTopBot.main ..)

theorem irr_conj (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} (h : ρ.IsIrreducible) :
    (conjRep e ρ).IsIrreducible := by
  rw [irr_iff] at h ⊢
  obtain ⟨hW, hmin⟩ := h
  refine ⟨e.symm.surjective.nontrivial, fun U' hU' => ?_⟩
  have hU : ∀ γ, ∀ x ∈ U'.comap (e : W →ₗ[ℂ] W'), ρ γ x ∈ U'.comap (e : W →ₗ[ℂ] W') := by
    intro γ x hx
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
    rw [conjRep_inter]; exact hU' γ _ hx
  have hback : U' = (U'.comap (e : W →ₗ[ℂ] W')).map (e : W →ₗ[ℂ] W') :=
    (Submodule.map_comap_eq_of_surjective e.surjective U').symm
  rcases hmin _ hU with h0 | h0
  · left; rw [hback, h0, Submodule.map_bot]
  · right; rw [hback, h0, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

theorem alg_conj (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} (h : IsAlgWeight L n ρ)
    [FiniteDimensional ℂ W'] : IsAlgWeight L n (conjRep e ρ) := by
  obtain ⟨-, ι, hι, hd, b, P, hP⟩ := h
  refine ⟨inferInstance, ι, hι, hd, b.map e, P, fun γ γ₀ hγ => ?_⟩
  rw [← hP γ γ₀ hγ]
  ext i j
  simp [LinearMap.toMatrix_apply, conjRep_apply]

theorem exists_autRepM (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) :
    ∃ m : GlobalTheory.AutQuot.AutRepM L n, π.Iso m.toAutRep := by
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  let e : π.W ≃ₗ[ℂ] (Fin (Module.finrank ℂ π.W) → ℂ) := (Module.finBasis ℂ π.W).equivFun
  let m : GlobalTheory.AutQuot.AutRepM L n :=
    { d := Module.finrank ℂ π.W
      ρ := conjRep e π.ρ
      alg := alg_conj e π.alg
      irr := irr_conj e π.irr
      S := π.S.map (compE (L := L) (n := n) e : (GAf L n → π.W) →ₗ[ℂ] (GAf L n → _))
      irrS := isIrrRep_map e (conjRep_inter e π.ρ) π.irrS }
  exact ⟨m, ⟨e, conjRep_inter e π.ρ⟩, isoRep_map e π.S⟩

end GlobalTheory.AutModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPrimePlacesNonempty
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PdPlace

theorem exists_place_over_prime (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (Formalism.BasicNotions.placesOver E p).Nonempty := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro hu
    have h1 := hu.map (Algebra.norm ℤ : 𝓞 E →* ℤ)
    rw [show ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) by simp, Algebra.norm_algebraMap] at h1
    have h2 := Int.isUnit_iff_natAbs_eq.1 h1
    have h3 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h2
    rcases Nat.pow_eq_one.1 h2 with h | h
    · exact hp.one_lt.ne' h
    · exact h3.ne' h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hmem⟩
  rw [h, Ideal.mem_bot] at hmem
  exact hp.ne_zero (by exact_mod_cast hmem)

theorem pD_nonempty : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw), (T.pD i).Nonempty := by
  intro D T i
  have hp : (if T.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
    split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  obtain ⟨v, hv⟩ := exists_place_over_prime D.host.E _ hp
  rw [← T.pD_eq i] at hv
  exact ⟨v, hv⟩

end GlobalTheory.PdPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEqStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_char_eq_of_inertia_condition : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (ϖ : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ π : Ω, π ^ m = algebraMap E Ω (ϖ : E) → ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, σ π = σ' π → χ σ = χ σ' := by
  first | exact @GlobalTheory.TameTau.char_eq_of_apply_root_eq | exact GlobalTheory.TameTau.char_eq_of_apply_root_eq | (intros; apply GlobalTheory.TameTau.char_eq_of_apply_root_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

def castQ {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : Qbar p ≃+* Qbar q := by
  subst h; exact RingEquiv.refl _

theorem exists_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) : ∃ z' : ℤ_[q], HEq z z' := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem castQ_alg {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) (z' : ℤ_[q]) (hz : HEq z z') :
    (castQ h).symm (algebraMap ℚ_[q] (Qbar q) (z' : ℚ_[q])) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := by
  subst h
  obtain rfl := eq_of_heq hz
  rfl

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {n : ℕ} (f : A →+* B)
    (g : B →+* C) (ρ : Γ →* GL (Fin n) A) : mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  ext x i j
  rfl

theorem isRepOf_cast (D : D7) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar q ≃+* ℂ) {n : ℕ}
    (π : D.naut.CG n) (s : ℝ) (ρ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar q))
    (hρ : IsRepOf D p ((castQ h).trans ι) π s (mapRep (castQ h).symm.toRingHom ρ)) : IsRepOf D q ι π s ρ := by
  subst h
  have e1 : (castQ (rfl : p = p)).trans ι = ι := by ext x; rfl
  have e2 : mapRep (castQ (rfl : p = p)).symm.toRingHom ρ = ρ := by ext g i j; rfl
  rw [e1, e2] at hρ
  exact hρ

theorem conj_of_isRepOf (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₁ : IsRepOf D l ι π s ρ₁) (h₂ : IsRepOf D l ι π s ρ₂) : IsConjRep ρ₁ ρ₂ := by
  obtain ⟨c₁, s₁, f₁⟩ := h₁
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, -, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 B g hB hg, hw.2 B g hB hg])
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₂ ρ₁ s₂ s₁ (fun g => (hcp g).symm)
  exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) : M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq]
  rfl

theorem rhoOfRow_isRepOf (D : D7) (hG : GalRepEx D) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc)
    (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    IsRepOf D (D.nd.l a) (D.naut.iotaQC a) (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
      (rhoOfRow D hG hC hη a π hc hr) := by
  obtain ⟨c1, ss1, f1⟩ := rowRho_spec D hG a π hc hr
  obtain ⟨cχ, awayχ, -⟩ := Classical.choose_spec (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη)
  set χ1 := Classical.choose (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη) with hχ1
  have e0 : rhoOfRow D hG hC hη a π hc hr =
      Formalism.MainNotions.SumRepresentations.At.twGL (rowRho D hG a π hc hr) (Matrix.GeneralLinearGroup.det.comp χ1) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; exact GlobalTheory.TwistLG.cont_twGL _ _ c1 cχ
  · rw [e0]; exact GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1
  have hfin := placesOver_finite D.host.E (D.nd.l a) (Fact.out : (D.nd.l a).Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : w ∉ placesOver D.host.E (D.nd.l a) := hwl

  have hue : D.naut.unr (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) :=
    (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  obtain ⟨u, hu1⟩ : ∃ u, D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    apply Multiset.card_eq_one.mp
    rw [D.naut.frobEig_tw _ _ (D.naut.etaTinv_def w).1, Multiset.card_map,
      D.naut.frobEig_card _ (D.naut.etaTinv_def w).1, D.naut.locG_dim]
  have hwd := D.naut.wdOf_frob a χ1 w hwl' cχ (by rw [awayχ w hwl']; exact hue) B σ hB hσ
  rw [awayχ w hwl', hu1, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C] at hwd
  have hχu : D.naut.iotaQC a ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) : Qbar (D.nd.l a)) = u := by
    have := congrArg (fun p : Polynomial ℂ => p.coeff 0) hwd
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, neg_inj] at this
    show D.naut.iotaQC a ((χ1 σ : Matrix (Fin 1) (Fin 1) _).det) = u
    rw [Matrix.det_unique]
    exact this

  have h1 := hw1 B σ hB hσ
  rw [isoLoc_single] at h1
  rw [e0, GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((rowRho D hG a π hc hr) σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map
      (D.naut.iotaQC a).toRingHom).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : (D.naut.iotaQC a).toRingHom ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) :
      Qbar (D.nd.l a)) = u := hχu
  rw [hχu']
  exact h3

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

theorem fracMap_eq {O0 O : Type} [CommRing O0] [IsDomain O0] [ValuationRing O0] [CommRing O] [IsDomain O]
    (f : O0 →+* O) (hf : Function.Injective f) {F : Type} [Field F] (e : F →+* FractionRing O0)
    (e' : F →+* FractionRing O) (h : ∀ x y, algebraMap O0 _ y = e x → e' x = algebraMap O _ (f y)) (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf (e x) = e' x := by
  rcases ValuationRing.isInteger_or_isInteger O0 (e x) with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, h x y hy]
  · have hy' : algebraMap O0 (FractionRing O0) y = e x⁻¹ := by rw [map_inv₀]; exact hy
    have h1 := h x⁻¹ y hy'
    have h2 : e x = (algebraMap O0 (FractionRing O0) y)⁻¹ := by rw [hy, inv_inv]
    rw [h2, map_inv₀, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, ← h1, map_inv₀, inv_inv]

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR


end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting


end GlobalTheory.HeightCounting
end
end

