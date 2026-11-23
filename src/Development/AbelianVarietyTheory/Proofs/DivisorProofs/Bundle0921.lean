module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlaces
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open scoped Pointwise

noncomputable section

namespace GlobalTheory.SUSuppCompact

theorem isCompact_SUSupp_of_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (∀ w ∈ S₁, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g = JR w.Completion J → ∀ i j, g i j ∈ C) → (∀ v ∈ S₂, ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g = JR (Fv F v) J → ∀ i j, g i j ∈ C) → IsCompact (SUSupp σ J ε) := by
  intro F E _ _ _ _ _ σ hCM M J hJ S₁ S₂ ε hε h₁ h₂
  classical
  haveI : FiniteDimensional F E := inferInstance
  have h₁' : ∀ w : InfinitePlace F, ∃ C : Set (w.Completion ⊗[F] E), IsCompact C ∧ (w ∈ S₁ →
      ∀ g : Matrix (Fin M) (Fin M) (w.Completion ⊗[F] E), Formalism.UG.cT (sigR w.Completion σ) g * JR w.Completion J * g =
        JR w.Completion J → ∀ i j, g i j ∈ C) := by
    intro w
    by_cases hw : w ∈ S₁
    · obtain ⟨C, hC, hC'⟩ := h₁ w hw
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hw⟩
  have h₂' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ (v ∈ S₂ →
      ∀ g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E), Formalism.UG.cT (sigR (Fv F v) σ) g * JR (Fv F v) J * g =
        JR (Fv F v) J → ∀ i j, g i j ∈ C) := by
    intro v
    by_cases hv : v ∈ S₂
    · obtain ⟨C, hC, hC'⟩ := h₂ v hv
      exact ⟨C, hC, fun _ => hC'⟩
    · exact ⟨∅, isCompact_empty, fun h => absurd h hv⟩
  choose C₁ hC₁ hC₁' using h₁'
  choose C₂ hC₂ hC₂' using h₂'
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Set (AF F ⊗[F] E)), (∀ i ∈ s, IsCompact (f i)) →
      IsCompact (∑ i ∈ s, f i) := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, ← Set.singleton_zero]; exact isCompact_singleton
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  set e := algebraMap (AF F) (AF F ⊗[F] E) ε with he
  let X : Set (AF F ⊗[F] E) := (fun δ => δ * (1 - e)) '' ({0, 1} : Set (AF F ⊗[F] E)) +
    (∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w) '' C₁ w) +
    ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v) '' C₂ v
  have hX : IsCompact X :=
    ((((Set.toFinite _).isCompact).image (continuous_id.mul continuous_const)).add
      (hsum _ _ fun w _ => (hC₁ w).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))).add (hsum _ _ fun v _ => (hC₂ v).image (GlobalTheory.T.continuous_placeExtensionByZero_tensor_of_place _))
  refine GlobalTheory.T.isCompact_specialUnitarySupportedAtPlaces σ J ε X hX (_root_.GlobalTheory.SUSuppClosed.isClosed_SUSupp σ J ε) fun g hg i j => ?_
  have hu : Formalism.UG.cT (sigR (AF F) σ) ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      JR (AF F) J * ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = JR (AF F) J := by
    let g' : HR (AF F) σ J := g
    exact g'.2
  set a := ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with ha
  set δ := (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j with hδ
  have hfix : e * (a - δ) = a - δ := by
    have := hg.2 i j
    simpa only [Matrix.sub_apply] using this
  have hdec : a = δ * (1 - e) + e * a := by linear_combination (-1 : AF F ⊗[F] E) * hfix
  rw [hdec, _root_.GlobalTheory.PlaceIdemSum.idem_mul_eq_sum S₁ S₂ ε hε a, ← add_assoc]
  refine Set.add_mem_add (Set.add_mem_add ⟨δ, ?_, rfl⟩ (Set.finsetSum_mem_finsetSum _ _ _ fun w hw => ⟨_, ?_, rfl⟩))
    (Set.finsetSum_mem_finsetSum _ _ _ fun v hv => ⟨_, ?_, rfl⟩)
  · rw [hδ, Matrix.one_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact hC₁' w hw _ (_root_.GlobalTheory.unitaryEq_baseChange σ J _ _ hu) i j
  · exact hC₂' v hv _ (_root_.GlobalTheory.unitaryEq_baseChange σ J _ _ hu) i j

end GlobalTheory.SUSuppCompact

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompacts
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime]

theorem isCompact_box (K : ∀ v : AwayP p, Set (Qv v)) (hK : ∀ v, IsCompact (K v))
    (h : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ) :
    IsCompact {a : AfP p | ∀ v, AfP.eval v a ∈ K v} := by
  let S : Set (AwayP p) := {v | K v ⊆ v.1.adicCompletionIntegers ℚ}
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 h
  let P := RestrictedProduct (fun v : AwayP p => v.1.adicCompletion ℚ)
      (fun v => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (Filter.principal S)
  have h1 : IsCompact {x : P | ∀ v, x v ∈ K v} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hK
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ v -
      exact hy v
    · intro hx
      exact ⟨⟨x, fun v hv => hv (hx v trivial)⟩, fun v => hx v trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : AfP p | ∀ v, AfP.eval v a ∈ K v} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ v, x v ∈ K v} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨(LevelExists.rp a).1, fun v hv => hv (ha v)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

def basA : Module.Basis (Fin (Module.finrank ℚ G.C)) (AfP p) (AfP p ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (AfP p) (Module.finBasis ℚ G.C)

def tv (v : AwayP p) : AfP p ⊗[ℚ] G.C →+* Qv v ⊗[ℚ] G.C :=
  (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom

theorem repr_tv (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) (i : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (tv G v y) i = AfP.eval v ((basA G).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp [tv, basV, basA, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem continuous_eval (v : AwayP p) : Continuous (AfP.eval (p := p) v) :=
  RestrictedProduct.continuous_eval v

end GlobalTheory.OrbFinAf.CompactOrbitVectors

namespace GlobalTheory.OrbFinAf.CompactOrbitVectors

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem tv_eq (v : AwayP p) (y : AfP p ⊗[ℚ] G.C) :
    tv G v y = (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) := by
  apply (basV G v).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  simp only [Module.Basis.equivFun_apply]
  exact repr_tv G v y i

theorem continuous_tv (v : AwayP p) :
    @Continuous _ _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)) (moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)) (tv G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : ContinuousAdd (Qv v ⊗[ℚ] G.C) := IsModuleTopology.toContinuousAdd (Qv v) _
  have h1 : Continuous (basA G).equivFun := IsModuleTopology.continuous_of_linearMap (basA G).equivFun.toLinearMap
  have h2 : Continuous (basV G v).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.symm.toLinearMap
  have : tv G v = fun y => (basV G v).equivFun.symm (fun i => AfP.eval v ((basA G).equivFun y i)) :=
    funext (tv_eq G v)
  rw [this]
  exact h2.comp (continuous_pi fun i => (continuous_eval v).comp ((continuous_apply i).comp h1))

theorem continuous_piV (v : AwayP p) : Continuous (piV G v) := by
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  have ht := continuous_tv G v
  have hval : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hinv : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hval2 : Continuous fun x : G.GAf => ((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hinv2 : Continuous fun x : G.GAf => ((((x : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · rw [Units.continuous_iff]
    exact ⟨ht.comp hval, ht.comp hinv⟩
  · rw [Units.continuous_iff]
    exact ⟨(continuous_eval v).comp hval2, (continuous_eval v).comp hinv2⟩

end GlobalTheory.OrbFinAf.CompactOrbitVectors

open scoped RestrictedProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]


open CompactOrbitVectors in
theorem isCompact_prod_local : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (D : ∀ v : AwayP p, Set (Gv G v)),
    (∀ v, IsCompact (D v)) → (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D v ⊆ IntV G v) →
    IsCompact {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
  intro p _ G D hDc hDi
  haveI : T2Space (AfP p) := inferInstanceAs
    (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) _
  haveI : T2Space (AfP p ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (AfP p) G.C

  let c1 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c2 : ∀ v : AwayP p, Fin (Module.finrank ℚ G.C) → Gv G v → Qv v := fun v i h =>
    (basV G v).repr ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) i
  let c3 : ∀ v : AwayP p, Gv G v → Qv v := fun v h => (((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v)
  let c4 : ∀ v : AwayP p, Gv G v → Qv v := fun v h =>
    ((((h : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v)
  have hc : ∀ v, (∀ i, Continuous (c1 v i)) ∧ (∀ i, Continuous (c2 v i)) ∧ Continuous (c3 v) ∧
      Continuous (c4 v) := by
    intro v
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    have hr : Continuous (basV G v).equivFun :=
      IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)))
    · exact (continuous_apply i).comp (hr.comp
        (Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)))
    · exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    · exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  let K : ∀ v : AwayP p, Set (Qv v) := fun v =>
    ((⋃ i, c1 v i '' D v) ∪ (⋃ i, c2 v i '' D v)) ∪ (c3 v '' D v ∪ c4 v '' D v)
  have hKc : ∀ v, IsCompact (K v) := fun v =>
    ((isCompact_iUnion fun i => (hDc v).image ((hc v).1 i)).union
      (isCompact_iUnion fun i => (hDc v).image ((hc v).2.1 i))).union
      (((hDc v).image (hc v).2.2.1).union ((hDc v).image (hc v).2.2.2))
  have hKi : ∀ᶠ v in Filter.cofinite, K v ⊆ v.1.adicCompletionIntegers ℚ := by
    filter_upwards [hDi] with v hv
    rintro y ((hy | hy) | (hy | hy))
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).1 i
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, hh, rfl⟩ := hi
      exact (hv hh).2.1 i
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.1
    · obtain ⟨h, hh, rfl⟩ := hy
      exact (hv hh).2.2.2
  let E : Set (AfP p) := {a | ∀ v, AfP.eval v a ∈ K v}
  have hE : IsCompact E := isCompact_box K hKc hKi
  let Bm : Set (AfP p ⊗[ℚ] G.C) := (basA G).equivFun.symm '' Set.univ.pi fun _ => E
  have hBm : IsCompact Bm := (isCompact_univ_pi fun _ => hE).image
    (IsModuleTopology.continuous_of_linearMap (basA G).equivFun.symm.toLinearMap)
  let B : Set (((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ)) :=
    (Bm ×ˢ (MulOpposite.op '' Bm)) ×ˢ (E ×ˢ (MulOpposite.op '' E))
  have hB : IsCompact B := (hBm.prod (hBm.image MulOpposite.continuous_op)).prod
    (hE.prod (hE.image MulOpposite.continuous_op))

  have hσ : Continuous (fun y : AfP p ⊗[ℚ] G.C ↦ (starT G.star (AfP p) y).unop) := by
    let σl : (AfP p ⊗[ℚ] G.C) →ₗ[AfP p] (AfP p ⊗[ℚ] G.C) :=
      { toFun := fun y ↦ (starT G.star (AfP p) y).unop
        map_add' := fun x y ↦ by simp only [map_add (f := _), MulOpposite.unop_add]
        map_smul' := by
          intro r x
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul a y =>
            simp only [TensorProduct.smul_tmul', smul_eq_mul, starT_tmul, RingHom.id_apply]
          | add x y hx hy => simp only [smul_add, map_add (f := _), MulOpposite.unop_add, hx, hy, RingHom.id_apply] }
    exact IsModuleTopology.continuous_of_linearMap σl
  have hj : Continuous (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AfP p) (AfP p ⊗[ℚ] G.C))
  have hGcl : IsClosed (UPts G.star (AfP p) : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
    apply isClosed_eq
    · exact (Units.continuous_val.comp continuous_fst).mul
        (hσ.comp (Units.continuous_val.comp continuous_fst))
    · exact hj.comp (Units.continuous_val.comp continuous_snd)
  let emb : G.GAf → ((AfP p ⊗[ℚ] G.C) × (AfP p ⊗[ℚ] G.C)ᵐᵒᵖ) × (AfP p × (AfP p)ᵐᵒᵖ) :=
    fun x ↦ (Units.embedProduct _ x.1.1, Units.embedProduct _ x.1.2)
  have hemb : Topology.IsClosedEmbedding emb :=
    (Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct).comp
      hGcl.isClosedEmbedding_subtypeVal

  have hS : IsClosed {g : G.GAf | ∀ v, piV G v g ∈ D v} := by
    have : {g : G.GAf | ∀ v, piV G v g ∈ D v} = ⋂ v, piV G v ⁻¹' D v := by
      ext g; simp
    rw [this]
    refine isClosed_iInter fun v => ?_
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
    haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
    haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
    haveI : T2Space (Qv v ⊗[ℚ] G.C) := LevelExists.t2Space_tensor_rat_finite_algebra_moduleTopology (Qv v) G.C
    haveI : T2Space (Gv G v) := inferInstance
    exact (hDc v).isClosed.preimage (continuous_piV G v)

  have hsub : emb '' {g : G.GAf | ∀ v, piV G v g ∈ D v} ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩
    have hco : ∀ y : AfP p ⊗[ℚ] G.C,
        (∀ v i, (basV G v).repr (tv G v y) i ∈ K v) → y ∈ Bm := by
      intro y hy
      refine ⟨(basA G).equivFun y, fun i _ v => ?_, by simp⟩
      rw [Module.Basis.equivFun_apply, ← repr_tv]
      exact hy v i
    refine ⟨⟨hco _ fun v i => ?_, ⟨_, hco _ fun v i => ?_, rfl⟩⟩, ⟨fun v => ?_, ⟨_, fun v => ?_, rfl⟩⟩⟩
    · exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, piV G v x, hx v, rfl⟩))
    · exact Or.inr (Or.inl ⟨piV G v x, hx v, rfl⟩)
    · exact Or.inr (Or.inr ⟨piV G v x, hx v, rfl⟩)
  exact hemb.isInducing.isCompact_iff.2 (hB.of_isClosed_subset (hemb.isClosedMap _ hS) hsub)

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompact
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem isCompact_setOf_fst_mem (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p) :
    letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C);
    ∀ K : Set (Qv v ⊗[ℚ] G.C)ˣ, IsCompact K →
      IsCompact {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} := by
  letI tA : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C)
  intro K hK
  haveI : IsModuleTopology (Qv v) (Qv v ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (Qv v ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (Qv v) _
  haveI : T2Space (Qv v ⊗[ℚ] G.C) := T2Space.of_injective_continuous (basV G v).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (basV G v).equivFun.toLinearMap)
  have hst1 : ∀ r : Qv v, (starT G.star (Qv v) (algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r)).unop =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) r := by
    intro r
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, starT_tmul, map_one,
      MulOpposite.unop_one]
  let sL : (Qv v ⊗[ℚ] G.C) →ₗ[Qv v] (Qv v ⊗[ℚ] G.C) :=
    { toFun := fun y => (starT G.star (Qv v) y).unop
      map_add' := fun x y => by simp
      map_smul' := fun r y => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, MulOpposite.unop_mul]
        rw [hst1]
        exact (Algebra.commutes r _).symm }
  have hsc : Continuous sL := IsModuleTopology.continuous_of_linearMap sL
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (K := Qv v) (s := ({()} : Set Unit))
    (v := fun _ : Unit => (1 : Qv v ⊗[ℚ] G.C)) (by
      rw [linearIndepOn_singleton_iff]; exact one_ne_zero)
  have hf1 : f 1 = 1 := hf () rfl
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have key : ∀ d : Gv G v, f (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C) *
      sL ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)) =
      (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := by
    intro d
    have hd : (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
        (starT G.star (Qv v) ((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : Qv v ⊗[ℚ] G.C)).unop =
        algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) (((d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) := d.2
    show f (_ * (starT G.star (Qv v) _).unop) = _
    rw [hd, Algebra.algebraMap_eq_smul_one, map_smul, hf1, smul_eq_mul, mul_one]
  set L1 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ => f ((u : Qv v ⊗[ℚ] G.C) * sL u)) '' K with hL1
  set L2 : Set (Qv v) := (fun u : (Qv v ⊗[ℚ] G.C)ˣ =>
    f (((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) * sL ((u⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C))) '' K with hL2
  have hL1c : IsCompact L1 := hK.image (hfc.comp (Units.continuous_val.mul (hsc.comp Units.continuous_val)))
  have hL2c : IsCompact L2 := hK.image (hfc.comp (Units.continuous_coe_inv.mul (hsc.comp Units.continuous_coe_inv)))
  set T : Set (Qv v)ˣ := Units.embedProduct (Qv v) ⁻¹' (L1 ×ˢ (MulOpposite.op '' L2)) with hT
  have hTc : IsCompact T :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hL1c.prod (hL2c.image MulOpposite.continuous_op))
  set Z : Set ((Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ) := {x | ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) *
      sL ((x.1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) =
      algebraMap (Qv v) (Qv v ⊗[ℚ] G.C) ((x.2 : (Qv v)ˣ) : Qv v)} with hZ
  have hZc : IsClosed Z := isClosed_eq
    ((Units.continuous_val.comp continuous_fst).mul (hsc.comp (Units.continuous_val.comp continuous_fst)))
    ((continuous_algebraMap (Qv v) (Qv v ⊗[ℚ] G.C)).comp (Units.continuous_val.comp continuous_snd))
  have himg : Subtype.val '' {d : Gv G v | (d : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 ∈ K} = (K ×ˢ T) ∩ Z := by
    ext x
    constructor
    · rintro ⟨d, hdK, rfl⟩
      have k2 := key d⁻¹
      simp only [Subgroup.coe_inv, Prod.fst_inv, Prod.snd_inv] at k2
      refine ⟨⟨hdK, ?_⟩, d.2⟩
      show Units.embedProduct (Qv v) _ ∈ L1 ×ˢ (MulOpposite.op '' L2)
      rw [Units.embedProduct_apply]
      exact ⟨⟨_, hdK, key d⟩, ⟨_, ⟨_, hdK, k2⟩, rfl⟩⟩
    · rintro ⟨⟨hK1, -⟩, hZ1⟩
      exact ⟨⟨x, hZ1⟩, hK1, rfl⟩
  exact Subtype.isCompact_iff.2 (himg ▸ (hK.prod hTc).inter_right hZc)

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassPullbackVeryAmple
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem eff_pull_of_veryAmpleBy : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (hH : H.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∀ (φ : Y ⟶ X), Nonempty Y → GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.pull φ (GlobalTheory.CechPic.cls H hH)) := by
  intro R _ X Y f H m s hH hva φ hY
  obtain ⟨y⟩ := hY
  have hy : φ y ∈ ⨆ i, nonzeroLocus (s i) := by rw [hva.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have hy' : y ∈ nonzeroLocus (GlobalTheory.secPull (s i) φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact hi
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
  have hne : (GlobalTheory.secPull (s i) φ).f k ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hk
    exact hk
  rw [← cls_pull hH φ (pull_isLB hH φ)]
  exact eff_of_sec _ _ _ k hne

end GlobalTheory.EffBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinOpenSubBaseChange
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory


open Matrix NumberField in
open scoped TensorProduct Classical in
theorem _root_.GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral (K : Type) [Field K] [NumberField K]
    (d D : ℕ) (B : ℝ) (hD : 0 < D) :
    {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧
      ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  have hT : {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}.Finite := by
    have h := NumberField.Embeddings.finite_of_norm_le K ℂ ((D : ℝ) * B)
    refine (h.image fun x => x / (D : K)).subset ?_
    intro c hc
    refine ⟨(D : K) * c, ⟨hc.1, fun φ => ?_⟩, ?_⟩
    · have := mul_le_mul_of_nonneg_left (hc.2 φ) (Nat.cast_nonneg (α := ℝ) D)
      simpa [norm_mul] using this
    · have hD' : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
      field_simp
  have hF : (Set.pi Set.univ fun _ : Fin (d + 1) =>
      {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => hT
  refine Set.Finite.of_finite_image
    (f := fun P : Polynomial K => fun i : Fin (d + 1) => P.coeff i) (hF.subset ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩ i -
    exact ⟨(hP.2.2 i).1, (hP.2.2 i).2⟩
  · intro P hP Q hQ hPQ
    ext n
    by_cases hn : n ≤ d
    · exact congrFun hPQ ⟨n, Nat.lt_succ_of_le hn⟩
    · push_neg at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.2.1.trans_lt hn),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.2.1.trans_lt hn)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumCompMulEquivStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_comp_mulEquiv : ∀ {Γ Γ' G₁ G₂ : Type} [Group Γ] [Group Γ'] [Group G₁] [Group G₂] (e : Γ' ≃* Γ) (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), pointSum (ι₁.comp e.toMonoidHom) (ι₂.comp e.toMonoidHom) θ K₁ K₂ γ δ f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.pointSum_comp_mulEquiv) | (exact GlobalTheory.pointSum_comp_mulEquiv) | (intros; apply GlobalTheory.pointSum_comp_mulEquiv  <;> assumption)
end

