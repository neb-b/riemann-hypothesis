module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetLocalComponentCopiesFixedAway
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.FinMultAway

section Abstract

variable {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
  {π : Representation ℂ G N} {ρ : Representation ℂ G X}

theorem apply_comm (φ : π.IntertwiningMap ρ) (g : G) (n : N) : φ.toLinearMap (π g n) = ρ g (φ.toLinearMap n) :=
  LinearMap.congr_fun (φ.isIntertwining' g) n

theorem isSemisimple_of_isotypic (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) : ρ.IsSemisimpleRepresentation := by
  haveI := hπ
  have hs : π.IsSemisimpleRepresentation :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule π).2 inferInstance
  exact GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range G X ρ (π.IntertwiningMap ρ) (fun _ => N) (fun _ => π)
    (fun φ => φ.toLinearMap) (fun _ => hs) (fun φ g x => apply_comm φ g x) h

theorem stable_biSup (s : Finset (π.IntertwiningMap ρ)) (g : G) :
    ∀ x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap, ρ g x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  intro x hx
  have : (⨆ φ ∈ s, LinearMap.range φ.toLinearMap) ≤ (⨆ φ ∈ s, LinearMap.range φ.toLinearMap).comap (ρ g) := by
    refine iSup₂_le fun φ hφ => ?_
    rintro _ ⟨n, rfl⟩
    rw [Submodule.mem_comap, ← apply_comm]
    exact Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ ⟨_, rfl⟩)
  exact this hx

theorem exists_intertwining_le (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) (C : Subrepresentation ρ)
    (hC : C ≠ ⊥) : ∃ ψ : π.IntertwiningMap ρ, Function.Injective ψ ∧ ∀ n, ψ n ∈ C.toSubmodule := by
  haveI := hπ
  haveI := isSemisimple_of_isotypic hπ h
  obtain ⟨C1, hc⟩ := exists_isCompl C
  have hc' : IsCompl C.toSubmodule C1.toSubmodule :=
    IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hc.inf_eq_bot)
      (congrArg Subrepresentation.toSubmodule hc.sup_eq_top)
  let P : X →ₗ[ℂ] X := C.toSubmodule.subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ hc'
  have hPl : ∀ a ∈ C.toSubmodule, P a = a := fun a ha =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc' ⟨a, ha⟩)
  have hPr : ∀ b ∈ C1.toSubmodule, P b = 0 := fun b hb =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc' ⟨b, hb⟩)
  have hPi : ∀ g x, P (ρ g x) = ρ g (P x) := fun g x => by
    have hx : x ∈ C.toSubmodule ⊔ C1.toSubmodule := by rw [hc'.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hPl a ha, hPr b hb, hPl _ (C.apply_mem_toSubmodule g ha),
      hPr _ (C1.apply_mem_toSubmodule g hb), add_zero, add_zero]
  have hPm : ∀ x, P x ∈ C.toSubmodule := fun x => by simp [P]
  obtain ⟨c, hc0, hcne⟩ : ∃ c ∈ C.toSubmodule, c ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hC (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun x hx => hn x hx))
  by_contra hno
  push_neg at hno
  have hall : ∀ φ : π.IntertwiningMap ρ, LinearMap.range φ.toLinearMap ≤ LinearMap.ker P := by
    intro φ
    let ψ : π.IntertwiningMap ρ := ⟨P ∘ₗ φ.toLinearMap, fun g => LinearMap.ext fun n => by
      simp only [LinearMap.comp_apply]
      rw [apply_comm φ g n, hPi]⟩
    rcases Representation.IsIrreducible.injective_or_eq_zero ψ with hi | h0
    · obtain ⟨n, hn⟩ := hno ψ hi
      exact absurd (hPm _) hn
    · rintro _ ⟨n, rfl⟩
      exact DFunLike.congr_fun h0 n
  have : c ∈ LinearMap.ker P := by
    have h1 : c ∈ isoPartAlg π ρ := by rw [h]; trivial
    exact (iSup_le hall) h1
  exact hcne ((hPl c hc0).symm.trans this)

end Abstract

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

section Abstract

variable {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
  {π : Representation ℂ G N} {ρ : Representation ℂ G X}

theorem le_biSup_of_fixed (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) {v : N} (hv : v ≠ 0) (Y : Submodule ℂ X)
    (hY : ∀ g, ∀ x ∈ Y, ρ g x ∈ Y) (s : Finset (π.IntertwiningMap ρ))
    (hF : ∀ x ∈ Y, (∀ g, π g v = v → ρ g x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) :
    Y ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  haveI := isSemisimple_of_isotypic hπ h
  let A : Subrepresentation ρ := ⟨Y ⊓ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap, fun g x hx =>
    ⟨hY g x hx.1, stable_biSup s g x hx.2⟩⟩
  obtain ⟨C0, hc⟩ := exists_isCompl A
  let C : Subrepresentation ρ := ⟨Y ⊓ C0.toSubmodule, fun g x hx => ⟨hY g x hx.1, C0.apply_mem_toSubmodule g hx.2⟩⟩
  have hC : C = ⊥ := by
    by_contra hne
    obtain ⟨ψ, hi, hm⟩ := exists_intertwining_le hπ h C hne
    have hx0 : ψ v ≠ 0 := fun e => hv (hi (e.trans (map_zero ψ).symm))
    have hxY : ψ v ∈ Y := (hm v).1
    have hxM := hF _ hxY fun g hg => by rw [← ψ.isIntertwining, hg]
    have h1 : ψ v ∈ (A ⊓ C0).toSubmodule := ⟨⟨hxY, hxM⟩, (hm v).2⟩
    rw [hc.inf_eq_bot] at h1
    exact hx0 h1
  intro y hy
  have h2 : y ∈ (A ⊔ C0).toSubmodule := by rw [hc.sup_eq_top]; trivial
  obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 h2
  have hcY : c ∈ Y := by simpa using Y.sub_mem hy ha.1
  have hcC : c ∈ C.toSubmodule := ⟨hcY, hc'⟩
  rw [hC] at hcC
  have hc0 : c = 0 := hcC
  rw [hc0, add_zero]
  exact ha.2

end Abstract

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

variable {D : D7} {V : HSp D} (u : HeightOneSpectrum (𝓞 D.host.F))

theorem finLoc_locFin (x : Gv V u) : finLoc V u (locFin V u x) = x :=
  proj_emb_self D.sp.cm.sig V.gram u x

theorem commute_locFin (x : Gv V u) {k : GfC V} (hk : finLoc V u k = 1) : Commute (locFin V u x) k :=
  Subtype.ext (commute_emb D.sp.cm.sig V.gram x hk).eq

theorem continuous_finLoc : Continuous (finLoc V u) :=
  (continuous_proj D.sp.cm.sig V.gram u).comp continuous_subtype_val

theorem continuous_locFin : Continuous (locFin V u) :=
  (continuous_emb D.sp.cm.sig V.gram u).subtype_mk _

noncomputable def away : GfC V →* GfC V where
  toFun k := k * (locFin V u (finLoc V u k))⁻¹
  map_one' := by simp
  map_mul' a b := by
    have hb : finLoc V u (b * (locFin V u (finLoc V u b))⁻¹) = 1 := by
      rw [map_mul, map_inv, finLoc_locFin, mul_inv_cancel]
    have hc := (commute_locFin u (finLoc V u a) hb).inv_left
    simp only [map_mul, mul_inv_rev]
    rw [mul_assoc a _ (b * _), hc.eq]
    simp only [mul_assoc]

theorem finLoc_away (k : GfC V) : finLoc V u (away u k) = 1 := by
  show finLoc V u (k * (locFin V u (finLoc V u k))⁻¹) = 1
  rw [map_mul, map_inv, finLoc_locFin, mul_inv_cancel]

theorem away_mul (k : GfC V) : away u k * locFin V u (finLoc V u k) = k := by
  show k * (locFin V u (finLoc V u k))⁻¹ * locFin V u (finLoc V u k) = k
  group

theorem continuous_away : Continuous (away (V := V) u) :=
  continuous_id.mul (((continuous_locFin u).comp (continuous_finLoc u)).inv)

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

theorem exists_finset_fixed_away : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))), ∀ x : W, (∀ k ∈ K, finLoc V u k = 1 → σ k x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  intro D V u W _ _ σ hσa N _ _ π hπ hπa hloc K hK
  have hiso : IsIsotypicAlg π (σ.comp (locFin V u)) := hloc
  obtain ⟨v, hv⟩ : ∃ v : N, v ≠ 0 := by
    by_contra hn
    push_neg at hn
    haveI : Subsingleton N := ⟨fun a b => (hn a).trans (hn b).symm⟩
    exact (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  let St : Subgroup (Gv V u) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} ha hb => by
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        show π a⁻¹ v = v
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSt : IsOpen (St : Set (Gv V u)) := hπa.1 v
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.CuspDec.exists_compact_open V
  let K2 : Subgroup (GfC V) := K0 ⊓ St.comap (finLoc V u) ⊓ K.comap (away u)
  have hK2o : IsOpen (K2 : Set (GfC V)) :=
    (hK0o.inter (hSt.preimage (continuous_finLoc u))).inter (hK.preimage (continuous_away u))
  have hK2c : IsCompact (K2 : Set (GfC V)) :=
    hK0c.of_isClosed_subset (K2.isClosed_of_isOpen hK2o) fun k hk => hk.1.1
  haveI := hσa.2 K2 hK2o hK2c
  let Y : Submodule ℂ W := GlobalTheory.PRep.fixed σ (K ⊓ (finLoc V u).ker)
  have hmemY : ∀ x, x ∈ Y ↔ ∀ k ∈ K, finLoc V u k = 1 → σ k x = x := by
    intro x
    rw [GlobalTheory.CuspDec.mem_fixed]
    exact ⟨fun h k hk h1 => h k ⟨hk, h1⟩, fun h k hk => h k hk.1 hk.2⟩
  have hY : ∀ g, ∀ x ∈ Y, σ.comp (locFin V u) g x ∈ Y := by
    intro g x hx
    rw [hmemY] at hx ⊢
    intro k hk h1
    show σ k (σ (locFin V u g) x) = σ (locFin V u g) x
    rw [← Module.End.mul_apply, ← map_mul, ← (commute_locFin u g h1).eq, map_mul, Module.End.mul_apply, hx k hk h1]
  let F : Submodule ℂ W := Y ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) St
  have hFle : F ≤ GlobalTheory.PRep.fixed σ K2 := by
    intro y hy
    rw [GlobalTheory.CuspDec.mem_fixed]
    intro k hk
    have h1 : σ (locFin V u (finLoc V u k)) y = y := (GlobalTheory.CuspDec.mem_fixed.1 hy.2) _ hk.1.2
    have h2 : σ (away u k) y = y := (hmemY y).1 hy.1 _ hk.2 (finLoc_away u k)
    rw [← away_mul u k, map_mul, Module.End.mul_apply, h1, h2]
  haveI : FiniteDimensional ℂ F := Submodule.finiteDimensional_of_le hFle
  have hFfg : F.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨s, hs⟩ := IsCompactElement.exists_finset_of_le_iSup ((Submodule.fg_iff_compact F).1 hFfg)
    (fun φ : π.IntertwiningMap (σ.comp (locFin V u)) => LinearMap.range φ.toLinearMap)
    (le_of_le_of_eq le_top hiso.symm)
  refine ⟨s, fun x hx => le_biSup_of_fixed hπ hiso hv Y hY s (fun y hy hfix => hs ⟨hy, ?_⟩) ((hmemY x).2 hx)⟩
  exact GlobalTheory.CuspDec.mem_fixed.2 fun k hk => hfix k hk

end GlobalTheory.FinMultAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInequivalentRepresentativesThroughMember
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrUnion

theorem exists_reps_through : ∀ (G : Type) [Group G] [TopologicalSpace G] (m : ℕ) (W : Fin m → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), ∀ i₀ : Fin m, ∃ (n : ℕ) (s : Fin n → Fin m), (∀ i j, i ≠ j → IsEmpty ((σ (s i)).Equiv (σ (s j)))) ∧ (∃ j, s j = i₀) ∧ ∀ i, ∃ j, Nonempty ((σ i).Equiv (σ (s j))) := by
  intro G _ _ m W _ _ σ i₀
  classical
  let R : Fin m → Fin m → Prop := fun i j => Nonempty ((σ i).Equiv (σ j))
  have hrefl : ∀ i, R i i := fun i => ⟨Representation.Equiv.refl _⟩
  have hsymm : ∀ {i j}, R i j → R j i := fun ⟨e⟩ => ⟨e.symm⟩
  have htrans : ∀ {i j k}, R i j → R j k → R i k := fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩
  let S : Setoid (Fin m) := ⟨R, ⟨hrefl, hsymm, htrans⟩⟩
  let f : Fin m → Fin m := fun i => if R i i₀ then i₀ else (Quotient.mk S i).out
  have hf : ∀ i, R (f i) i := by
    intro i
    by_cases h : R i i₀
    · simp only [f, if_pos h]; exact hsymm h
    · simp only [f, if_neg h]; exact Quotient.mk_out (s := S) i
  have hfc : ∀ i j, R i j → f i = f j := by
    intro i j hij
    by_cases h : R i i₀
    · have h' : R j i₀ := htrans (hsymm hij) h
      simp only [f, if_pos h, if_pos h']
    · have h' : ¬ R j i₀ := fun h' => h (htrans hij h')
      simp only [f, if_neg h, if_neg h']
      rw [Quotient.sound (s := S) hij]
  let T : Finset (Fin m) := Finset.univ.image f
  let e : T ≃ Fin T.card := T.equivFin
  refine ⟨T.card, fun k => (e.symm k).1, ?_, ?_, ?_⟩
  · intro k l hkl
    refine ⟨fun hR => ?_⟩
    apply hkl
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (e.symm k).2
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 (e.symm l).2
    have hxy : R x y := by
      have h1 : R (f x) (f y) := by rw [hx, hy]; exact ⟨hR⟩
      exact htrans (hsymm (hf x)) (htrans h1 (hf y))
    have : (e.symm k).1 = (e.symm l).1 := by rw [← hx, ← hy]; exact hfc x y hxy
    exact e.symm.injective (Subtype.ext this)
  · have hmem : i₀ ∈ T := Finset.mem_image.2 ⟨i₀, Finset.mem_univ _, by simp only [f, if_pos (hrefl i₀)]⟩
    exact ⟨e ⟨i₀, hmem⟩, by simp⟩
  · intro i
    have hmem : f i ∈ T := Finset.mem_image_of_mem f (Finset.mem_univ i)
    refine ⟨e ⟨f i, hmem⟩, ?_⟩
    show R i (e.symm (e ⟨f i, hmem⟩)).1
    rw [Equiv.symm_apply_apply]
    exact hsymm (hf i)

end GlobalTheory.TrUnion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntLevelSchwartzBruhatFiniteAdelic
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace GlobalTheory.SBLevel

theorem exists_int_level : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x u : κ → FiniteAdeleRing (𝓞 F) F,
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 F),
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) v ∈ v.adicCompletionIntegers F) →
      g (x + u) = g x := by
  intro F _ _ κ _ g hg
  classical
  obtain ⟨N, hN, hNg⟩ := GlobalTheory.SBBox.exists_nhds_zero_add_eq hg.1 hg.2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hW : (⋂ i, t i) ∈ nhds (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  refine ⟨d, hd0, fun x u hu => hNg x u (hIt fun i _ => ?_)⟩
  have hdK : (algebraMap (𝓞 F) F d) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hmem := hd (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) (hu i)
  have he : algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F d) *
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹) * u i) = u i := by
    rw [← mul_assoc, ← map_mul]
    have : algebraMap (𝓞 F) F d * (d : F)⁻¹ = 1 := mul_inv_cancel₀ hdK
    rw [this, map_one, one_mul]
  rw [he] at hmem
  exact Set.mem_iInter.1 hmem i

end GlobalTheory.SBLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleAdmissibleLocalComponentFiniteA
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.LocCompFin

open GlobalTheory.CuspRep.LocEx GlobalTheory.AutMult

section Groups

variable {D : D7} (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F))

theorem finLoc_locFin (x : Gv V u) : finLoc V u (locFin V u x) = x :=
  GlobalTheory.AdelicU.proj_emb_self _ _ u x

theorem commute_locFin (x : Gv V u) {g : GfC V} (hg : finLoc V u g = 1) : Commute (locFin V u x) g :=
  Subtype.ext (GlobalTheory.AdelicU.commute_emb _ _ x hg).eq

theorem continuous_locFin : Continuous (locFin V u) :=
  (GlobalTheory.AdelicU.continuous_emb _ _ u).subtype_mk _

theorem continuous_finLoc : Continuous (finLoc V u) :=
  (GlobalTheory.AdelicU.continuous_proj _ _ u).comp continuous_subtype_val

theorem finLoc_inv_mul (g : GfC V) : finLoc V u ((locFin V u (finLoc V u g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, finLoc_locFin, inv_mul_cancel]

end Groups

theorem exists_locComp : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
    ∃ (N : Type) (_ : AddCommGroup N) (_ : Module ℂ N) (π : Representation ℂ (Gv V u) N),
      π.IsIrreducible ∧ IsAdmissible π ∧ FinHasLocComp V u π σ := by
  intro D V u W _ _ σ hirr hadm
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  obtain ⟨hnt, hinv⟩ := (GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr
  obtain ⟨x, hx0⟩ := exists_ne (0 : W)
  have hsplit : ∀ g (y : W), σ g y = σ (locFin V u (finLoc V u g)) (σ ((locFin V u (finLoc V u g))⁻¹ * g) y) :=
    fun g y => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hcomm : ∀ g : GfC V, finLoc V u g = 1 → ∀ h (y : W),
      σ g (σ (locFin V u h) y) = σ (locFin V u h) (σ g y) := by
    intro g hg h y
    rw [← Module.End.mul_apply, ← map_mul, ← (commute_locFin V u h hg).eq, map_mul, Module.End.mul_apply]
  have hρ : GlobalTheory.PRep.IsSmooth (σ.comp (locFin V u)) := fun v => (hadm.1 v).preimage (continuous_locFin V u)
  let K₀ : Subgroup (GfC V) := stab σ x
  have hK₀ : IsOpen (K₀ : Set (GfC V)) := hadm.1 x
  let Kc : Subgroup (Gv V u) := K₀.comap (locFin V u) ⊓ Kv V u
  have hKco : IsOpen (Kc : Set (Gv V u)) :=
    (hK₀.preimage (continuous_locFin V u)).inter (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ u)
  have hKcc : IsCompact (Kc : Set (Gv V u)) :=
    (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ u).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hKco) fun k hk => hk.2
  have hKcK₀ : ∀ k ∈ Kc, locFin V u k ∈ K₀ := fun k hk => hk.1
  have hxKc : x ∈ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc := mem_fix.2 fun k hk => hKcK₀ k hk
  have hnull : nullPart (σ.comp (locFin V u)) Kc = ⊥ := by
    rcases hinv (nullPart (σ.comp (locFin V u)) Kc) (fun g y hy => by
      rw [hsplit g y]
      exact nullPart_act _ Kc (finLoc V u g) (nullPart_comm _ Kc (σ _)
        (fun h z => hcomm _ (finLoc_inv_mul V u g) h z) hy)) with h | h
    · exact h
    · exact absurd (eq_zero_of_mem_nullPart hρ hKcc hxKc (h ▸ Submodule.mem_top)) hx0
  have h2 : ∀ Y : Submodule ℂ W, (∀ g, ∀ v ∈ Y, σ.comp (locFin V u) g v ∈ Y) →
      Y ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) Kc = ⊥ → Y = ⊥ :=
    fun Y hY h => le_bot_iff.1 (hnull ▸ le_nullPart hρ hKcc Y hY h)
  let L' : Subgroup (GfC V) := K₀ ⊓ (finLoc V u).ker
  let U : Submodule ℂ W := GlobalTheory.PRep.fixed σ L'
  have hU : ∀ g, ∀ v ∈ U, σ.comp (locFin V u) g v ∈ U := fun g v hv => mem_fix.2 fun k hk => by
    change σ k (σ (locFin V u g) v) = σ (locFin V u g) v
    rw [hcomm k hk.2 g v, mem_fix.1 hv k hk]
  have hU0 : U ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun k hk => hk.1, hx0⟩
  obtain ⟨C, hCo, hCc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hfin : ∀ K' : Subgroup (Gv V u), IsOpen (K' : Set (Gv V u)) →
      FiniteDimensional ℂ ↥(U ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) K') := by
    intro K' hK'
    let M : Subgroup (GfC V) := (K₀ ⊓ (Kc ⊓ K').comap (finLoc V u)) ⊓ C
    have hMo : IsOpen (M : Set (GfC V)) :=
      (hK₀.inter ((hKco.inter hK').preimage (continuous_finLoc V u))).inter hCo
    have hMc : IsCompact (M : Set (GfC V)) :=
      hCc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hMo) fun k hk => hk.2
    have := hadm.2 M hMo hMc
    refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.PRep.fixed σ M) fun v hv => mem_fix.2 fun k hk => ?_
    have hk1 : (locFin V u (finLoc V u k))⁻¹ * k ∈ L' :=
      ⟨K₀.mul_mem (K₀.inv_mem (hKcK₀ _ hk.1.2.1)) hk.1.1, finLoc_inv_mul V u k⟩
    rw [hsplit k v, mem_fix.1 hv.1 _ hk1]
    exact mem_fix.1 hv.2 _ hk.1.2.2
  obtain ⟨π, ⟨f, hf0, hf⟩, hπ⟩ := exists_irred hρ hKco h2 U hU hU0 hfin
  refine ⟨π.V, inferInstance, inferInstance, π.ρ, π.irred, hπ, ?_⟩
  let F : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
    { toLinearMap := f, isIntertwining' := fun g => LinearMap.ext (hf g) }
  have hI : ∀ g, ∀ y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)), σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u)) := by
    intro g y hy
    refine Submodule.iSup_induction _ (motive := fun y => σ g y ∈ isoPartAlg π.ρ (σ.comp (locFin V u))) hy ?_ ?_ ?_
    · rintro T _ ⟨z, rfl⟩
      let T' : π.ρ.IntertwiningMap (σ.comp (locFin V u)) :=
        { toLinearMap := σ ((locFin V u (finLoc V u g))⁻¹ * g) ∘ₗ T.toLinearMap
          isIntertwining' := fun h => LinearMap.ext fun w => by
            change σ _ (T (π.ρ h w)) = σ (locFin V u h) (σ _ (T w))
            rw [T.isIntertwining]
            exact hcomm _ (finLoc_inv_mul V u g) h _ }
      refine Submodule.mem_iSup_of_mem T' ⟨π.ρ (finLoc V u g) z, ?_⟩
      change T' (π.ρ (finLoc V u g) z) = σ g (T z)
      rw [T'.isIntertwining, hsplit g (T z)]
      rfl
    · simp only [map_zero]; exact zero_mem _
    · intro a b ha hb; simp only [map_add (f := _)]; exact add_mem ha hb
  rcases hinv _ hI with h | h
  · refine absurd ?_ hf0
    have hr : LinearMap.range F.toLinearMap ≤ ⊥ :=
      h ▸ le_iSup (fun T : π.ρ.IntertwiningMap (σ.comp (locFin V u)) => LinearMap.range T.toLinearMap) F
    exact LinearMap.range_eq_bot.1 (le_bot_iff.1 hr)
  · exact h

end GlobalTheory.LocCompFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCardCosetsDiagonalDoubleCosetGLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_card_cosets_diagonalDoubleCoset_GL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∃ B₀ : Multiset ℂˣ, (∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) // a.out ∈ DoubleCoset.doubleCoset (T d.1) (KGL w (n := r) : Set (GL (Fin r) (w.adicCompletion E))) (KGL w (n := r))} : ℝ) : ℂ) * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B₀ ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B₀.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  first | exact @GlobalTheory.FinZeta.TrivCount.hasSum_card_cosets_diag | exact GlobalTheory.FinZeta.TrivCount.hasSum_card_cosets_diag | (intros; apply GlobalTheory.FinZeta.TrivCount.hasSum_card_cosets_diag <;> assumption)
end

