module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothRepIrreducibleSubcontainingVector
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.MaschkeCompactGroup
section
noncomputable section

namespace UpperTheory.NonzeroTypeTheory.MaschkeCompactGroup

variable {K : Type} [Group K] {m : ℕ}

theorem ker_isOpen [TopologicalSpace K] [IsTopologicalGroup K] (V : Representation ℂ K (Fin m → ℂ))
    (hs : GlobalTheory.PRep.IsSmooth V) : IsOpen ((MonoidHom.ker V : Subgroup K) : Set K) := by
  refine Subgroup.isOpen_of_mem_nhds (MonoidHom.ker V) (g := 1) (Filter.mem_of_superset
    ((isOpen_iInter_of_finite fun i : Fin m => hs (Pi.single i 1)).mem_nhds (by simp)) fun g hg => ?_)
  refine MonoidHom.mem_ker.2 ((Pi.basisFun ℂ (Fin m)).ext fun i => ?_)
  rw [Pi.basisFun_apply]
  exact Set.mem_iInter.1 hg i

theorem maschke [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (V : Representation ℂ K (Fin m → ℂ)) (hs : GlobalTheory.PRep.IsSmooth V)
    (U : Submodule ℂ (Fin m → ℂ)) (hU : ∀ k, ∀ u ∈ U, V k u ∈ U) :
    ∃ S : Submodule ℂ (Fin m → ℂ), IsCompl U S ∧ ∀ k, ∀ s ∈ S, V k s ∈ S := by
  classical
  have : Finite (K ⧸ MonoidHom.ker V) := Subgroup.quotient_finite_of_isOpen _ (ker_isOpen V hs)
  let _ : Fintype (K ⧸ MonoidHom.ker V) := Fintype.ofFinite _
  let ρ : K ⧸ MonoidHom.ker V →* Module.End ℂ (Fin m → ℂ) :=
    QuotientGroup.lift (MonoidHom.ker V) V le_rfl
  have hρ : ∀ k : K, ρ (k : K ⧸ MonoidHom.ker V) = V k := fun k => rfl
  have hmul : ∀ a b : K ⧸ MonoidHom.ker V, ∀ w, ρ a (ρ b w) = ρ (a * b) w := fun a b w => by
    rw [map_mul]; rfl
  have hρU : ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
    intro g u hu
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hρ]
    exact hU k u hu
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl U
  let π := U.projection T hT
  have hπU : ∀ v, π v ∈ U := fun v => Submodule.projection_apply_mem hT v
  have hπid : ∀ u ∈ U, π u = u := fun u hu => Submodule.projection_apply_of_mem_left hT hu
  let P : Module.End ℂ (Fin m → ℂ) := ∑ g : K ⧸ MonoidHom.ker V, (ρ g).comp (π.comp (ρ g⁻¹))
  have hP : ∀ v, P v = ∑ g : K ⧸ MonoidHom.ker V, ρ g (π (ρ g⁻¹ v)) := fun v => by
    simp only [P, LinearMap.sum_apply, LinearMap.comp_apply]
  have hPU : ∀ v, P v ∈ U := fun v => by
    rw [hP]
    exact Submodule.sum_mem _ fun g _ => hρU g _ (hπU _)
  have hPid : ∀ u ∈ U, P u = Fintype.card (K ⧸ MonoidHom.ker V) • u := by
    intro u hu
    have h1 : ∀ g : K ⧸ MonoidHom.ker V, ρ g (π (ρ g⁻¹ u)) = u := fun g => by
      rw [hπid _ (hρU _ _ hu), hmul, mul_inv_cancel, map_one]
      rfl
    rw [hP, Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_const, Finset.card_univ]
  have hPeq : ∀ h v, P (ρ h v) = ρ h (P v) := by
    intro h v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, hP, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun x => ?_
    simp only [Equiv.coe_mulLeft]
    rw [hmul h, mul_inv_cancel_left, mul_inv_rev, inv_inv, ← hmul]
  have hc : (Fintype.card (K ⧸ MonoidHom.ker V) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let f : (Fin m → ℂ) →ₗ[ℂ] U :=
    LinearMap.codRestrict U (((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P)
      (fun v => U.smul_mem _ (hPU v))
  have hf : ∀ x : U, f x = x := by
    intro x
    apply Subtype.ext
    change ((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P x = x
    rw [hPid _ x.2, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hker : ∀ x, x ∈ LinearMap.ker f ↔ P x = 0 := by
    intro x
    rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero]
    change ((Fintype.card (K ⧸ MonoidHom.ker V) : ℂ)⁻¹) • P x = 0 ↔ P x = 0
    rw [smul_eq_zero]
    simp [hc]
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj hf, fun k s hs => ?_⟩
  rw [hker] at hs ⊢
  rw [← hρ, hPeq, hs, map_zero]

end UpperTheory.NonzeroTypeTheory.MaschkeCompactGroup

namespace UpperTheory.NonzeroTypeTheory

open MaschkeCompactGroup in
theorem invariantComplement_holds : SmoothRepIrreducibleSubcontainingVector := by
  intro K _ _ _ _ m V hs v0 hv0
  classical
  have hbot : (∀ k, ∀ w ∈ (⊥ : Submodule ℂ (Fin m → ℂ)), V k w ∈ (⊥ : Submodule ℂ (Fin m → ℂ))) ∧
      v0 ∉ (⊥ : Submodule ℂ (Fin m → ℂ)) := by
    refine ⟨fun k w hw => ?_, fun h => hv0 ((Submodule.mem_bot ℂ).1 h)⟩
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]
  obtain ⟨U, ⟨hUst, hv0U⟩, hUmax⟩ := set_has_maximal_iff_noetherian.mpr inferInstance
    {W : Submodule ℂ (Fin m → ℂ) | (∀ k, ∀ w ∈ W, V k w ∈ W) ∧ v0 ∉ W} ⟨⊥, hbot⟩
  obtain ⟨S, hUS, hSst⟩ := maschke V hs U hUst
  let p := S.projection U hUS.symm
  have hpS : ∀ v, p v ∈ S := fun v => Submodule.projection_apply_mem hUS.symm v
  have hpid : ∀ s ∈ S, p s = s := fun s hs => Submodule.projection_apply_of_mem_left hUS.symm hs
  have hp0 : ∀ v, p v = 0 ↔ v ∈ U := fun v => Submodule.projection_apply_eq_zero_iff hUS.symm
  have hdec : ∀ v, v - p v ∈ U := fun v => Submodule.sub_projection_mem hUS.symm v
  have hpU : ∀ u ∈ U, p u = 0 := fun u hu => (hp0 u).2 hu
  have hpv0 : p v0 ≠ 0 := fun h => hv0U ((hp0 v0).1 h)

  have key : ∀ W : Submodule ℂ (Fin m → ℂ), W ≤ S → (∀ k, ∀ w ∈ W, V k w ∈ W) → W ≠ ⊥ → p v0 ∈ W := by
    intro W hWS hWst hW0
    have hsup : ∀ k, ∀ x ∈ U ⊔ W, V k x ∈ U ⊔ W := by
      intro k x hx
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hUst k u hu) (hWst k w hw)
    have hmem : v0 ∈ U ⊔ W := by
      by_contra hn
      refine hUmax (U ⊔ W) ⟨hsup, hn⟩ (lt_of_le_of_ne le_sup_left fun heq => hW0 ?_)
      refine eq_bot_iff.2 ((le_inf (le_sup_right.trans heq.ge) hWS).trans (disjoint_iff.1 hUS.disjoint).le)
    obtain ⟨u, hu, w, hw, hsum⟩ := Submodule.mem_sup.1 hmem
    rw [← hsum, map_add (f := _), hpU u hu, zero_add, hpid w (hWS hw)]
    exact hw
  refine ⟨S, p, fun h => hpv0 ?_, hSst, fun S' hS'S hS'st => ?_, hpS, hpid, fun k v => ?_, hpv0⟩
  · have := hpS v0
    rw [h, Submodule.mem_bot] at this
    exact this
  · by_cases h0 : S' = ⊥
    · exact Or.inl h0
    right
    have h1 := key S' hS'S hS'st h0
    obtain ⟨T, hST, hTst⟩ := maschke V hs S' hS'st
    have hST0 : S ⊓ T = ⊥ := by
      by_contra hn
      have h2 := key (S ⊓ T) inf_le_left
        (fun k x hx => Submodule.mem_inf.2 ⟨hSst k x (Submodule.mem_inf.1 hx).1, hTst k x (Submodule.mem_inf.1 hx).2⟩) hn
      have h3 : p v0 ∈ S' ⊓ T := Submodule.mem_inf.2 ⟨h1, (Submodule.mem_inf.1 h2).2⟩
      rw [disjoint_iff.1 hST.disjoint, Submodule.mem_bot] at h3
      exact hpv0 h3
    refine le_antisymm hS'S fun s hs => ?_
    have hs' : s ∈ S' ⊔ T := by rw [hST.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, t, ht, hat⟩ := Submodule.mem_sup.1 hs'
    have htS : t ∈ S := by
      have : t = s - a := by rw [← hat]; abel
      rw [this]
      exact S.sub_mem hs (hS'S ha)
    have ht0 : t = 0 := by
      have : t ∈ S ⊓ T := Submodule.mem_inf.2 ⟨htS, ht⟩
      rwa [hST0, Submodule.mem_bot] at this
    rw [← hat, ht0, add_zero]
    exact ha
  · have hv : V k v = V k (p v) + V k (v - p v) := by
      rw [← map_add (f := _)]
      congr 1
      abel
    rw [hv, map_add (f := _), hpid _ (hSst k _ (hpS v)), hpU _ (hUst k _ (hdec v)), add_zero]

end UpperTheory.NonzeroTypeTheory
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfTypeData
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

theorem nz_of_typeData (h2 : SmoothRepIrreducibleSubcontainingVector) (h3 : SmoothRepMinimalSubrepresentation) (h4 : SchurInjectiveFromIrreducible) (TD : TypeData) : NZ := by
  intro E Ω _ _ _ _ _ A w h rc hrc n χ ho
  obtain ⟨J, lam, m, V0, v0, -, -, hsm, hv0, hvec, himp, hemb⟩ := TD E Ω A w h rc hrc n χ ho
  have : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) :=
    isCompact_iff_compactSpace.1 (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  obtain ⟨S, p, hS0, hSst, hSirr, hpS, hpid, hpeq, hpv⟩ := h2 _ m V0 hsm v0 hv0
  obtain ⟨d, ξ, ι, hι, hrange, hint, hirr, hsmξ⟩ := h3 _ m V0 hsm S hS0 hSst hSirr
  refine ⟨d, ξ, hirr, hsmξ, fun π => ⟨?_, ?_⟩⟩
  · rintro ⟨g, hg0, hg⟩
    have hgi : Function.Injective g := h4 _ d ξ hirr π.V (π.ρ.comp (GlobalTheory.LFun.KGL w (n := n)).subtype) g hg0 hg
    obtain ⟨z, hz⟩ : p v0 ∈ LinearMap.range ι := hrange ▸ hpS v0
    refine himp π ⟨g z, fun h0 => hpv ?_, fun j => ?_⟩
    · have : z = 0 := hgi (h0.trans (map_zero g).symm)
      rw [← hz, this, map_zero]
    · have hξz : ξ (j : ↥(GlobalTheory.LFun.KGL w (n := n))) z = ((lam j : ℂˣ) : ℂ) • z := hι (by
        rw [← hint, hz, ← hpeq, hvec j, map_smul, ← hz, map_smul])
      have := hg (j : ↥(GlobalTheory.LFun.KGL w (n := n))) z
      rw [hξz, map_smul] at this
      exact this.symm
  · intro hc
    obtain ⟨f, hf, hfeq⟩ := hemb π hc
    obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, z ≠ 0 := by
      by_contra hne
      push Not at hne
      have : S = ⊥ := by
        rw [← hrange, LinearMap.range_eq_bot]
        exact LinearMap.ext fun v => by rw [hne v, map_zero, LinearMap.zero_apply]
      exact hS0 this
    refine ⟨f ∘ₗ ι, fun h0 => hz (hι (hf ?_)), fun k v => ?_⟩
    · rw [map_zero, map_zero]
      exact LinearMap.congr_fun h0 z
    · simp only [LinearMap.comp_apply]
      rw [← hint, hfeq]

end UpperTheory.NonzeroTypeTheory
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SchurKernelSubmodule
section
noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace SchurKernelSubmodule

def kerSub {K : Type} [Group K] {d : ℕ} (ξ : Representation ℂ K (Fin d → ℂ)) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ K W) (g : (Fin d → ℂ) →ₗ[ℂ] W)
    (hint : ∀ k v, g (ξ k v) = ρ k (g v)) : Subrepresentation ξ :=
  ⟨LinearMap.ker g, fun k v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hint, hv, map_zero]⟩

end SchurKernelSubmodule

open SchurKernelSubmodule in
theorem schurInjective_holds : SchurInjectiveFromIrreducible := by
  intro K _ d ξ hξ W _ _ ρ g hg hint
  haveI : IsSimpleOrder (Subrepresentation ξ) := hξ
  rcases eq_bot_or_eq_top (kerSub ξ ρ g hint) with h | h
  · rw [← LinearMap.ker_eq_bot]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk
      | simpa [kerSub] using hk
  · exfalso
    apply hg
    rw [← LinearMap.ker_eq_top]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk
      | simpa [kerSub] using hk

end UpperTheory.NonzeroTypeTheory
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SubrepresentationTransport
section
noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace SubrepresentationTransport

variable {K : Type} [Group K] {m : ℕ}

def transport (V : Representation ℂ K (Fin m → ℂ)) (S : Submodule ℂ (Fin m → ℂ))
    (hS : ∀ k, ∀ s ∈ S, V k s ∈ S) {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] S) : Representation ℂ K (Fin d → ℂ) where
  toFun k := e.symm.toLinearMap ∘ₗ (V k).restrict (fun s hs => hS k s hs) ∘ₗ e.toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    apply e.injective
    apply Subtype.ext
    simp [LinearMap.restrict_apply]
  map_mul' a b := by
    refine LinearMap.ext fun v => ?_
    apply e.injective
    apply Subtype.ext
    simp [LinearMap.restrict_apply]

lemma transport_apply (V : Representation ℂ K (Fin m → ℂ)) (S : Submodule ℂ (Fin m → ℂ))
    (hS : ∀ k, ∀ s ∈ S, V k s ∈ S) {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] S) (k : K) (v : Fin d → ℂ) :
    ((e (transport V S hS e k v) : S) : Fin m → ℂ) = V k (e v) := by
  simp [transport, LinearMap.restrict_apply]

end SubrepresentationTransport

open SubrepresentationTransport in
theorem minimalSubrepresentation_holds : SmoothRepMinimalSubrepresentation := by
  intro K _ _ _ m V hV S hS0 hS hmin
  set d := Module.finrank ℂ S
  let e : (Fin d → ℂ) ≃ₗ[ℂ] S := (Module.finBasis ℂ S).equivFun.symm
  let ξ := transport V S hS e
  let ι : (Fin d → ℂ) →ₗ[ℂ] (Fin m → ℂ) := S.subtype ∘ₗ e.toLinearMap
  have hι : ∀ v, ι v = ((e v : S) : Fin m → ℂ) := fun v => rfl
  have hinj : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hint : ∀ k v, V k (ι v) = ι (ξ k v) := by
    intro k v
    rw [hι, hι]
    exact (transport_apply V S hS e k v).symm
  have hrange : LinearMap.range ι = S := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e v).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by rw [hι]; simp⟩
  refine ⟨d, ξ, ι, hinj, hrange, hint, ?_, ?_⟩
  · have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.mpr hS0
    have : Nontrivial (Fin d → ℂ) := e.toEquiv.nontrivial
    have hne : (⊥ : Subrepresentation ξ) ≠ ⊤ := by
      intro h
      have h' := congrArg Subrepresentation.toSubmodule h
      exact bot_ne_top h'
    have : Nontrivial (Subrepresentation ξ) := ⟨⟨⊥, ⊤, hne⟩⟩
    refine { eq_bot_or_eq_top := ?_ }
    intro W
    have hle : W.toSubmodule.map ι ≤ S := by
      rw [← hrange]
      exact LinearMap.map_le_range
    have hst : ∀ k, ∀ s ∈ W.toSubmodule.map ι, V k s ∈ W.toSubmodule.map ι := by
      rintro k s ⟨w, hw, rfl⟩
      exact ⟨ξ k w, W.apply_mem_toSubmodule k hw, (hint k w).symm⟩
    rcases hmin _ hle hst with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.map_injective_of_injective hinj
      rw [h]
      exact (Submodule.map_bot ι).symm
    · right
      apply Subrepresentation.toSubmodule_injective
      apply Submodule.map_injective_of_injective hinj
      rw [h, ← hrange, LinearMap.range_eq_map]
      rfl
  · intro v
    have hset : {k : K | ξ k v = v} = {k : K | V k (ι v) = ι v} := by
      ext k
      change ξ k v = v ↔ V k (ι v) = ι v
      rw [hint]
      exact hinj.eq_iff.symm
    rw [hset]
    exact hV (ι v)

end UpperTheory.NonzeroTypeTheory
end
end

