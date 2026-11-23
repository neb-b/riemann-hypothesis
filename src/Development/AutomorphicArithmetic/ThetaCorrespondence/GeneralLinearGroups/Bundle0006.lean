module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsJacQuot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsNeOfNeBot
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FAssocR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
public import GroundTheory.AutomorphicForms.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FDecompL
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ind₂_equiv_pair (y z : IrrGL (k := k)) {N : ℕ} (h : y.1 + z.1 = N) (hd : ∑ a, (![y, z] a).1 = N) :
    Nonempty ((ind₂ (stdSum h) (extTensor y.rep z.rep)).Equiv (prodIrr ![y, z] hd)) := by
  subst h
  exact nonempty_prod₂_equiv_prodIrr_pair y z hd

private theorem emb_unit (x : IrrGL (k := k)) : ∃ y : IrrGL (k := k), y.1 = 0 ∧ Emb x y x := by
  let o : IrrRep (GL (Fin 0) k) := IrrRep.det (k := k) (Fin 0) 1 isSmoothChar_one
  let y : IrrGL (k := k) := IrrGL.of o.ρ o.smooth o.irr
  have φ : o.ρ.Equiv y.rep := IrrGL.equivOf o.ρ o.smooth o.irr
  have κ : y.2.rep.V ≃ₗ[ℂ] ℂ := φ.toLinearEquiv.symm
  have h : 0 + x.1 = x.1 := Nat.zero_add _
  have hd : ∑ a, (![y, x] a).1 = x.1 := (Fin.sum_univ_two _).trans h
  obtain ⟨a⟩ := GlobalTheory.ProdReorder.ind₂_line_left h y.rep κ x.rep x.2.rep.smooth
  obtain ⟨b⟩ := ind₂_equiv_pair y x h hd
  exact ⟨y, rfl, hd, (a.symm.trans b).toIntertwiningMap, (a.symm.trans b).toLinearEquiv.injective⟩

private theorem emb_deg {x y z : IrrGL (k := k)} (h : Emb x y z) : y.1 + z.1 = x.1 := by
  obtain ⟨hd, -⟩ := h
  exact (Fin.sum_univ_two _).symm.trans hd

private theorem suppIn_occ {v y ρ : IrrGL (k := k)} {P : Set (IrrGL (k := k))} (h : Occ v y ρ) (hy : SuppIn y P)
    (hρ : ρ.IsCusp) (hP : ρ ∈ P) : SuppIn v P := by
  obtain ⟨hd, hne⟩ := h
  obtain ⟨A, hA, hAP⟩ := hy
  have hS := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![y, ρ]) (hd := hd) (t := ![A, {ρ}])
    (fun a => by
      fin_cases a
      · exact hA
      · exact hasSupport_self hρ) v.2.rep.irr (jhMult_ne_zero_iff.1 hne)
  refine ⟨_, hS, fun w hw => ?_⟩
  rw [Fin.sum_univ_two] at hw
  rcases Multiset.mem_add.1 hw with h | h
  · exact hAP w h
  · have : w = ρ := Multiset.mem_singleton.1 h
    exact this ▸ hP

end

theorem UpperTheory.Lit.Full.decompL :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))), ∃ y z, Emb x y z ∧ SuppIn y P ∧ FirstIn z Pᶜ := by
  intro hG hBZ k _ _ _ _ x P
  have key : ∀ (n : ℕ) (y z : IrrGL (k := k)), z.1 = n → Emb x y z → SuppIn y P →
      ∃ y z, Emb x y z ∧ SuppIn y P ∧ FirstIn z Pᶜ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro y z hz hE hS
      by_cases hF : FirstIn z Pᶜ
      · exact ⟨y, z, hE, hS, hF⟩
      unfold FirstIn at hF
      push Not at hF
      obtain ⟨q, hq, hc, hj, hP⟩ := hF
      have hP' : q 0 ∈ P := by simpa using hP
      obtain ⟨w, hw⟩ := UpperTheory.Lit.Full.embL hG hBZ k z q hq hc hj
      obtain ⟨v, hv, hvw⟩ := UpperTheory.Lit.Full.assocL hG hBZ k x y z (q 0) w hE hw
      have h1 := emb_deg hw
      have h2 := hc.1
      exact ih w.1 (by omega) v w rfl hvw (suppIn_occ hv hS hc hP')
  obtain ⟨y, hy, hE⟩ := emb_unit x
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG y
  refine key _ y x rfl hE ⟨s, hs, ?_⟩
  rw [GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport hy hs]
  simp
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FDecompR
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

theorem UpperTheory.Lit.Full.decompR :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))), ∃ y z, Emb x y z ∧ LastIn y Pᶜ ∧ SuppIn z P := by
  intro hG hBZ k _ _ _ _ x P
  have key : ∀ (n : ℕ) (y z : IrrGL (k := k)), y.1 = n → Emb x y z → SuppIn z P →
      ∃ y z, Emb x y z ∧ LastIn y Pᶜ ∧ SuppIn z P := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro y z rfl hxyz hz
      by_cases hl : LastIn y Pᶜ
      · exact ⟨y, z, hxyz, hl, hz⟩
      obtain ⟨q, hq, hc, hj, hP⟩ : ∃ (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = y.1),
          (q 1).IsCusp ∧ jm q hq y.rep ≠ 0 ∧ q 1 ∈ P := by
        by_contra hn
        exact hl fun q hq hc hj hP => hn ⟨q, hq, hc, hj, hP⟩
      obtain ⟨u, hu⟩ := UpperTheory.Lit.Full.embR hG hBZ k y q hq hc hj
      obtain ⟨v, ⟨hd, hv⟩, hxuv⟩ := UpperTheory.Lit.Full.assocR hG hBZ k x y z u (q 1) hxyz hu
      obtain ⟨A, hA, hAP⟩ := hz
      have hlt : u.1 < y.1 := by
        obtain ⟨hd', -⟩ := hu
        have h1 : u.1 + (q 1).1 = y.1 := by simpa using hd'
        have := hc.1
        omega
      refine ih u.1 hlt u v rfl hxuv ⟨∑ a, (![{q 1}, A] : Fin 2 → Multiset (IrrGL (k := k))) a, ?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := ![q 1, z]) ?_ v.2.rep.irr
          (jhMult_ne_zero_iff.1 hv)
        exact Fin.forall_fin_two.2 ⟨hasSupport_self hc, hA⟩
      · intro w hw
        have hw' : w ∈ ({q 1} : Multiset (IrrGL (k := k))) + A := by simpa using hw
        rcases Multiset.mem_add.1 hw' with h | h
        · rw [Multiset.mem_singleton.1 h]; exact hP
        · exact hAP w h
  let o : IrrGL (k := k) := ⟨0, (IrrRep.det (Fin 0) (1 : kˣ →* ℂˣ) isSmoothChar_one).cl⟩
  have hd : ∑ a, (![x, o] a).1 = x.1 := by simp [o]
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_pair_zero k x o rfl hd
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG o
  refine key x.1 x o rfl ⟨hd, φ.toIntertwiningMap, φ.toLinearEquiv.injective⟩ ⟨s, hs, ?_⟩
  rw [GlobalTheory.LocGL.SupportUnique.eq_zero_of_hasSupport (N := o.1) rfl hs]
  simp
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FZfirst
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem segTerm_smooth {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))

private theorem segTerm_irr {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  isIrreducible_twist σ.irr _

private theorem piSeg_irr (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {d : ℕ} (σ : IrrRep (GL (Fin d) k))
    (l : ℕ) : (piTensor (segTerm σ.ρ l)).IsIrreducible :=
  _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k (Fin l) (fun _ => Fin d) fun a => ⟨_, segTerm σ.ρ l a, segTerm_smooth σ l a, segTerm_irr σ l a⟩

private theorem range_eq {l d N : ℕ} (e : (Σ _ : Fin l, Fin d) ≃ Fin N) {V X : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π)
    {T : Representation ℂ (Levi k fun _ : Fin l => Fin d) X} (hs : IsSmooth T) (hi : T.IsIrreducible)
    (θ : (jac e π).Equiv T) (f g : π.IntertwiningMap (parInd e T)) (hf : f ≠ 0) :
    ∃ c : ℂ, g = c • f := by
  haveI := hi
  have hs' : GroundTheory.Automorphic.IsSmooth T := hs
  have hb := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hs').2
  have key : ∀ f : π.IntertwiningMap (parInd e T), ∃ c : ℂ, ∀ x, Model.evalOne e f x = c • θ x := by
    intro f
    obtain ⟨c, hc⟩ := hb ((Model.evalOne e f).comp θ.symm.toIntertwiningMap)
    refine ⟨c, fun x => ?_⟩
    have h1 : c • θ x = Model.evalOne e f (θ.symm (θ x)) :=
      congrArg (fun F : T.IntertwiningMap T => F (θ x)) hc
    rw [h1, θ.symm_apply_apply]
  obtain ⟨a, ha⟩ := key f
  obtain ⟨b, hb⟩ := key g
  have hinj := (Model.evalOne_bijective e hπ T).1
  have ha0 : a ≠ 0 := by
    rintro rfl
    refine hf (hinj ?_)
    refine DFunLike.ext _ _ fun x => ?_
    rw [ha, zero_smul]
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  refine ⟨b / a, hinj (DFunLike.ext _ _ fun x => ?_)⟩
  have : Model.evalOne e ((b / a) • f) x = (b / a) • Model.evalOne e f x := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  rw [this, ha, hb, smul_smul, div_mul_cancel₀ _ ha0]

private theorem isSocle_of {l d N : ℕ} (e : (Σ _ : Fin l, Fin d) ≃ Fin N) {X : Type}
    [AddCommGroup X] [Module ℂ X] (π : IrrRep (GL (Fin N) k))
    {T : Representation ℂ (Levi k fun _ : Fin l => Fin d) X} (hs : IsSmooth T) (hi : T.IsIrreducible)
    (θ : (jac e π.ρ).Equiv T) (f : π.ρ.IntertwiningMap (parInd e T)) (hf : Function.Injective f)
    (H : ∀ (τ : IrrRep (GL (Fin N) k)) (g : τ.ρ.IntertwiningMap (parInd e T)), Function.Injective g →
      Nonempty (τ.ρ.Equiv π.ρ)) : IsSocle π.ρ (parInd e T) := by
  refine ⟨π.irr, f, hf, fun S hS => ?_⟩
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  let ι : S.toRepresentation.IntertwiningMap (parInd e T) := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hsm : IsSmooth S.toRepresentation :=
    (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth (isSmooth_parInd _ _)
  obtain ⟨ψ⟩ : Nonempty (S.toRepresentation.Equiv π.ρ) :=
    H ⟨_, S.toRepresentation, hsm, hirr⟩ ι Subtype.val_injective
  have hf0 : f ≠ 0 := by
    rintro rfl
    haveI := Model.nontrivial_of_isIrreducible π.irr
    obtain ⟨v, w, h⟩ := exists_pair_ne π.V
    exact h (hf rfl)
  obtain ⟨c, hc⟩ := range_eq e π.smooth hs hi θ f (ι.comp ψ.symm.toIntertwiningMap) hf0
  refine (((isAtom_range π.irr f hf).le_iff_eq hS.1).1 fun v hv => ?_)
  have h1 : ι (ψ.symm (ψ ⟨v, hv⟩)) = c • f (ψ ⟨v, hv⟩) :=
    congrArg (fun F : π.ρ.IntertwiningMap (parInd e T) => F (ψ ⟨v, hv⟩)) hc
  rw [ψ.symm_apply_apply, ← map_smul] at h1
  exact ⟨_, h1.symm⟩

private theorem exists_unit_one_add_generator (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k) :
    ∃ z : IrrGL (k := k), IsZSeg Δ z.rep := by
  have hd : ∑ a, (Δ.term a).1 = Δ.len * Δ.d := Δ.sum_term_fst
  have H := hZ Δ Δ.start.rep Δ.start.cl_rep (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd)
  obtain ⟨f, hf⟩ := (H (Z Δ).rep).1.1 (Z Δ).cl_rep
  obtain ⟨θ⟩ := (H (Z Δ).rep).2.1 (Z Δ).cl_rep
  have hS : IsSocle (Z Δ).rep.ρ
      (multiProd (stdBlocks (fun _ : Fin Δ.len => Δ.d) hd) (segTerm Δ.start.rep.ρ Δ.len)) :=
    isSocle_of _ (Z Δ).rep (isSmooth_piTensor (segTerm_smooth _ _)) (piSeg_irr hBZ _ _) θ f hf
      fun τ g hg => IrrRep.cl_eq_iff.1 (((H τ).1.2 ⟨g, hg⟩).trans (Z Δ).cl_rep.symm)
  exact ⟨⟨_, Z Δ⟩, hd, hS.of_equiv (.refl _) (segProdEquiv Δ hd)⟩


set_option maxHeartbeats 1000000 in
private theorem glue {n s : ℕ} (π : IrrRep (GL (Fin n) k)) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n)
    (σ : ∀ a, IrrRep (GL (Fin (d a)) k)) (φ : π.ρ.IntertwiningMap (multiProd e fun a => (σ a).ρ))
    (hφ : Function.Injective φ) (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL (k := k))
    (e' : ∀ a, (Σ b, Fin (u a b).1) ≃ Fin (d a))
    (ψ : ∀ a, (σ a).ρ.IntertwiningMap (multiProd (e' a) fun b => (u a b).rep))
    (hψ : ∀ a, Function.Injective (ψ a)) :
    ∃ (w : Fin (∑ a, t a) → IrrGL (k := k)) (E : (Σ c, Fin (w c).1) ≃ Fin n)
      (Φ : π.ρ.IntertwiningMap (multiProd E fun c => (w c).rep)), Function.Injective Φ ∧
        ∀ c, w c = u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 := by
  obtain ⟨E0, ⟨χ⟩⟩ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1) e'
    (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep) (Fin n) e
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a),
      Fin (u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2).1) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F).trans E0
  obtain ⟨ω⟩ := _root_.GlobalTheory.SmGL.BlockRename.multiProd_rename (k := k) F (_root_.GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  let Ψ := parIndMap e (GlobalTheory.CompanionTheory.CuspEmbed.piTensorMap ψ)
  have hΨ : Function.Injective Ψ :=
    GlobalTheory.CompanionTheory.CuspEmbed.parIndMap_injective e _ (GlobalTheory.CompanionTheory.CuspEmbed.piTensorMap_injective ψ hψ)
  exact ⟨fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, E,
    (χ.trans ω).toIntertwiningMap.comp (Ψ.comp φ),
    (χ.trans ω).toLinearEquiv.injective.comp (hΨ.comp hφ), fun _ => rfl⟩

private theorem embeds' (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (x : IrrGL (k := k)) : ∃ (s : ℕ) (u : Fin s → IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin x.1),
      (∀ a, (u a).IsCusp) ∧ ∃ φ : x.rep.IntertwiningMap (multiProd e fun a => (u a).rep), Function.Injective φ :=
  GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep)

private theorem word (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)} (hZ : IsSegmentClass k Z) (Δ : Segment k) {N : ℕ}
    (π : IrrRep (GL (Fin N) k)) (h : IsZSeg Δ π.ρ) {s : ℕ} (u : Fin s → IrrGL (k := k)) (hu : ∀ a, (u a).IsCusp)
    (e : (Σ a, Fin (u a).1) ≃ Fin N) (φ : π.ρ.IntertwiningMap (multiProd e fun a => (u a).rep))
    (hφ : Function.Injective φ) (a : Fin s) : u a = Δ.first.nu (a : ℕ) := by
  obtain rfl : Δ.len * Δ.d = N := h.deg_eq
  have h1 : HasSupport π.ρ (Finset.univ.val.map u) :=
    ⟨s, u, rfl, π.irr, fun a => ⟨(hu a).1, IrrRep.irr _, (hu a).2⟩, e, .of_injective φ hφ⟩
  have h2 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ h1 h.hasSupport
  obtain rfl : Δ.len = s := by simpa using (congrArg Multiset.card h2).symm
  have h3 : ∀ a, ∃ c : IrrCl (GL (Fin Δ.d) k), u a = ⟨Δ.d, c⟩ := by
    intro a
    have : u a ∈ Δ.ms := h2 ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ a)
    obtain ⟨b, hb⟩ := Segment.mem_ms.1 this
    exact ⟨(Δ.term b).2, hb.symm⟩
  choose c hc using h3
  obtain rfl : u = fun a => ⟨Δ.d, c a⟩ := funext hc
  obtain ⟨θ⟩ := (hZ Δ Δ.start.rep Δ.start.cl_rep e π).2.1 (h.cl_eq hZ)
  have hT : (piTensor fun a => (c a).rep.ρ).IsIrreducible :=
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k (Fin Δ.len) (fun _ => Fin Δ.d) fun a => (c a).rep
  haveI := Model.nontrivial_of_isIrreducible π.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : π.V)
  have h4 := GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac e hT φ ⟨v, fun h0 => hv (hφ (h0.trans (map_zero φ).symm))⟩
  have h5 : IsSubquotient (piTensor fun a => (c a).rep.ρ) (piTensor (segTerm Δ.start.rep.ρ Δ.len)) :=
    (jhMult_ne_zero_iff.1 (ENat.one_le_iff_ne_zero.1 h4)).trans
      (.of_injective θ.toIntertwiningMap θ.toLinearEquiv.injective)
  have h6 := GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (segTerm Δ.start.rep.ρ Δ.len) a (c a).rep.irr
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun a => (c a).rep.ρ) (fun a => (c a).rep.irr) a).trans
      (GlobalTheory.LocGL.SupportUnique.isSubquotient_comp h5 _))
  obtain ⟨ω⟩ := h6.nonempty_equiv (c a).rep.irr (segTerm_irr _ _ a)
  have ω' := ω.symm.trans (Δ.first.twEquiv _ (isSmoothChar_absPow ((a : ℕ) : ℂ)))
  exact (IrrGL.of_rep (⟨Δ.d, c a⟩ : IrrGL (k := k))).symm.trans
    ((IrrGL.of_eq_of.2 ⟨ω'⟩).trans (IrrGL.of_rep (Δ.first.nu (a : ℕ))))

end

theorem UpperTheory.Lit.Full.zfirst :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k), (∃ z : IrrGL (k := k), IsZSeg Δ z.rep) ∧ ∀ z : IrrGL (k := k), IsZSeg Δ z.rep → FirstIn z {Δ.first} := by
  intro hG hBZ hP k _ _ _ _ Δ
  obtain ⟨Z, -, hZ, -⟩ := hP k
  refine ⟨exists_unit_one_add_generator hBZ hZ Δ, fun z hz q hq hc hj => ?_⟩
  obtain ⟨y, hd, φ, hφ⟩ := UpperTheory.Lit.Full.embL hG hBZ k z q hq hc hj
  choose t u e' hu ψ hψ using fun a : Fin 2 => embeds' hG hBZ (![q 0, y] a)
  obtain ⟨w, E, Φ, hΦ, hwu⟩ := glue z.2.rep (fun a => (![q 0, y] a).1) (stdBlocks (fun a => (![q 0, y] a).1) hd)
    (fun a => (![q 0, y] a).2.rep) φ hφ t u e' ψ hψ
  have hw := word hG hBZ hZ Δ z.2.rep hz w (fun c => hwu c ▸ hu _ _) E Φ hΦ
  have h1 : HasSupport (q 0).rep (Finset.univ.val.map (u 0)) :=
    ⟨t 0, u 0, rfl, (q 0).2.rep.irr, fun a => ⟨(hu 0 a).1, IrrRep.irr _, (hu 0 a).2⟩, e' 0,
      .of_injective (ψ 0) (hψ 0)⟩
  have h2 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ h1 (hasSupport_self hc)
  have h3 : t 0 = 1 := by simpa using congrArg Multiset.card h2
  let b : Fin (t 0) := ⟨0, by omega⟩
  have h4 : u 0 b = q 0 :=
    Multiset.mem_singleton.1 (h2 ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ b))
  have h5 := hw (finSigmaFinEquiv ⟨0, b⟩)
  have h6 : ((finSigmaFinEquiv ⟨0, b⟩ : Fin (∑ a, t a)) : ℕ) = 0 := by
    rw [finSigmaFinEquiv_apply]; simp [b]
  rw [hwu, h6, Nat.cast_zero, IrrGL.nu_zero, Equiv.symm_apply_apply] at h5
  exact h4.symm.trans h5
end

