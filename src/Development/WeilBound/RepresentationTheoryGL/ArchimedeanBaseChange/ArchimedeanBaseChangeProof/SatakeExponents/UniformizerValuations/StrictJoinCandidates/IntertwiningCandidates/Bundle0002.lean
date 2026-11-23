module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PolynomialPairSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.IsoInv
section
noncomputable section

namespace PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

open GlobalTheory.PRep

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  show (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}

theorem symm_intertwines (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    ∀ g w, L.symm (ρ' g w) = ρ g (L.symm w) := by
  intro g w
  apply L.injective
  rw [hL, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem map_fixed_le (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') ≤ fixed ρ' K := by
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_fixed_iff] at hv
  rw [mem_fixed_iff]
  intro h
  simp only [LinearEquiv.coe_coe]
  rw [← hL, hv h]

theorem map_fixed_eq (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') = fixed ρ' K := by
  refine le_antisymm (map_fixed_le L hL K) ?_
  intro w hw
  have hm : (L.symm : V' →ₗ[ℂ] V) w ∈ (fixed ρ' K).map (L.symm : V' →ₗ[ℂ] V) := ⟨w, hw, rfl⟩
  refine ⟨L.symm w, map_fixed_le L.symm (symm_intertwines L hL) K hm, ?_⟩
  simp

def imap (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) : ρ.IntertwiningMap ρ' :=
  ⟨(L : V →ₗ[ℂ] V'), fun g => by ext v; exact hL g v⟩

theorem isSubquotient_of (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    GlobalTheory.SmGL.IsSubquotient ρ' ρ :=
  GlobalTheory.SmGL.IsSubquotient.of_surjective (imap L hL) (fun w => ⟨L.symm w, L.apply_symm_apply w⟩)

end PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open GlobalTheory.PRep IsoInverse

theorem IsoInv_holds : IsoInv := by
  intro G V V' _ _ _ _ _ ρ ρ' ⟨e⟩ K
  have hL : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining (f := e.toIntertwiningMap) (g := g) (v := v)
  have hL' := symm_intertwines e.toLinearEquiv hL
  let F := e.toLinearEquiv.ofSubmodules _ _ (map_fixed_eq e.toLinearEquiv hL K)
  refine ⟨fun W _ _ τ => ⟨fun h => h.trans (isSubquotient_of e.toLinearEquiv.symm hL'),
    fun h => h.trans (isSubquotient_of e.toLinearEquiv hL)⟩, F.finrank_eq,
    ⟨fun _ => F.finiteDimensional, fun _ => F.symm.finiteDimensional⟩⟩

end PositivityTheory.Rg.BcB.F.FX.Bo
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.LevOpen
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcB.G8
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.LevelOpenness

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Rd.LevOC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def LOk (d : LocData E n) : Prop :=
  ∀ a ≤ n, ∀ w ∈ d.S₀ ∪ d.Bad, IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w))

theorem LOk_of_ok (d : LocData E n) (hd : d.Ok) : LOk d := fun a ha w hw => (L_open_le d hd a ha w hw).1

theorem lev_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev a w : Set (GLw a w × GLw (n - a) w)) := by
  unfold LocData.lev
  split_ifs with h1 h2
  · exact iwahori_pair_isOpen a (n - a) w
  · exact hd a ha w h2
  · exact maximal_pair_isOpen a (n - a) w

theorem lev₂_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) := by
  unfold LocData.lev₂
  split_ifs with h2
  · exact hd a ha w h2
  · exact maximal_pair_isOpen a (n - a) w

theorem C_open (d : LocData E n) (hd : LOk d) (a : ℕ) (ha : a ≤ n) {S : Set (Pl E)} (i : Slot S) :
    IsOpen (C d a i) := by
  rcases i with w | w
  · exact lev_open d hd a ha w.1
  · exact lev₂_open d hd a ha w.1

theorem gSet_open' (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (gSet Sec d a) := by
  have hSl' := hSl E a (n - a) Sec hS
  obtain ⟨hKo1, -⟩ := _root_.GlobalTheory.CompanionTheory.IntegralPoints.kfOC E a
  obtain ⟨hKo2, -⟩ := _root_.GlobalTheory.CompanionTheory.IntegralPoints.kfOC E (n - a)
  set U : Set (Hf E a (n - a)) := (((Kf E a).prod (Kf E (n - a)) : Subgroup (Hf E a (n - a))) : Set (Hf E a (n - a)))
    with hU
  have hUo : IsOpen U := by
    rw [hU, Subgroup.coe_prod]
    exact hKo1.prod hKo2
  have hF := (Filter.eventually_cofinite.1 (C_cof d a (S := Sec)))
  set V : Set (Hf E a (n - a)) := U ∩ ⋂ i ∈ {i : Slot Sec | ¬ C d a i = (K2 a (n - a) i.pl : Set _)},
    (i.cp a (n - a)) ⁻¹' C d a i with hV
  have hVo : IsOpen V :=
    hUo.inter (hF.isOpen_biInter fun i _ => (C_open d hd a ha i).preimage (hSl'.2.1 i))
  have h1V : (1 : Hf E a (n - a)) ∈ V := by
    refine ⟨one_mem _, Set.mem_iInter₂.2 fun i _ => ?_⟩
    have h1 : (1 : Hf E a (n - a)) ∈ gSet Sec d a := (levSub Sec d a).one_mem
    rw [gSet_eq] at h1
    exact h1 i
  have hVsub : V ⊆ gSet Sec d a := by
    intro x hx
    rw [gSet_eq]
    intro i
    by_cases hi : C d a i = (K2 a (n - a) i.pl : Set _)
    · rw [hi]
      exact (hSl'.2.2.2.2.2.1 x).1 hx.1 i
    · exact Set.mem_iInter₂.1 hx.2 i hi
  exact Subgroup.isOpen_of_mem_nhds (levSub Sec d a) (g := 1) (Filter.mem_of_superset (hVo.mem_nhds h1V) hVsub)

theorem g₁_open (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₁ Sec d a : Set (GL (Fin a) (Af E))) := by
  rw [g₁_coe]
  exact (gSet_open' hSl hS d hd a ha).preimage (continuous_id.prodMk continuous_const)

theorem g₂_open (hSl : Slots) {Sec : Set (Pl E)} (hS : IsSection Sec) (d : LocData E n) (hd : LOk d) (a : ℕ)
    (ha : a ≤ n) : IsOpen (g₂ Sec d a : Set (GL (Fin (n - a)) (Af E))) := by
  rw [g₂_coe]
  exact (gSet_open' hSl hS d hd a ha).preimage (continuous_const.prodMk continuous_id)

theorem loc_LOk {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S : Finset (Pl E)} (F₀ : Frame0 hR π S)
    (T' : Finset (Pl E)) c e b : LOk (F₀.loc T' c e b) :=
  fun a ha w hw => LOk_of_ok F₀.d₀ F₀.ok₀ a ha w hw

end PositivityTheory.Rg.BcB.F.FX.Bo.LevelOpenness

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F

theorem LevOpen_holds : LevOpen := by
  intro hR E _ _ _ n π S F₀ T' c e b a ha
  have hd := LevelOpenness.loc_LOk F₀ T' c e b
  exact ⟨LevelOpenness.g₁_open slots F₀.hSec _ hd a ha, LevelOpenness.g₂_open slots F₀.hSec _ hd a ha⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictEqv
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

namespace StrictEquivalence

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem siso_symm (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) (hx : _root_.GlobalTheory.CuspRep.IsStable x.2) (h : SIso x y) : SIso y x := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨h, hI⟩ := h
  simp only at h
  subst h
  exact ⟨rfl, F5.Bo.isoV_symm' hx hI⟩

theorem siso_trans (x y z : Σ M : ℕ, Submodule ℂ (Sm E M)) (h : SIso x y) (h' : SIso y z) : SIso x z := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain ⟨z1, z2⟩ := z
  obtain ⟨h, hI⟩ := h
  obtain ⟨h', hI'⟩ := h'
  simp only at h h'
  subst h h'
  exact ⟨rfl, F5.Bo.isoV_trans' hI hI'⟩

theorem forall₂_flip_of {α : Type} {R S : α → α → Prop} {p : α → Prop} (hRS : ∀ x y, p x → R x y → S y x) :
    ∀ {l l' : List α}, (∀ x ∈ l, p x) → List.Forall₂ R l l' → List.Forall₂ S l' l
  | _, _, _, List.Forall₂.nil => List.Forall₂.nil
  | _, _, hp, List.Forall₂.cons hab htl =>
      List.Forall₂.cons (hRS _ _ (hp _ (List.mem_cons_self ..)) hab)
        (forall₂_flip_of hRS (fun x hx => hp x (List.mem_cons_of_mem _ hx)) htl)

theorem forall₂_trans_of {α : Type} {R : α → α → Prop} (hR : ∀ x y z, R x y → R y z → R x z) :
    ∀ {l l' l'' : List α}, List.Forall₂ R l l' → List.Forall₂ R l' l'' → List.Forall₂ R l l''
  | _, _, _, List.Forall₂.nil, List.Forall₂.nil => List.Forall₂.nil
  | _, _, _, List.Forall₂.cons hab htl, List.Forall₂.cons hbc htl' =>
      List.Forall₂.cons (hR _ _ _ hab hbc) (forall₂_trans_of hR htl htl')

theorem parts_stable {n : ℕ} (P : Pre E n) : ∀ x ∈ parts P, _root_.GlobalTheory.CuspRep.IsStable x.2 := by
  intro x hx
  rw [parts, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact (P.discrete i).stable

end StrictEquivalence

open StrictEquivalence in
theorem StrictEqv_holds : StrictEqv := by
  intro E _ _ _ n P P' P''
  refine ⟨fun ⟨hF, hc, hm⟩ => ⟨forall₂_flip_of (p := fun x => _root_.GlobalTheory.CuspRep.IsStable x.2) (fun x y hx h => siso_symm x y hx h)
      (parts_stable P) hF, hc.symm, fun i => ?_⟩, fun ⟨hF, hc, hm⟩ ⟨hF', hc', hm'⟩ =>
      ⟨forall₂_trans_of siso_trans hF hF', hc.trans hc', fun i => ?_⟩⟩
  · rw [hm (Fin.cast hc.symm i)]
    congr 1
  · rw [hm i, hm' (Fin.cast hc i)]
    congr 1

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoinHolds
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw.StrictJoinAlt

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasInf_map {a : ℕ} {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (χ : HChar E) :
    HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map]; exact h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

theorem isoV_map {a : ℕ} {V V' : Submodule ℂ (Sm E a)} (hV : IsoV V V') (χ : HChar E) :
    IsoV (V.map (mulChi a χ).toLinearMap) (V'.map (mulChi a χ).toLinearMap) := by
  obtain ⟨T, hT⟩ := hV
  let M := mulChi a χ
  refine ⟨((M.submoduleMap V).symm.trans T).trans (M.submoduleMap V'), ?_⟩
  intro o φ ψ hψ
  set φ₀ := (M.submoduleMap V).symm φ with hφ₀
  set ψ₀ := (M.submoduleMap V).symm ψ with hψ₀
  have eφ : φ.1 = M φ₀.1 := by
    have := congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply φ); rw [← this]; rfl
  have eψ : ψ.1 = M ψ₀.1 := by
    have := congrArg Subtype.val ((M.submoduleMap V).apply_symm_apply ψ); rw [← this]; rfl
  have key : ψ₀.1 = ((opMul χ o : ℂˣ) : ℂ) • act o φ₀.1 + opAdd χ o • φ₀.1 := by
    apply M.injective
    rw [← eψ, hψ, eφ]
    exact act_mulChi χ o φ₀.1
  have hmem : act o φ₀.1 ∈ V := by
    have : act o φ₀.1 = ((opMul χ o : ℂˣ) : ℂ)⁻¹ • (ψ₀.1 - opAdd χ o • φ₀.1) := by
      rw [key, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    rw [this]
    exact V.smul_mem _ (V.sub_mem ψ₀.2 (V.smul_mem _ φ₀.2))
  have hψ' : ψ₀ = ((opMul χ o : ℂˣ) : ℂ) • (⟨act o φ₀.1, hmem⟩ : V) + opAdd χ o • φ₀ := Subtype.ext key
  have h1 := hT o φ₀ ⟨act o φ₀.1, hmem⟩ rfl
  change (M (T ψ₀).1) = act o (M (T φ₀).1)
  rw [act_mulChi, hψ', map_add (f := _), map_smul, map_smul]
  simp only [Submodule.coe_add, Submodule.coe_smul, h1]
  rfl

theorem sIso_tw {x y : Σ M : ℕ, Submodule ℂ (Sm E M)} (h : SIso x y) (χ : HChar E) :
    SIso (twPart χ x) (twPart χ y) := by
  obtain ⟨N, V⟩ := x
  obtain ⟨N', V'⟩ := y
  obtain ⟨e, hi⟩ := h
  dsimp only at e
  subst e
  exact ⟨rfl, isoV_map hi χ⟩

def SInf (x y : Σ M : ℕ, Submodule ℂ (Sm E M)) : Prop :=
  ∀ τ, ∃ m, HasInfCharGL x.2 τ m ∧ HasInfCharGL y.2 τ m

theorem length_parts {n : ℕ} (P : Pre E n) : (parts P).length = P.c := by simp [parts]

theorem sInf_tw {a : ℕ} {P P' : Pre E a} (h : Strict P P') (χ : HChar E) :
    List.Forall₂ SInf ((parts P).map (twPart χ)) ((parts P').map (twPart χ)) := by
  obtain ⟨hc, hm⟩ := h.2
  rw [List.forall₂_iff_get]
  refine ⟨by simp [length_parts, hc], fun i h₁ h₂ => ?_⟩
  intro τ
  have hi : i < P.c := by simpa [length_parts] using h₁
  refine ⟨(P.m ⟨i, hi⟩ τ).map (· + expo χ τ), ?_, ?_⟩
  · have e : ((parts P).map (twPart χ)).get ⟨i, h₁⟩ = twPart χ ⟨P.N ⟨i, hi⟩, P.V ⟨i, hi⟩⟩ := by
      simp [parts]
    rw [e]
    exact hasInf_map (P.inf _ τ) χ
  · have e : ((parts P').map (twPart χ)).get ⟨i, h₂⟩ =
        twPart χ ⟨P'.N (Fin.cast hc ⟨i, hi⟩), P'.V (Fin.cast hc ⟨i, hi⟩)⟩ := by
      simp [parts]
    rw [e, hm ⟨i, hi⟩]
    exact hasInf_map (P'.inf _ τ) χ

theorem strict_of {n : ℕ} {P P' : Pre E n} (h₁ : List.Forall₂ SIso (parts P) (parts P'))
    (h₂ : List.Forall₂ SInf (parts P) (parts P')) : Strict P P' := by
  have hc : P.c = P'.c := by rw [← length_parts, ← length_parts]; exact h₂.length_eq
  refine ⟨h₁, hc, fun i => funext fun τ => ?_⟩
  have hi : i.1 < (parts P).length := by rw [length_parts]; exact i.2
  have hi' : i.1 < (parts P').length := by rw [length_parts, ← hc]; exact i.2
  obtain ⟨m, hm, hm'⟩ := (List.forall₂_iff_get.1 h₂).2 i.1 hi hi' τ
  have e : (parts P).get ⟨i.1, hi⟩ = ⟨P.N i, P.V i⟩ := by simp [parts]
  have e' : (parts P').get ⟨i.1, hi'⟩ = ⟨P'.N (Fin.cast hc i), P'.V (Fin.cast hc i)⟩ := by
    simp only [parts, List.get_ofFn]; rfl
  rw [e] at hm
  rw [e'] at hm'
  have e1 := LemDd.InfUniq_holds E _ _ τ _ _ (P.discrete i).ne_bot (P.inf i τ) hm
  have e2 := LemDd.InfUniq_holds E _ _ τ _ _ (P'.discrete _).ne_bot (P'.inf _ τ) hm'
  rw [e1, e2]

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw.StrictJoinAlt

namespace PositivityTheory.Rg.BcB.F.FX.Bo.Tw

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.FX.Bo StrictJoinAlt

theorem StrictJoin_holds : StrictJoin := by
  intro E _ _ _ n a b χ₁ χ₂ Pa Pa' Pb Pb' D D' hJ hJ' ha hb
  refine strict_of ?_ ?_
  · rw [hJ, hJ']
    exact List.rel_append
      (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (ha.1.imp fun _ _ h => sIso_tw h χ₁)))
      (List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (hb.1.imp fun _ _ h => sIso_tw h χ₂)))
  · rw [hJ, hJ']
    exact List.rel_append (sInf_tw ha χ₁) (sInf_tw hb χ₂)

end PositivityTheory.Rg.BcB.F.FX.Bo.Tw

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictProd
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

theorem StrictProd_holds : StrictProd := by
  intro E _ _ _ n P P' hS w
  obtain ⟨c, N, h, V, σ, m, pos, disc, loc, inf⟩ := P
  obtain ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ := P'
  obtain ⟨hF, hc, -⟩ := hS
  simp only at hc
  subst hc
  have key : ∀ i : Fin c, SIso (E := E) ⟨N i, V i⟩ ⟨N' i, V' i⟩ := by
    intro i
    have := (List.forall₂_iff_get.1 hF).2 i.1 (by simp [parts]) (by simp [parts])
    simpa [parts] using this
  have hN : N = N' := funext fun i => (key i).1
  subst hN
  have hσ : ∀ i, Nonempty ((σ i w).ρ.Equiv (σ' i w).ρ) := by
    intro i
    obtain ⟨hNi, hiso⟩ := key i
    have hl : IsLocCompGL (V' i) w (σ i w) := Bo.LocIso_holds E (N i) (V i) (V' i) hiso w (σ i w) (loc i w)
    exact GlobalTheory.LocGL.IrrGL.of_eq_of.1 (Bo.LocUniq_holds E (N i) (V' i) (disc' i) w _ _ hl (loc' i w))
  exact ⟨GlobalTheory.LocGL.multiProdEquiv _ fun i => (hσ i).some⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
end

