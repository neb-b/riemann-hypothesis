module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GMain
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem gMain (h1 : DeterminantVectorProp) (h2 : UnramifiedTwistProp) (h3 : SumOverListProp) (h4a : IsotypicComponentProp)
    (h4b : ScalarOnInertiaProp) (h5 : SphericalOfUnramifiedProp) (h5' : SphericalUnramifiedProp) (h6 : TwistRestrictionProp) (h6' : UntwistRestrictionProp)
    (h7 : ProductRestrictionProp) (h8a : CuspidalSupportProp) (h8b : ProductIrreducibleProp) (h9 : ArtinInertiaProp) : GMain := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL hLit s d η hη hdist x hd
  have hψ : ∀ b, IsSmooth ((η b).comp a) := fun b => ha.smooth (hη b)
  constructor
  · rintro ⟨h0, hc⟩
    obtain ⟨v, hv, hsum⟩ := h4a E Ω A w h (rc x) s d (fun b => (η b).comp a) hψ hdist h0 hc
    have hv' : ∀ b, ∃ v' : WD h, v'.unr ∧ v'.lpDim = d b ∧
        v b = v'.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨v', hu, hdim, he⟩ := h4b E Ω A w h (v b) ((η b).comp a) (hψ b) (hv b).1
        (fun t => by rw [(hv b).2.1]; exact (hv b).2.2 t)
      exact ⟨v', hu, hdim.trans (hv b).2.1, he⟩
    choose v' hu hdim he using hv'
    choose Xs instA instM σ hs hi hsph hrc using fun b => h5 E Ω A w h a ha ε rc hL (d b) (v' b) (hu b) (hdim b)
    letI := instA
    letI := instM
    choose hs' hi' hrc' using fun b => h6 E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
    have hdet : ∀ b, HasDetVec (twist (σ b) (detChar (Fin (d b)) (η b))) (η b) :=
      fun b => (h1 _ (d b) (Xs b) (σ b) (η b)).1 (hsph b)
    have hdistU : ∀ b c, b ≠ c → ∃ u : (w.adicCompletion E)ˣ,
        valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 ∧ η b u ≠ η c u := by
      intro b c hbc
      obtain ⟨t, ht⟩ := hdist b c hbc
      exact ⟨a (ineIncl h t), (h9 E Ω A w h a ha).1 t, ht⟩
    have hI := h8b h8a hLit _ s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' η hη hdet hdistU
    have hrcP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' hI
    have heq : rc (IrrGL.of (multiProd (stdBlocks d hd) fun b => twist (σ b) (detChar (Fin (d b)) (η b)))
        (isSmooth_parInd _ _) hI) = rc x := by
      rw [hrcP, hsum]
      congr 1
      refine List.ofFn_inj.2 (funext fun b => ?_)
      rw [hrc' b, hrc b, he b]
    have e2 := (hL.bij.1 heq).trans (IrrGL.of_rep x).symm
    obtain ⟨e⟩ := IrrGL.of_eq_of.1 e2
    exact ⟨Xs, instA, instM, fun b => twist (σ b) (detChar (Fin (d b)) (η b)), hs', hi', hdet, ⟨e.symm⟩⟩
  · rintro ⟨Xs, instA, instM, σ, hs, hi, hdet, ⟨e⟩⟩
    letI := instA
    letI := instM
    have hI : (multiProd (stdBlocks d hd) σ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e x.2.rep.irr
    have hx : x = IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI :=
      (IrrGL.of_rep x).symm.trans (IrrGL.of_eq_of.2 ⟨e⟩)
    have hfac : ∀ b, ∃ u : WD h, u.unr ∧ u.lpDim = d b ∧
        rc (IrrGL.of (σ b) (hs b) (hi b)) = u.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨hs', hi', hr⟩ := h6' E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
      exact ⟨_, h5' E Ω A w h a ha ε rc hL (d b) (Xs b) _ hs' hi' ((h1 _ (d b) (Xs b) (σ b) (η b)).2 (hdet b)),
        hL.dim _, hr⟩
    choose u hu hud hur using hfac
    have hl := h3 E Ω A w h (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))
    have hP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs σ hs hi hI
    rw [← hx] at hP
    rw [hP]
    refine ⟨hl.1.2 fun y hy => ?_, fun t => ?_⟩
    · simp only [List.mem_ofFn, Set.mem_range] at hy
      obtain ⟨b, rfl⟩ := hy
      rw [hur b]
      exact (h2 E Ω A w h (u b) _ (hψ b) (hu b)).1
    · rw [hl.2, List.map_ofFn, List.prod_ofFn]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Function.comp_apply]
      rw [hur b, (h2 E Ω A w h (u b) _ (hψ b) (hu b)).2 t, hud b]
      rfl

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPowAlgebraMap
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

abbrev red (n r : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ r) :=
  Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ r))


variable (k) in
def H (n r : ℕ) : Subgroup (GL (Fin n) k) := (red (k := k) n r).ker.map (incl n)

theorem inPow_algebraMap (r : ℕ) (y : 𝒪[k]) :
    InPow r (algebraMap 𝒪[k] k y) ↔ y ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  constructor
  · rintro ⟨z, hz, e⟩
    have : z = y := Subtype.val_injective e
    exact this ▸ hz
  · intro h
    exact ⟨y, h, rfl⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem entry_sub (n : ℕ) (u : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (((incl n u : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) =
      algebraMap 𝒪[k] k ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) := by
  split_ifs <;> simp [Matrix.GeneralLinearGroup.map]

theorem red_eq_one_iff (n r : ℕ) (u : GL (Fin n) 𝒪[k]) :
    red (k := k) n r u = 1 ↔ ∀ i j, ((u : Matrix (Fin n) (Fin n) 𝒪[k]) i j - if i = j then 1 else 0) ∈
      IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  rw [Units.ext_iff]
  constructor
  · intro h i j
    have h' := congrFun (congrFun h i) j
    rw [← Ideal.Quotient.eq]
    split_ifs with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
  · intro h
    ext i j
    have h' := Ideal.Quotient.eq.2 (h i j)
    split_ifs at h' with hij
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'
    · simpa [Matrix.GeneralLinearGroup.map, hij] using h'

theorem mem_KC_iff (n r : ℕ) (g : GL (Fin n) k) : g ∈ KC k n r ↔ g ∈ H k n r := by
  constructor
  · rintro ⟨⟨u, rfl⟩, hP⟩
    refine ⟨u, (red_eq_one_iff n r u).2 fun i j => ?_, rfl⟩
    have := hP i j
    rwa [entry_sub, inPow_algebraMap] at this
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [entry_sub, inPow_algebraMap]
    exact (red_eq_one_iff n r u).1 hu i j

theorem coe_H (n r : ℕ) : (H k n r : Set (GL (Fin n) k)) = KC k n r :=
  Set.ext fun g => (mem_KC_iff n r g).symm

theorem isOpen_inPow (r : ℕ) : IsOpen {x : k | InPow r x} := by
  let A : AddSubgroup k :=
    (IsLocalRing.maximalIdeal 𝒪[k] ^ r).toAddSubgroup.map (algebraMap 𝒪[k] k).toAddMonoidHom
  have hA : (A : Set k) = {x : k | InPow r x} := by
    ext x
    simp only [A, AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_ofPred_eq, InPow]
    rfl
  rw [← hA]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (IsDiscreteValuationRing.not_a_field 𝒪[k])
  have hc : (algebraMap 𝒪[k] k w) ^ r ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h
    exact hw0 (Subtype.val_injective h)
  refine A.isOpen_of_mem_nhds (g := 0) ?_
  rw [mem_nhds_iff]
  refine ⟨(fun x => (algebraMap 𝒪[k] k w) ^ r * x) '' (𝒪[k] : Set k), ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨w ^ r * ⟨y, hy⟩, Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw r), ?_⟩
    show algebraMap 𝒪[k] k (w ^ r * ⟨y, hy⟩) = algebraMap 𝒪[k] k w ^ r * y
    rw [map_mul, map_pow]
    rfl
  · have := (Homeomorph.mulLeft₀ _ hc).isOpenMap _ (Valuation.isOpen_integer (v := valuation k))
    simpa using this
  · exact ⟨0, zero_mem _, mul_zero _⟩

theorem isOpen_KC (n r : ℕ) : IsOpen (KC k n r) := by
  have e : KC k n r = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j - if i = j then 1 else 0) ⁻¹'
        {x : k | InPow r x} := by
    ext g
    simp only [KC, Set.mem_ofPred_eq, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_inPow r).preimage ?_)
  have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
  fun_prop

end UpperTheory.TNZ.Grp.P_KC

namespace UpperTheory.TNZ.Grp

open P_KC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_KC {n : ℕ} (G : Grp k n) : CompactOpenKernelProp G := by
  intro hB r
  refine ⟨?_, ?_, isOpen_KC n r, fun g hg => hg.1, ?_⟩
  · show ((Subgroup.closure (KC k n r) : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = KC k n r
    rw [← coe_H, Subgroup.closure_eq]
  · intro g hg u hu
    obtain ⟨v, rfl⟩ := hg
    obtain ⟨w, hw, rfl⟩ := (mem_KC_iff n r u).1 hu
    refine (mem_KC_iff n r _).2 ⟨v * w * v⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hw ⊢
    simp [hw]
  · intro hr g hg
    refine ⟨hg.1, fun i j hij => ?_⟩
    have hne : i ≠ j := fun h => (ne_of_lt hij) (h ▸ rfl)
    obtain ⟨y, hy, e⟩ := hg.2 i j
    rw [if_neg hne, sub_zero] at e
    have hc : cc G.μ (G.bl j) (G.bl i) ≤ r := (hB.2.1 (G.bl j) (G.bl i)).le.trans hr
    exact ⟨y, Ideal.pow_le_pow_right hc hy, e⟩

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPowMono
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace P_PJ

variable {n : ℕ} (G : Grp k n)

theorem inPow_mono {a b : ℕ} (hab : a ≤ b) {x : k} (hx : InPow b x) : InPow a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩

theorem KC_mono {a b : ℕ} (hab : a ≤ b) : KC k n b ⊆ KC k n a := fun _ hg =>
  ⟨hg.1, fun i j => inPow_mono hab (hg.2 i j)⟩

def Jsub (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) : Subgroup (GL (Fin n) k) where
  carrier := G.JSet
  one_mem' := h1
  mul_mem' := fun ha hb => hmul _ ha _ hb
  inv_mem' := fun ha => hinv _ ha

theorem Jg_sub (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) {g : GL (Fin n) k} (hg : g ∈ G.Jg) : g ∈ G.JSet :=
  (Subgroup.closure_le (K := Jsub G h1 hmul hinv)).2 (fun _ hx => hx) hg

theorem Jg_le_KO (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) : G.Jg ≤ KO k (Fin n) := fun _ hg =>
  (Jg_sub G h1 hmul hinv hg).1

theorem core (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    (hlM : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, G.lam (g * h) = G.lam g * G.lam h)
    (hlB : G.lam 1 = 1 ∧ (∀ g, G.lam g ≠ 0) ∧ ∀ g ∈ KC k n G.lev, G.lam g = 1)
    (hKC : ∀ r : ℕ, ((KCg k n r : Set (GL (Fin n) k)) = KC k n r) ∧
      (∀ g ∈ KO k (Fin n), ∀ u ∈ KC k n r, g * u * g⁻¹ ∈ KC k n r) ∧ IsOpen (KC k n r) ∧
        KC k n r ⊆ (KO k (Fin n) : Set _) ∧ (G.lev ≤ r → KC k n r ⊆ G.JSet))
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ) (hr : G.lev ≤ r) :
    Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) ∧
    ∀ v : V, (∀ u ∈ KC k n r, π u v = v) →
      G.PJ π r v ∈ G.Eig π ∧ (∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v) ∧
      (v ∈ G.Eig π → G.PJ π r v = (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) • v) := by
  obtain ⟨hKCeq, hKCn, hKCo, -, -⟩ := hKC r
  have hJ : ∀ {g : GL (Fin n) k}, g ∈ G.Jg → g ∈ G.JSet := fun hg => Jg_sub G h1 hmul hinv hg
  have hJK := Jg_le_KO G h1 hmul hinv
  have hKCmem : ∀ {u : GL (Fin n) k}, u ∈ KCg k n r → u ∈ KC k n r := fun hu => by
    rw [← hKCeq]; exact hu

  have hfin : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := by
    have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO
    have : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 hc
    have ho : IsOpen (((KCg k n r).subgroupOf (KO k (Fin n)) : Subgroup (KO k (Fin n))) : Set (KO k (Fin n))) := by
      have : IsOpen (KCg k n r : Set (GL (Fin n) k)) := by rw [hKCeq]; exact hKCo
      exact this.preimage continuous_subtype_val
    have : Finite (KO k (Fin n) ⧸ (KCg k n r).subgroupOf (KO k (Fin n))) := Subgroup.quotient_finite_of_isOpen _ ho
    have h0 : (KCg k n r).relIndex (KO k (Fin n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h0' : (KCg k n r).relIndex G.Jg ≠ 0 := fun h => h0 (Subgroup.relIndex_eq_zero_of_le_right hJK h)
    have : ((KCg k n r).subgroupOf G.Jg).FiniteIndex := ⟨h0'⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  refine ⟨hfin, fun v hv => ?_⟩
  let _ : Fintype (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := Fintype.ofFinite _
  have hN : ((KCg k n r).subgroupOf G.Jg).Normal := ⟨fun h hh g => by
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.subset_closure (hKCn _ (hJK g.2) _ (hKCmem hh))⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ↥G.Jg → V, ∀ x, f x = (G.lam x)⁻¹ • π x v := ⟨_, fun _ => rfl⟩
  have hlamH : ∀ h : ↥G.Jg, h ∈ (KCg k n r).subgroupOf G.Jg → G.lam h = 1 := fun h hh =>
    hlB.2.2 _ (KC_mono hr (hKCmem (Subgroup.mem_subgroupOf.1 hh)))
  have hπH : ∀ h : ↥G.Jg, h ∈ (KCg k n r).subgroupOf G.Jg → π h v = v := fun h hh =>
    hv _ (hKCmem (Subgroup.mem_subgroupOf.1 hh))
  have hf : ∀ x y : ↥G.Jg, (x : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) = y → f x = f y := by
    intro x y hxy
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ (KCg k n r).subgroupOf G.Jg, y = x * h :=
      ⟨x⁻¹ * y, QuotientGroup.eq.1 hxy, by group⟩
    rw [hfdef, hfdef, Subgroup.coe_mul, hlM _ (hJ x.2) _ (hJ h.2), hlamH h hh, mul_one, map_mul,
      Module.End.mul_apply, hπH h hh]
  have hPJ : ∀ w : V, G.PJ π r w = ∑ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
      (G.lam ((Quotient.out c : ↥G.Jg) : GL (Fin n) k))⁻¹ • π ((Quotient.out c : ↥G.Jg) : GL (Fin n) k) w :=
    fun w => finsum_eq_sum_of_fintype _
  have hPJv : G.PJ π r v = ∑ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg, f (Quotient.out c) := by
    rw [hPJ]; simp only [hfdef]
  have hA : ∀ g ∈ G.JSet, π g (G.PJ π r v) = G.lam g • G.PJ π r v := by
    intro g hg
    have hg0 := hlB.2.1 g
    have hterm : ∀ x : ↥G.Jg, π g (f x) = G.lam g • f (⟨g, Subgroup.subset_closure hg⟩ * x) := by
      intro x
      rw [hfdef, hfdef, Subgroup.coe_mul, Subgroup.coe_mk, hlM g hg _ (hJ x.2), map_smul, map_mul,
        Module.End.mul_apply, smul_smul]
      congr 1
      field_simp
    have hmv : ∀ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
        f (⟨g, Subgroup.subset_closure hg⟩ * Quotient.out c) =
          f (Quotient.out ((QuotientGroup.mk ⟨g, Subgroup.subset_closure hg⟩ : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) * c)) := by
      intro c
      apply hf
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPJv, map_sum, Finset.smul_sum]
    simp_rw [hterm, hmv]
    exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk ⟨g, Subgroup.subset_closure hg⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)) _ _ (fun c => rfl)
  refine ⟨fun g hg => hA g hg, fun j hj => ?_, fun hEv => ?_⟩
  · have hjinv := hinv j hj
    have h1' : G.lam j⁻¹ * G.lam j = 1 := by rw [← hlM _ hjinv _ hj, inv_mul_cancel, hlB.1]
    have hterm : ∀ x : ↥G.Jg, (G.lam x)⁻¹ • π x (π j v) =
        π j (f ((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩)) := by
      intro x
      have hx := hJ x.2
      have e : (((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg) :
          GL (Fin n) k) = j⁻¹ * x * j := rfl
      have hl : G.lam (((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg) :
          GL (Fin n) k) = G.lam x := by
        rw [e, hlM _ (hmul _ hjinv _ hx) _ hj, hlM _ hjinv _ hx]
        linear_combination G.lam x * h1'
      rw [hfdef, hl, map_smul, e, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 3
      group
    have hmv : ∀ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
        f ((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * Quotient.out c * ⟨j, Subgroup.subset_closure hj⟩) =
          f (Quotient.out ((QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)⁻¹ * c *
            QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩)) := by
      intro c
      apply hf
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq']
    rw [hPJ (π j v)]
    simp_rw [hterm, hmv]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← hA j hj, hPJv]
    congr 1
    exact Fintype.sum_equiv ((Equiv.mulLeft (QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)⁻¹).trans (Equiv.mulRight (QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg))) _ _ (fun c => rfl)
  · have hfv : ∀ x : ↥G.Jg, f x = v := fun x => by
      rw [hfdef, hEv _ (hJ x.2), smul_smul, inv_mul_cancel₀ (hlB.2.1 _), one_smul]
    rw [hPJv]
    simp_rw [hfv]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

end P_PJ

theorem step_PJ {n : ℕ} (G : Grp k n) : ParabolicJacquetProp G := by
  intro hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  exact P_PJ.core G hJone.1 (hJmul hcb hccB) (hJinv hcb hccB) (hlM hcb hΔU hΔM hccB) (hlB hccB) (hKC hccB)

end UpperTheory.TNZ.Grp
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacNeZero
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

variable {n : ℕ} (G : Grp k n)

theorem jac_ne_zero (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k))
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π)
    (x : V) (hx0 : x ≠ 0) (hx : x ∈ G.Eig π) :
    (Submodule.Quotient.mk x : Jacquet π (unipRad k G.e)) ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := hun
  have hJmul' := hJmul hcb hccB
  have hJinv' := hJinv hcb hccB
  have hΔU' := hΔU hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  have hiw' := hiw hcb hccB hΔU hJmul hJinv
  have hTE' := hTE hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw
  have hPJ' := hPJ hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  have hTI' := hTI hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hlU hiw hPJ hkill hni hTE hKC ϖ hϖ V π hs
  have hTp' := hTp hcb hccB hΔU hΔM hJmul hJinv hlM hlU hiw hTE ϖ hϖ V π
  have hE : ∀ y ∈ G.Eig π, G.Tz π ϖ 1 y ∈ G.Eig π := fun y hy => (hTE' ϖ hϖ 1).2 V π y hy
  have key : ∀ m : ℕ, ∀ y ∈ G.Eig π, (G.Tz π ϖ 1)^[m] y = 0 → y = 0 := by
    intro m
    induction m with
    | zero => intro y _ h; simpa using h
    | succ m ih =>
      intro y hy h
      rw [Function.iterate_succ_apply] at h
      exact hTI' y hy (ih _ (hE y hy) h)
  intro h0
  obtain ⟨m, hm⟩ := hjK hcb hccB hΔU hΔM hJmul hJinv hlM hiw hTE hlU ϖ hϖ V π hs x hx h0
  rw [hTp' x hx m] at hm
  exact hx0 (key m x hx hm)

theorem cMain (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k)) (hlL : LeviSubgroupRestriction) (hjI : G.JacquetImageProp) (hjP : G.JacquetProductProp) : G.CMainFor := by
  intro L V _ _ π hs hirr ⟨x, hx0, hx⟩
  refine hjP L V π hs hirr ⟨_, G.jac_ne_zero hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp
    hjK hTI hun π hs x hx0 hx, fun m hm => hjI hlL hJone V π x hx m hm⟩

end Grp

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetImage
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace JacquetImage

variable {n : ℕ} (G : Grp k n)

theorem leviEmb_mem_PO (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) : leviEmb k G.e m ∈ G.PO :=
  ⟨leviEmb_mem_KO (k := k) G.e hm, leviEmb_mem_parab k G.e m⟩

theorem lam_leviEmb (hL : LeviSubgroupRestriction) (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) :
    G.lam (leviEmb k G.e m) = G.eta m := by
  have h := hL k n G ⟨leviEmb k G.e m, leviEmb_mem_parab k G.e m⟩ (leviEmb_mem_PO G m hm).1
  rw [leviProj_leviEmb] at h
  exact h

end JacquetImage

theorem step_jacImage {n : ℕ} (G : Grp k n) : JacquetImageProp G := by
  intro hL hJ V _ _ π x hx m hm
  show (Submodule.Quotient.mk (π (leviEmb k G.e m) x) : Jacquet π (unipRad k G.e)) = _
  rw [hx _ (hJ.2 (JacquetImage.leviEmb_mem_PO G m hm)), JacquetImage.lam_leviEmb G hL m hm,
    Submodule.Quotient.mk_smul]

end UpperTheory.TNZ.Grp
end
end

