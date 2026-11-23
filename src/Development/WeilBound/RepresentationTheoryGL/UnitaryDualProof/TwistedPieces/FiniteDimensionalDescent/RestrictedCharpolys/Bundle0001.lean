module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PullPieces
public import GroundTheory.AutomorphicForms.WhittakerLSpace
public import GroundTheory.AutomorphicForms.WhittakerDistribution
public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0013
public import GroundTheory.LocalFields.Interface

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FbExists
section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiA

open PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure FB (k : Type) [Field k] [TopologicalSpace k] (q d : ℕ) where
  β : Fin d → k
  cF : k →+ (Fin d → k)
  recon : ∀ a, ∑ j, cF a j ^ q * β j = a
  uniq : ∀ w : Fin d → k, cF (∑ j, w j ^ q * β j) = w
  cont : Continuous cF

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem fb_smul {q d : ℕ} (B : FB k q d) (l a : k) : B.cF (l ^ q * a) = fun j => l * B.cF a j := by
  conv_lhs => rw [← B.recon a, Finset.mul_sum]
  have : ∑ j, l ^ q * (B.cF a j ^ q * B.β j) = ∑ j, (l * B.cF a j) ^ q * B.β j :=
    Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring
  rw [this, B.uniq]

theorem fb_exists (hF : FinDim k) (p c : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ d : ℕ, 0 < d ∧ Nonempty (FB k (p ^ c) d) := by
  letI := frMod (k := k) p c
  obtain ⟨hfd, hpos⟩ := hF p c
  set d := Module.finrank k (Fr k p c) with hd
  let b : Module.Basis (Fin d) k (Fr k p c) := Module.finBasis k (Fr k p c)
  let toK : Fr k p c → k := fun x => x
  let ofK : k → Fr k p c := fun x => x
  have hsm : ∀ (a : k) (x : Fr k p c), a • x = ofK (a ^ p ^ c * toK x) := by
    intro a x
    show iterateFrobenius k p c a * toK x = _
    rw [iterateFrobenius_def]
  let β : Fin d → k := fun j => toK (b j)
  let g : (Fin d → k) → k := fun w => ∑ j, w j ^ p ^ c * β j
  have gadd : ∀ v w, g (v + w) = g v + g w := by
    intro v w
    simp only [g, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]
  let f : (Fin d → k) →+ k := AddMonoidHom.mk' g gadd
  have hfb : ∀ w, f w = toK (b.equivFun.symm w) := by
    intro w
    rw [Module.Basis.equivFun_symm_apply]
    show ∑ j, w j ^ p ^ c * β j = _
    exact Finset.sum_congr rfl fun j _ => (hsm (w j) (b j)).symm
  have hinj : Function.Injective f := by
    intro v w h
    rw [hfb, hfb] at h
    exact b.equivFun.symm.injective h
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨b.equivFun (ofK a), ?_⟩
    rw [hfb, LinearEquiv.symm_apply_apply]
  have hcont : Continuous f := by
    show Continuous g
    fun_prop
  have hopen : IsOpenMap f := AddMonoidHom.isOpenMap_of_sigmaCompact f hsurj hcont
  let E : (Fin d → k) ≃+ k := AddEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨d, hpos, ⟨{ β := β, cF := E.symm.toAddMonoidHom, recon := ?_, uniq := ?_, cont := ?_ }⟩⟩
  · intro a
    exact E.apply_symm_apply a
  · intro w
    exact E.symm_apply_apply w
  · show Continuous E.symm
    rw [continuous_def]
    intro U hU
    have himg : ⇑E.symm ⁻¹' U = f '' U := by
      ext y
      constructor
      · intro hy
        exact ⟨E.symm y, hy, E.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        show E.symm (E x) ∈ U
        rw [E.symm_apply_apply]
        exact hx
    rw [himg]
    exact hopen U hU

end PositivityTheory.RgUd.TP.Desc.Restr.PphiA
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FibVanPull
section
noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker Set Topology

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2B

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n N q : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)}
  {φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k} {e : (Fin n → k) ≃+ (Fin N → k)}

def Φ (φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k) (e : (Fin n → k) ≃+ (Fin N → k)) (p : Sp k n) : Sp k N :=
  (φ p.1, e p.2)

def eH (hd : PhiData q Z Z' φ e) : (Fin n → k) ≃ₜ (Fin N → k) :=
  { toEquiv := e.toEquiv, continuous_toFun := hd.econt, continuous_invFun := hd.econt' }

theorem isClosedEmbedding_Φ (hd : PhiData q Z Z' φ e) : IsClosedEmbedding (Φ φ e) :=
  hd.emb.prodMap (eH hd).isClosedEmbedding

theorem comp_mem (hd : PhiData q Z Z' φ e) {f : Sp k N → ℂ} (hf : f ∈ locallyConstantCompactSupport (Sp k N) ℂ ℂ) :
    f ∘ Φ φ e ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ := by
  obtain ⟨h1, h2⟩ := hf
  exact ⟨h1.comp_continuous (isClosedEmbedding_Φ hd).continuous,
    h2.comp_isClosedEmbedding (isClosedEmbedding_Φ hd)⟩

theorem inv_val (hd : PhiData q Z Z' φ e) {g : GL (Fin n) k} {g' : GL (Fin N) k} (h : φ g.val = g'.val) :
    φ g⁻¹.val = g'⁻¹.val := by
  calc φ g⁻¹.val = φ g⁻¹.val * (g'.val * g'⁻¹.val) := by simp
    _ = φ (g⁻¹.val * g.val) * g'⁻¹.val := by rw [map_mul, h, mul_assoc]
    _ = g'⁻¹.val := by simp

theorem act_Φ (hd : PhiData q Z Z' φ e) {g : GL (Fin n) k} {g' : GL (Fin N) k} (h : φ g.val = g'.val) (p : Sp k n) :
    act g' (Φ φ e p) = Φ φ e (act g p) := by
  simp only [act, Φ, map_mul, hd.intertw, h, inv_val hd h]

private theorem exists_compact_clopen_between {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] {K U : Set Y} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set Y, IsClopen V ∧ IsCompact V ∧ K ⊆ V ∧ V ⊆ U := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  have hb := loc_compact_Haus_tot_disc_of_zero_dim (X := Y)
  have hx : ∀ x : K, ∃ V : Set Y, IsClopen V ∧ (x : Y) ∈ V ∧ V ⊆ interior L := fun x =>
    hb.mem_nhds_iff.1 (isOpen_interior.mem_nhds (hKL x.2))
  choose V hV using hx
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V (fun x => (hV x).1.isOpen)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hV ⟨x, hx⟩).2.1⟩)
  have hcl : IsClopen (⋃ i ∈ I, V i) := I.finite_toSet.isClopen_biUnion (fun i _ => (hV i).1)
  refine ⟨⋃ i ∈ I, V i, hcl, ?_, hI, ?_⟩
  · exact hL.of_isClosed_subset hcl.isClosed
      (iUnion₂_subset fun i _ => (hV i).2.2.trans interior_subset)
  · exact iUnion₂_subset fun i _ => (hV i).2.2.trans (interior_subset.trans hLU)

private theorem exists_compact_clopen_preimage_Phi_eq (hd : PhiData q Z Z' φ e) {A : Set (Sp k n)} (hA : IsClopen A)
    (hAc : IsCompact A) (hAO : A ⊆ {p | p.2 ≠ 0}) :
    ∃ B : Set (Sp k N), IsClopen B ∧ IsCompact B ∧ B ⊆ {p | p.2 ≠ 0} ∧ Φ φ e ⁻¹' B = A := by
  haveI := totallyDisconnectedSpace_localField (F := k)
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  have hE := isClosedEmbedding_Φ hd
  have hO : IsOpen ({p : Sp k N | p.2 ≠ 0} ∩ (Φ φ e '' Aᶜ)ᶜ) :=
    (isOpen_ne_fun continuous_snd continuous_const).inter
      (hE.isClosedMap _ hA.isOpen.isClosed_compl).isOpen_compl
  have hKO : Φ φ e '' A ⊆ {p : Sp k N | p.2 ≠ 0} ∩ (Φ φ e '' Aᶜ)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · show e x.2 ≠ 0
      intro h0
      exact hAO hx ((map_eq_zero_iff e e.injective).1 h0)
    · rintro ⟨y, hy, hyx⟩
      exact hy (hE.injective hyx ▸ hx)
  obtain ⟨V, hV, hVc, hKV, hVO⟩ :=
    exists_compact_clopen_between (Y := Sp k N) (hAc.image hE.continuous) hO hKO
  refine ⟨V, hV, hVc, fun p hp => (hVO hp).1, ?_⟩
  ext x
  constructor
  · intro hx
    by_contra hxA
    exact (hVO hx).2 ⟨x, hxA, rfl⟩
  · intro hx
    exact hKV ⟨x, hx, rfl⟩

private theorem exists_supportedIn_comp_Phi_eq (hd : PhiData q Z Z' φ e) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn {p : Sp k n | p.2 ≠ 0}) :
    ∃ h ∈ supportedIn {p : Sp k N | p.2 ≠ 0}, h ∘ Φ φ e = f := by
  obtain ⟨⟨hlc, hcs⟩, hsupp⟩ := hf
  have hK := hcs.isCompact
  have key : ∀ c : ℂ, c ≠ 0 → ∃ B : Set (Sp k N), IsClopen B ∧ IsCompact B ∧
      B ⊆ {p | p.2 ≠ 0} ∧ Φ φ e ⁻¹' B = f ⁻¹' {c} := by
    intro c hc
    have hcl : IsClopen (f ⁻¹' {c}) := hlc.isClopen_fiber c
    have hsub : f ⁻¹' {c} ⊆ Function.support f := fun x hx => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      simp [Function.mem_support, hx, hc]
    exact exists_compact_clopen_preimage_Phi_eq hd hcl
      (hK.of_isClosed_subset hcl.isClosed (hsub.trans (subset_tsupport f))) (hsub.trans hsupp)
  choose! B hB using key
  have hfin : (Set.range f).Finite := by
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
    have hc : Continuous (fun x : tsupport f => (x : Sp k n)) := continuous_subtype_val
    have h1 := (hlc.comp_continuous hc).range_finite
    refine (h1.insert 0).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : f x = 0
    · exact Or.inl hx
    · exact Or.inr ⟨⟨x, subset_tsupport f hx⟩, rfl⟩
  set S := hfin.toFinset.filter (· ≠ 0) with hS
  refine ⟨∑ c ∈ S, c • (B c).indicator (fun _ => (1 : ℂ)), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    obtain ⟨hBc, hBk, hBO, -⟩ := hB c hc0
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      have := Set.indicator_const_preimage (B c) s (1 : ℂ)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h | h | h <;> rw [h]
      exacts [isOpen_univ, hBc.isOpen, hBc.isClosed.isOpen_compl, isOpen_empty]
    · exact HasCompactSupport.intro hBk fun x hx => Set.indicator_of_notMem hx _
    · exact Set.support_indicator_subset.trans hBO
  · funext x
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ c ∈ S, c * (B c).indicator (fun _ => (1 : ℂ)) (Φ φ e x) =
        if f x = c then c else 0 := by
      intro c hc
      have hpre := (hB c (Finset.mem_filter.1 hc).2).2.2.2
      by_cases hx : f x = c
      · have hm : Φ φ e x ∈ B c := by
          show x ∈ Φ φ e ⁻¹' B c
          rw [hpre]
          exact hx
        simp [Set.indicator_of_mem hm, hx]
      · have hm : Φ φ e x ∉ B c := by
          show x ∉ Φ φ e ⁻¹' B c
          rw [hpre]
          exact hx
        simp [Set.indicator_of_notMem hm, hx]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, Ne.symm hne⟩)

theorem fibVan_pull (hd : PhiData q Z Z' φ e) (F : Set (Matrix (Fin n) (Fin n) k))
    (F' : Set (Matrix (Fin N) (Fin N) k)) (hF : ∀ x ∈ F, φ x ∈ F') (h' : FibVan Z' F') : FibVan Z F := by
  intro ξ hS hI
  let ξ' : (Sp k N → ℂ) →ₗ[ℂ] ℂ := ξ.comp (LinearMap.funLeft ℂ ℂ (Φ φ e))
  have hmem : ∀ g ∈ supportedIn (univ : Set (Sp k N)),
      g ∘ Φ φ e ∈ supportedIn (univ : Set (Sp k n)) := by
    intro g hg
    obtain ⟨hg1, -⟩ := hg
    exact ⟨comp_mem hd hg1, subset_univ _⟩
  have hS' : Supp ξ' (F' ×ˢ univ) := by
    intro g hg hz
    show ξ (g ∘ Φ φ e) = 0
    refine hS _ (hmem g hg) ?_
    rintro p ⟨hp, -⟩
    exact hz _ ⟨hF _ hp, mem_univ _⟩
  have hI' : PositivityTheory.RgUd.T.Inv Z' ξ' := by
    intro g' hg' g hg
    obtain ⟨g0, hg0, hφ⟩ := (hd.gz g').1 hg'
    show ξ ((fun p => g (act g' p)) ∘ Φ φ e) = ξ (g ∘ Φ φ e)
    have hfun : ((fun p => g (act g' p)) ∘ Φ φ e) = fun p => (g ∘ Φ φ e) (act g0 p) := by
      funext p
      simp only [Function.comp_apply, act_Φ hd hφ]
    rw [hfun]
    exact hI g0 hg0 _ (hmem g hg)
  have hK := h' ξ' hS' hI'
  intro f hf
  obtain ⟨h, hh, rfl⟩ := exists_supportedIn_comp_Phi_eq hd hf
  exact hK h hh

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2B
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FiniteCharpoly
section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2A

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n N q : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)}
  {φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k} {e : (Fin n → k) ≃+ (Fin N → k)}

theorem choose_zero (hd : PhiData q Z Z' φ e) (hN : 0 < N) :
    1 ≤ q ∧ ∀ i, 0 < i → i < q → (q.choose i : k) = 0 := by
  have hinf : Infinite k := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    classical
    haveI := Fintype.ofFinite k
    have hr : r ≠ 0 := by simpa using hr0
    have h1 := FiniteField.pow_card_sub_one_eq_one r hr
    have h2 := congrArg (ValuativeRel.valuation k) h1
    rw [map_pow, map_one] at h2
    have hc : Fintype.card k - 1 ≠ 0 := by
      have := Fintype.one_lt_card (α := k)
      omega
    exact (pow_lt_one₀ zero_le' hr1 hc).ne h2
  haveI : Nontrivial (Matrix (Fin N) (Fin N) k) := by
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    infer_instance
  let f : k →+* Matrix (Fin N) (Fin N) k := φ.comp (algebraMap k _)
  have hfinj : Function.Injective f := f.injective
  have hfq : ∀ a : k, f (a ^ q) = algebraMap k _ a := fun a => hd.scal a
  have hq : 1 ≤ q := by
    by_contra h
    have h0 : q = 0 := by omega
    have h3 := hfq 0
    rw [h0, pow_zero, map_one, map_zero] at h3
    exact one_ne_zero h3
  have hadd : ∀ a b : k, (a + b) ^ q = a ^ q + b ^ q := by
    intro a b
    apply hfinj
    rw [hfq, map_add (f := _), map_add (f := _), hfq, hfq]
  refine ⟨hq, fun i hi1 hi2 => ?_⟩
  have hP : ((X + 1 : k[X]) ^ q - X ^ q - 1) = 0 := by
    apply Polynomial.funext
    intro a
    simp [hadd a 1]
  have h4 := congrArg (fun p => p.coeff i) hP
  have hi0 : i ≠ 0 := by omega
  have hiq : i ≠ q := by omega
  simpa [coeff_X_add_one_pow, coeff_X_pow, coeff_one, hi0, hiq, Ne.symm hi0] using h4

theorem pow_sum {R : Type*} [Ring R] {q : ℕ} (hq : 1 ≤ q) (hc : ∀ i, 0 < i → i < q → (q.choose i : R) = 0)
    {ι : Type*} (s : Finset ι) (a : ι → R) (hcomm : ∀ i j, Commute (a i) (a j)) :
    (∑ i ∈ s, a i) ^ q = ∑ i ∈ s, a i ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_pow (by omega)]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    have hc' : Commute (a j) (∑ i ∈ s, a i) := Commute.sum_right _ _ _ fun i _ => hcomm j i
    rw [hc'.add_pow, Finset.sum_eq_add q 0 (by omega)]
    · simp
    · intro m hm hm'
      rw [hc m (by omega) (by have := Finset.mem_range.1 hm; omega), mul_zero]
    · intro h
      simp at h
    · intro h
      simp at h

theorem aeval_expand (hd : PhiData q Z Z' φ e) (hN : 0 < N) (χ : k[X]) (x : Matrix (Fin n) (Fin n) k)
    (hx : aeval x χ = 0) : aeval (φ x) (expand k q χ) = 0 := by
  obtain ⟨hq, hc⟩ := choose_zero hd hN
  have hcM : ∀ i, 0 < i → i < q → (q.choose i : Matrix (Fin N) (Fin N) k) = 0 := by
    intro i h1 h2
    rw [← map_natCast (algebraMap k (Matrix (Fin N) (Fin N) k)), hc i h1 h2, map_zero]
  have hsum : φ (aeval x χ) = ∑ i ∈ Finset.range (χ.natDegree + 1), φ (χ.coeff i • x ^ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [aeval_eq_sum_range, map_sum]
  rw [hx, map_zero] at hsum
  have hp := pow_sum hq hcM (Finset.range (χ.natDegree + 1)) (fun i => φ (χ.coeff i • x ^ i))
    (fun i j => (((Commute.pow_pow_self x i j).smul_left _).smul_right _).map φ)
  beta_reduce at hp
  rw [← hsum, zero_pow (by omega)] at hp
  rw [expand_aeval, aeval_eq_sum_range, hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow φ (χ.coeff i • x ^ i) q, _root_.smul_pow, ← pow_mul, ← pow_mul, Algebra.smul_def,
    Algebra.smul_def, map_mul, hd.scal, map_pow, mul_comm q i]

private theorem sub_dvd_lemma {R : Type*} [Ring R] [Algebra k R] (P : k[X]) (x y : R) (h : Commute x y) :
    ∃ Q : R, aeval x P - aeval y P = Q * (x - y) := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • ∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j), ?_⟩
  rw [aeval_eq_sum_range, aeval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_sub, smul_mul_assoc, h.geom_sum₂_mul]

theorem finite_charpoly (N : ℕ) (P : k[X]) (hP : P ≠ 0) :
    ∃ l : List k[X], l.Nodup ∧ ∀ A : Matrix (Fin N) (Fin N) k, aeval A P = 0 → A.charpoly ∈ l := by
  classical
  let F := Polynomial.fintypeSubtypeMonicDvd (P ^ N) (pow_ne_zero N hP)
  refine ⟨((@Finset.univ _ F).image Subtype.val).toList, Finset.nodup_toList _, fun A hA => ?_⟩
  rw [Finset.mem_toList, Finset.mem_image]
  refine ⟨⟨A.charpoly, A.charpoly_monic, ?_⟩, Finset.mem_univ _, rfl⟩
  let ψ := (Algebra.ofId k k[X]).mapMatrix (m := Fin N)
  let T : Matrix (Fin N) (Fin N) k[X] := algebraMap k[X] _ X
  obtain ⟨Q, hQ⟩ := sub_dvd_lemma P T (ψ A) (Algebra.commute_algebraMap_left X (ψ A))
  have h1 : aeval (ψ A) P = 0 := by rw [aeval_algHom_apply, hA, map_zero]
  have h2 : aeval T P = algebraMap k[X] _ P := by
    rw [aeval_algebraMap_apply, aeval_X_left_apply]
  have h3 : T - ψ A = charmatrix A := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply]
    · simp [T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply, hij]
  rw [h1, h2, sub_zero, h3] at hQ
  have h4 := congrArg Matrix.det hQ
  rw [det_mul, Matrix.algebraMap_eq_diagonal] at h4
  simp only [det_diagonal] at h4
  simp at h4
  exact ⟨Q.det, by rw [h4, mul_comm]; rfl⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2A
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PfinDim
section
noncomputable section

open ValuativeRel

namespace PositivityTheory.RgUd.TP.Desc.Restr.PfinDim

open PositivityTheory.RgUd.TP.Desc.Restr

theorem finDim (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    FinDim k := by
  intro p c _ _
  letI := frMod (k := k) p c
  letI := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  have hc : CompleteSpace k := inferInstance
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  have : CompleteSpace k := hc
  have : IsTopologicalAddGroup (Fr k p c) := inferInstanceAs (IsTopologicalAddGroup k)
  have : T2Space (Fr k p c) := inferInstanceAs (T2Space k)
  have : LocallyCompactSpace (Fr k p c) := inferInstanceAs (LocallyCompactSpace k)
  have : Nontrivial (Fr k p c) := inferInstanceAs (Nontrivial k)
  have : ContinuousSMul k (Fr k p c) := ⟨by
    show Continuous fun q : k × k => (iterateFrobenius k p c q.1) * q.2
    simp only [iterateFrobenius_def]
    exact (continuous_fst.pow _).mul continuous_snd⟩
  have hfd : FiniteDimensional k (Fr k p c) := FiniteDimensional.of_locallyCompactSpace k
  exact ⟨hfd, Module.finrank_pos⟩

end PositivityTheory.RgUd.TP.Desc.Restr.PfinDim

end
end

