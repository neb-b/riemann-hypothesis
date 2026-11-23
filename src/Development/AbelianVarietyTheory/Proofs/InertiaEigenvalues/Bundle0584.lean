module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0579
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusOnStratifiedValue
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.FrobValue

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem hf_comp {Q Q' : Obj l ↥(OL K)} (c : Hom Q Q') (g : Hom bk.prism Q) :
    BK.hf (c.comp g) = c.f.comp (BK.hf g) := rfl

theorem frob_change (S : Strat bk d) {Q : Obj l ↥(OL K)} (g g' : Hom bk.prism Q) (y y' : Fin d → Q.A)
    (hy : y = (S.ε g g').mulVec y') :
    BK.hf g' bk.E ^ S.a • (S.A.map (BK.hf g)).mulVec (fun i => Q.D.φ (y i)) =
      BK.hf g bk.E ^ S.a • (S.ε g g').mulVec ((S.A.map (BK.hf g')).mulVec (fun i => Q.D.φ (y' i))) := by
  have e : (fun i => Q.D.φ (y i)) = ((S.ε g g').map Q.D.φ).mulVec (fun i => Q.D.φ (y' i)) := by
    funext i; rw [hy, RingHom.map_mulVec]; rfl
  rw [e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
    S.ε_φ]

theorem push (S : Strat bk d) {C Q : Obj l ↥(OL K)} (p : Hom C Q) (f : Hom bk.prism C) (c : C.A)
    (y : Fin d → C.A) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i)) =
      p.f c ^ S.a • (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) := by
  funext i
  have h1 : p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i) =
      p.f c ^ S.a * p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) := by
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
  have h2 : p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) =
      (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) i := by
    rw [RingHom.map_mulVec, Matrix.map_map, hf_comp]
    congr 1
    funext j
    exact p.f_φ (y j)
  refine h1.trans ?_
  simp only [h2, Pi.smul_apply, smul_eq_mul]

theorem vec_cancel {A : Type} [CommRing A] {r : A} (hr : r ∈ nonZeroDivisors A) {u w : Fin d → A}
    (e : r • u = r • w) : u = w :=
  funext fun i => (mul_cancel_left_mem_nonZeroDivisors hr).1 (congrFun e i)

theorem pow_smul_transfer_of_regular {A : Type} [CommRing A] {a : ℕ} {e e' u u' : A} {L R : Fin d → A}
    (hr : e ^ a * e' ^ a ∈ nonZeroDivisors A) (hF : e' ^ a • L = e ^ a • R) (hT : u * e = u' * e') :
    u ^ a • L = u' ^ a • R := by
  refine vec_cancel hr ?_
  calc (e ^ a * e' ^ a) • (u ^ a • L) = (u * e) ^ a • (e' ^ a • L) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring
    _ = (u' * e') ^ a • (e ^ a • R) := by rw [hF, hT]
    _ = (e ^ a * e' ^ a) • (u' ^ a • R) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring

theorem compat (S : Strat bk d) {B C Q : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (hn : ∀ g : Hom bk.prism Q, BK.hf g bk.E ∈ nonZeroDivisors Q.A)
    (x : N) (p q : Hom C Q) (hpq : p.comp h = q.comp h) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) =
      (S.ε (p.comp f) (q.comp f)).mulVec
        (fun i => q.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) := by
  have hY : ∀ j, p.f (V.v h f x j) = V.v (p.comp h) (p.comp f) x j :=
    fun j => (V.v_nat p h f x j).symm
  have hY' : ∀ j, q.f (V.v h f x j) = V.v (p.comp h) (q.comp f) x j := by
    rw [hpq]; exact fun j => (V.v_nat q h f x j).symm
  have hF := frob_change S (p.comp f) (q.comp f) _ _ (V.v_ε (p.comp h) (p.comp f) (q.comp f) x)
  have hT : p.f c * BK.hf (p.comp f) bk.E = q.f c * BK.hf (q.comp f) bk.E := by
    have e1 : p.f (c * BK.hf f bk.E) = q.f (c * BK.hf f bk.E) := by
      rw [hc]; exact congrArg (fun k : Hom B Q => k.f t) hpq
    simpa only [map_mul, hf_comp, RingHom.comp_apply] using e1
  rw [push S p f c, push S q f c, Matrix.mulVec_smul]
  simp only [hY, hY']
  exact pow_smul_transfer_of_regular (mul_mem (pow_mem (hn (p.comp f)) S.a) (pow_mem (hn (q.comp f)) S.a)) hF hT

theorem pow_smul_matrix_swap_of_relation {A : Type} [CommRing A] {a : ℕ} {e e' u : A} {L M : Fin d → A} {P : Matrix (Fin d) (Fin d) A}
    (hF : e' ^ a • L = e ^ a • P.mulVec M) : e ^ a • P.mulVec (u ^ a • M) = (u * e') ^ a • L := by
  rw [Matrix.mulVec_smul, mul_pow, mul_smul, hF, smul_comm]

theorem coord (S : Strat bk d) {B C Q Q' : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (a : Hom B Q) (g : Hom bk.prism Q) (h' : Hom Q Q') (a' : Hom C Q') (hcomm : a'.comp h = h'.comp a)
    (hinj' : Function.Injective h'.f) (x w : N)
    (hw : V.v h f w = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i))) :
    BK.hf g bk.E ^ S.a • V.v a g w = a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i) := by
  have nat' : ∀ (y : N) j, h'.f (V.v a g y j) = V.v (a'.comp h) (h'.comp g) y j := by
    intro y j; rw [hcomm]; exact (V.v_nat h' a g y j).symm
  have natC : ∀ (y : N) j, a'.f (V.v h f y j) = V.v (a'.comp h) (a'.comp f) y j :=
    fun y j => (V.v_nat a' h f y j).symm
  have ht : h'.f (a.f t) = a'.f c * BK.hf (a'.comp f) bk.E := by
    have e : h'.f (a.f t) = a'.f (h.f t) := congrArg (fun k : Hom B Q' => k.f t) hcomm.symm
    rw [e, ← hc, map_mul]; rfl
  have e1 : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      BK.hf (h'.comp g) bk.E ^ S.a • V.v (a'.comp h) (h'.comp g) w := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, nat']
    rfl
  have e2 : V.v (a'.comp h) (a'.comp f) w =
      a'.f c ^ S.a • (S.A.map (BK.hf (a'.comp f))).mulVec fun j => Q'.D.φ (V.v (a'.comp h) (a'.comp f) x j) := by
    have e := push S a' f c (V.v h f x)
    rw [← hw] at e
    simp only [natC] at e
    exact e
  have e3 := push S h' g (a.f t) (V.v a g x)
  simp only [nat', ht] at e3
  have hF := frob_change S (h'.comp g) (a'.comp f) _ _ (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) x)
  have key : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      fun i => h'.f ((a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun j => Q.D.φ (V.v a g x j)) i) := by
    have v1 := (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) w).trans (congrArg _ e2)
    exact e1.trans ((congrArg (fun v => BK.hf (h'.comp g) bk.E ^ S.a • v) v1).trans ((pow_smul_matrix_swap_of_relation hF).trans e3.symm))
  funext i
  exact hinj' (congrFun key i)

theorem psi_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I →
    ∃ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ := by
  intro l _ K bk d S B N _ _ V t ht
  obtain ⟨C, h, ⟨f⟩, hC⟩ := _root_.GlobalTheory.BSP.exists_cover_receiving_bk l K bk B
  have hIC := (_root_.GlobalTheory.BSP.hf_E_span_and_regular l K bk C f).1
  have htC : h.f t ∈ Ideal.span {BK.hf f bk.E} := hIC ▸ h.f_I t ht
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 htC
  obtain ⟨hinj, hsurj⟩ := _root_.GlobalTheory.BSP.Eval.effective_of_cover l K bk d S B C N V h f hC
  have hzc : ∀ x : N, ∃ y, V.v h f y = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i)) :=
    fun x => hsurj _ fun Q p q hpq =>
      compat S V h f c t hc (fun g => (_root_.GlobalTheory.BSP.hf_E_span_and_regular l K bk Q g).2) x p q hpq
  choose Ψf hΨf using hzc
  have zadd : ∀ x y : N, Ψf (x + y) = Ψf x + Ψf y := by
    intro x y
    apply hinj
    have e1 : V.v h f (x + y) = V.v h f x + V.v h f y := map_add (V.v h f) x y
    have e2 : V.v h f (Ψf x + Ψf y) = V.v h f (Ψf x) + V.v h f (Ψf y) := map_add (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (x + y) i)) =
        (fun i => C.D.φ (V.v h f x i)) + (fun i => C.D.φ (V.v h f y i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans (C.D.φ.map_add _ _)
    refine (hΨf (x + y)).trans (Eq.trans ?_ ((congrArg₂ (· + ·) (hΨf x) (hΨf y)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_add _ _ _)).trans (smul_add _ _ _)
  have zsmul : ∀ (b : B.A) (x : N), Ψf (b • x) = B.D.φ b • Ψf x := by
    intro b x
    apply hinj
    have e1 : V.v h f (b • x) = h.f b • V.v h f x := LinearMap.map_smulₛₗ (V.v h f) b x
    have e2 : V.v h f (B.D.φ b • Ψf x) = h.f (B.D.φ b) • V.v h f (Ψf x) := LinearMap.map_smulₛₗ (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (b • x) i)) = h.f (B.D.φ b) • (fun i => C.D.φ (V.v h f x i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans
        ((C.D.φ.map_mul _ _).trans (congrArg (· * C.D.φ (V.v h f x i)) (h.f_φ b).symm))
    refine (hΨf (b • x)).trans (Eq.trans ?_ ((congrArg (h.f (B.D.φ b) • ·) (hΨf x)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_smul _ _ _)).trans (smul_comm _ _ _)
  refine ⟨{ toFun := Ψf, map_add' := zadd, map_smul' := zsmul }, ?_⟩
  intro Q a g x
  obtain ⟨Q', h', a', hcomm, hinj'⟩ := _root_.GlobalTheory.BSP.cover_po_injective l K bk d S B C h hC Q a
  exact coord S V h f c t hc a g h' a' hcomm hinj' x (Ψf x) (hΨf x)

end GlobalTheory.BSP.FrobValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem exists_fundamentalDomain_mass_one : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G], ∃ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro G _ _ _ _ _ _ Γ hΓ _ _
  obtain ⟨hdisc, K, hK, hKc⟩ := hΓ
  have : DiscreteTopology Γ := hdisc
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance

  obtain ⟨U, hUo, hU⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set Γ))
  have hU0 : ∀ γ ∈ Γ, γ ∈ U → γ = 0 := by
    intro γ hγ hγU
    have h : (⟨γ, hγ⟩ : Γ) ∈ (Subtype.val ⁻¹' U : Set Γ) := hγU
    rw [hU] at h
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 h)
  have hUn : U ∈ nhds (0 : G) := by
    have h : (0 : Γ) ∈ (Subtype.val ⁻¹' U : Set Γ) := by rw [hU]; rfl
    exact hUo.mem_nhds h

  obtain ⟨V, hV, hVU⟩ := exists_nhds_zero_half hUn
  set V₀ := interior (V ∩ (fun x => -x) ⁻¹' V) with hV₀
  have hV₀o : IsOpen V₀ := isOpen_interior
  have hV₀0 : (0 : G) ∈ V₀ := by
    rw [hV₀, mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hV ?_
    exact continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV)
  have hsub : ∀ a ∈ V₀, ∀ b ∈ V₀, a - b ∈ U := by
    intro a ha b hb
    have ha' := (interior_subset ha).1
    have hb' : -b ∈ V := (interior_subset hb).2
    rw [sub_eq_add_neg]
    exact hVU a ha' (-b) hb'

  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : G => (fun x => x - k) ⁻¹' V₀)
    (fun k => hV₀o.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simpa using hV₀0⟩)
  set l := t.toList with hl
  let c : ℕ → G := fun n => l.getD n 0
  let W : ℕ → Set G := fun n => (fun x => x - c n) ⁻¹' V₀ ∩ K ∩ {_x | n < l.length}
  let S : ℕ → Set G := fun n => ⋃ γ : Γ, (fun x => (γ : G) + x) ⁻¹' W n
  let F : Set G := ⋃ n, (W n ∩ ⋂ m, ⋂ (_ : m < n), (S m)ᶜ)
  have hWm : ∀ n, MeasurableSet (W n) := fun n =>
    ((hV₀o.preimage (continuous_id.sub continuous_const)).measurableSet.inter
      hK.isClosed.measurableSet).inter (MeasurableSet.const _)
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    MeasurableSet.iUnion fun γ => (hWm n).preimage (measurable_const_add _)
  have hFm : MeasurableSet F :=
    MeasurableSet.iUnion fun n => (hWm n).inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hSm m).compl)
  have hFK : F ⊆ K := by
    intro x hx
    obtain ⟨n, hn, -⟩ := Set.mem_iUnion.1 hx
    exact hn.1.2

  have hSinv : ∀ n, ∀ γ ∈ Γ, ∀ x, γ + x ∈ S n ↔ x ∈ S n := by
    intro n γ hγ x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨δ, hδ⟩
      exact ⟨⟨(δ : G) + γ, Γ.add_mem δ.2 hγ⟩, by simpa [add_assoc] using hδ⟩
    · rintro ⟨δ, hδ⟩
      refine ⟨⟨(δ : G) - γ, Γ.sub_mem δ.2 hγ⟩, ?_⟩
      rw [show (δ : G) - γ + (γ + x) = δ + x by abel]
      exact hδ

  have hcov : ∀ y ∈ K, ∃ n, y ∈ W n := by
    intro y hy
    obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hkl : k ∈ l := by rw [hl]; exact Finset.mem_toList.2 hk
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hkl
    refine ⟨n, ⟨?_, hy⟩, hn⟩
    have hc : c n = l[n] := List.getD_eq_getElem _ _ hn
    simpa [hc] using hyk
  have hex : ∀ x : G, ∃! γ : Γ, γ +ᵥ x ∈ F := by
    intro x
    have hne : ∃ n, x ∈ S n := by
      obtain ⟨γ, hγ, hγK⟩ := hKc x
      obtain ⟨n, hn⟩ := hcov _ hγK
      exact ⟨n, Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hn⟩⟩
    classical
    obtain ⟨δ, hδ⟩ := Set.mem_iUnion.1 (Nat.find_spec hne)
    have hδF : δ +ᵥ x ∈ F := by
      refine Set.mem_iUnion.2 ⟨Nat.find hne, hδ, ?_⟩
      simp only [Set.mem_iInter, Set.mem_compl_iff]
      intro m hm
      change ¬ ((δ : G) + x ∈ S m)
      rw [hSinv m δ δ.2 x]
      exact Nat.find_min hne hm
    refine ⟨δ, hδF, ?_⟩
    intro γ hγ
    change (γ : G) + x ∈ F at hγ
    have hγ' : (δ : G) + x ∈ F := hδF
    obtain ⟨n, hn, hnS⟩ := Set.mem_iUnion.1 hγ
    obtain ⟨n', hn', hnS'⟩ := Set.mem_iUnion.1 hγ'
    simp only [Set.mem_iInter, Set.mem_compl_iff] at hnS hnS'
    have hxn : x ∈ S n := Set.mem_iUnion.2 ⟨γ, hn⟩
    have hxn' : x ∈ S n' := Set.mem_iUnion.2 ⟨δ, hn'⟩
    rcases lt_trichotomy n n' with h | rfl | h
    · exact absurd ((hSinv n δ δ.2 x).2 hxn) (hnS' n h)
    · have hd := hsub _ hn.1.1 _ hn'.1.1
      have hmem : (γ : G) - δ ∈ Γ := Γ.sub_mem γ.2 δ.2
      have h0 := hU0 _ hmem (by simpa [sub_sub_sub_cancel_right, add_sub_add_right_eq_sub] using hd)
      exact Subtype.ext (sub_eq_zero.1 h0)
    · exact absurd ((hSinv n' γ γ.2 x).2 hxn') (hnS n' h)

  let μ₀ : Measure G := Measure.addHaar
  have hF₀ : IsAddFundamentalDomain Γ F μ₀ := IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hex
  have h0 : μ₀ F ≠ 0 := hF₀.measure_ne_zero (NeZero.ne μ₀)
  have htop : μ₀ F ≠ ⊤ := ((measure_mono hFK).trans_lt hK.measure_lt_top).ne
  refine ⟨(μ₀ F)⁻¹ • μ₀, F, Measure.IsAddHaarMeasure.smul μ₀ (ENNReal.inv_ne_zero.2 htop) (ENNReal.inv_ne_top.2 h0),
    IsAddFundamentalDomain.mk' hFm.nullMeasurableSet hex, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalMirabolicMovingRowToLast
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem mir_exists_row : ∀ (E : Type) [Field E] [NumberField E] (a m : ℕ), m + 1 < a →
    ∀ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, ξ ≠ 0 → ∃ γ : GL (Fin a) E, IsMir (m + 1) γ ∧
      ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1 = ξ t := by
  intro E _ _ a m hma ξ hξ
  classical
  set mm : Fin a := ⟨m, by omega⟩ with hmm
  set c : Fin a := ⟨m + 1, hma⟩ with hc
  let v : Fin a → E := fun k => if h : (k : ℕ) ≤ m then ξ ⟨(k, c), by simp [hc]; omega⟩ else 0
  have hv : ∀ t : UnipotentBlockColumnIndex a (m + 1) (m + 1), v t.1.1 = ξ t := by
    intro t
    have h1 := t.2
    have hle : (t.1.1 : ℕ) ≤ m := by omega
    simp only [v, dif_pos hle]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext; simp [hc]; omega
  obtain ⟨t₀, ht₀⟩ := Function.ne_iff.1 hξ
  set i₀ : Fin a := t₀.1.1 with hi₀
  have hi₀m : (i₀ : ℕ) ≤ m := by have := t₀.2; omega
  have hvi₀ : v i₀ ≠ 0 := by rw [hi₀, hv]; exact ht₀
  let M : Matrix (Fin a) (Fin a) E := Matrix.of fun i k =>
    if i = mm then v k else if i = i₀ then (if k = mm then 1 else 0) else (1 : Matrix (Fin a) (Fin a) E) i k
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hrow : ∀ j, (M *ᵥ x) j = 0 := fun j => by rw [hx]; rfl
    have hoff : ∀ j, j ≠ i₀ → x j = 0 := by
      intro j hj
      by_cases hjm : j = mm
      · have hi₀ne : i₀ ≠ mm := hjm ▸ Ne.symm hj
        have := hrow i₀
        simpa [M, Matrix.mulVec, dotProduct, hi₀ne, hjm] using this
      · have := hrow j
        simpa [M, Matrix.mulVec, dotProduct, hjm, hj, Matrix.one_apply] using this
    apply hx0
    funext j
    by_cases hj : j = i₀
    · subst hj
      have := hrow mm
      simp only [M, Matrix.mulVec, dotProduct, Matrix.of_apply, if_true] at this
      rw [Finset.sum_eq_single i₀ (fun k _ hk => by rw [hoff k hk, mul_zero]) (by simp)] at this
      exact (mul_eq_zero.1 this).resolve_left hvi₀
    · exact hoff j hj
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  refine ⟨hu.unit, ?_, ?_⟩
  · intro i k hik
    rw [IsUnit.unit_spec]
    simp only [M, Matrix.of_apply]
    rcases hik with hi | hk
    · have h1 : i ≠ mm := fun e => by rw [e] at hi; simp [hmm] at hi
      have h2 : i ≠ i₀ := fun e => by rw [e] at hi; omega
      simp [h1, h2]
    · have h1 : k ≠ mm := fun e => by rw [e] at hk; simp [hmm] at hk
      have h2 : k ≠ i₀ := fun e => by rw [e] at hk; omega
      split_ifs with e1 e2
      · subst e1
        simp only [v, Matrix.one_apply, h1.symm, if_false]
        rw [dite_eq_right (by omega)]
      · simp [e2, Matrix.one_apply, Ne.symm h2]
      · rfl
  · intro t
    rw [IsUnit.unit_spec]
    have hs : ∃ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), s.1.1 = mm := ⟨⟨(mm, c), by simp [hmm, hc]⟩, rfl⟩
    obtain ⟨s₀, hs₀⟩ := hs
    rw [Finset.sum_eq_single s₀]
    · simp only [eLast, hs₀, hmm, M, Matrix.of_apply, if_true, one_mul]
      exact hv t
    · intro s _ hs
      have : ¬ ((s.1.1 : ℕ) + 1 = m + 1) := by
        intro e
        apply hs
        apply Subtype.ext
        have h1 := s.2; have h2 := s₀.2
        apply Prod.ext
        · apply Fin.ext; rw [hs₀]; simp [hmm]; omega
        · apply Fin.ext; omega
      simp only [eLast, if_neg this, zero_mul]
    · simp

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleHomValueMap
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem stratHom_map_mulVec {m n : Type} [Fintype n] {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : Matrix m n A) (v : n → A) : (fun i => φ ((M.mulVec v) i)) = (M.map φ).mulVec (fun i => φ (v i)) := by
  funext i
  exact RingHom.map_mulVec φ M v i

theorem stratHom_coord_nat {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    (Y : Matrix (Fin d') (Fin d) bk.S) {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) {Q Q' : Obj l ↥(OL K)} (r : Hom Q Q') (a : Hom B Q) (g : Hom bk.prism Q) (x : N) :
    (fun i => r.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) i)) =
      (Y.map (BK.hf (r.comp g))).mulVec (V.v (r.comp a) (r.comp g) x) := by
  rw [stratHom_map_mulVec]
  have e1 : (Y.map (BK.hf g)).map r.f = Y.map (BK.hf (r.comp g)) := by
    rw [Matrix.map_map]; rfl
  have e2 : (fun i => r.f (V.v a g x i)) = V.v (r.comp a) (r.comp g) x := by
    funext i; exact (V.v_nat r a g x i).symm
  rw [e1, e2]

theorem stratHom_coord_ε {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    {S' : Strat bk d'} {Y : Matrix (Fin d') (Fin d) bk.S} (hY : IsStratHom S S' Y) {B : Obj l ↥(OL K)} {N : Type}
    [AddCommGroup N] [Module B.A N] (V : Eval S B N) {Q : Obj l ↥(OL K)} (a : Hom B Q) (g g' : Hom bk.prism Q)
    (x : N) :
    (Y.map (BK.hf g)).mulVec (V.v a g x) = (S'.ε g g').mulVec ((Y.map (BK.hf g')).mulVec (V.v a g' x)) := by
  rw [V.v_ε a g g' x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hY.ε]

theorem evalHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S), IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N]
    [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] (V : Eval S B N) (V' : Eval S' B N'),
    ∃ w : N →ₗ[B.A] N', ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x) := by
  intro l _ K bk d d' S S' Y hY B N _ _ N' _ _ V V'
  obtain ⟨C, h, ⟨f⟩, hc⟩ := _root_.GlobalTheory.BSP.exists_cover_receiving_bk l K bk B
  obtain ⟨inj, ev⟩ := _root_.GlobalTheory.BSP.Eval.effective_of_cover l K bk d' S' B C N' V' h f hc
  have hz : ∀ x, ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h →
      (fun i => p.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i)) = (S'.ε (p.comp f) (q.comp f)).mulVec
        fun i => q.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i) := by
    intro x Q p q hpq
    have e : V.v (p.comp h) (p.comp f) x = V.v (q.comp h) (p.comp f) x := by rw [hpq]
    refine (stratHom_coord_nat Y V p h f x).trans ?_
    refine Eq.trans ?_ (congrArg (S'.ε (p.comp f) (q.comp f)).mulVec (stratHom_coord_nat Y V q h f x)).symm
    rw [e]
    exact stratHom_coord_ε hY V (q.comp h) (p.comp f) (q.comp f) x
  choose w0 hw0 using fun x => ev _ (hz x)
  let w : N →ₗ[B.A] N' :=
    { toFun := w0
      map_add' := fun x y => by
        apply inj
        show V'.v h f (w0 (x + y)) = V'.v h f (w0 x + w0 y)
        refine (hw0 (x + y)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_add (w0 x) (w0 y)).symm
        refine Eq.trans ?_ (congrArg₂ (· + ·) (hw0 x) (hw0 y)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_add x y)).trans (Matrix.mulVec_add _ _ _)
      map_smul' := fun c x => by
        apply inj
        show V'.v h f (w0 (c • x)) = V'.v h f (c • w0 x)
        refine (hw0 (c • x)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_smulₛₗ c (w0 x)).symm
        refine Eq.trans ?_ (congrArg (h.f c • ·) (hw0 x)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_smulₛₗ c x)).trans (Matrix.mulVec_smul _ _ _) }
  refine ⟨w, fun Q a g x => ?_⟩
  obtain ⟨Q', h', a', hcomm, hinj⟩ := _root_.GlobalTheory.BSP.cover_po_injective l K bk d S B C h hc Q a
  have hw : w x = w0 x := rfl
  funext i
  apply hinj
  have lhs : (fun j => h'.f (V'.v a g (w0 x) j)) = V'.v (a'.comp h) (h'.comp g) (w0 x) := by
    exact (funext fun j => (V'.v_nat h' a g (w0 x) j).symm).trans
      (congrArg (fun t => V'.v t (h'.comp g) (w0 x)) hcomm.symm)
  have rhs : (fun j => h'.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) j)) =
      (Y.map (BK.hf (h'.comp g))).mulVec (V.v (a'.comp h) (h'.comp g) x) := by
    exact (stratHom_coord_nat Y V h' a g x).trans
      (congrArg (fun t => (Y.map (BK.hf (h'.comp g))).mulVec (V.v t (h'.comp g) x)) hcomm.symm)
  have mid : V'.v (a'.comp h) (a'.comp f) (w0 x) = (Y.map (BK.hf (a'.comp f))).mulVec (V.v (a'.comp h) (a'.comp f) x) := by
    exact (funext fun j => V'.v_nat a' h f (w0 x) j).trans
      ((congrArg (fun v : Fin d' → C.A => fun j => a'.f (v j)) (hw0 x)).trans (stratHom_coord_nat Y V a' h f x))
  have := congrFun (lhs.trans ((V'.v_ε (a'.comp h) (h'.comp g) (a'.comp f) (w0 x)).trans
    ((congrArg (S'.ε (h'.comp g) (a'.comp f)).mulVec mid).trans
      ((stratHom_coord_ε hY V (a'.comp h) (h'.comp g) (a'.comp f) x).symm.trans rhs.symm)))) i
  rw [hw]
  exact this

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrixStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_galois_comparison_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) = bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (ht.Y.map bk.iA * ε) := by
  first | exact @GlobalTheory.BSP.Height.rel_gal | exact GlobalTheory.BSP.Height.rel_gal | (intros; apply GlobalTheory.BSP.Height.rel_gal <;> assumption)
end

