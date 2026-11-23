module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
public import Batteries.Tactic.OpenPrivate

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Ord

private theorem ord_parts {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A]
    (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ) {P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.Part ι lam ξ → Prop}
    (hP : AutY H ι P) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d) (hs : H.IsSpec θ ι x.toRingHom lam ξ c0 sp) (hlam : lam ∈ H.admitted) (K : H.Lev) :
    H.OrdAt θ ι x.toRingHom lam ξ K c0 =
      ⨆ Y : {Y : H.Part ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K c0 := by
  let matchingEigenvectors {M : Type} [AddCommGroup M] [Module ℂ M] {G : Type} [Group G] (ρ : Representation ℂ G M) (K : Subgroup G) (F : M) : Submodule ℂ M := {
    carrier := {y | ∀ k ∈ K, ∀ a : ℂ, ρ k F = a • F → ρ k y = a • y}
    add_mem' ha hb k hk a h := by rw [map_add (f := _), ha k hk a h, hb k hk a h, smul_add]
    zero_mem' k _ a _ := by simp
    smul_mem' c v hv k hk a h := by rw [map_smul, hv k hk a h, smul_comm] }

  have matchingEigenvectors_stable {M : Type} [AddCommGroup M] [Module ℂ M] {G : Type} [Group G] (ρ : Representation ℂ G M) (K : Subgroup G) (F : M) (φ : M →ₗ[ℂ] M)
      (hφ : ∀ k y, ρ k (φ y) = φ (ρ k y)) {y : M} (hy : y ∈ matchingEigenvectors ρ K F) : φ y ∈ matchingEigenvectors ρ K F := fun k hk a h => by
    rw [hφ, hy k hk a h, map_smul]

  have averagingProjection {M : Type} [AddCommGroup M] [Module ℂ M] {S : Type} [Group S] (ρ : Representation ℂ S M) (U : Subgroup S) [U.FiniteIndex] :
      ∃ P : M →ₗ[ℂ] M, (∀ y ∈ fixd ρ U, ∀ s, ρ s (P y) = P y) ∧ (∀ y, (∀ s, ρ s y = y) → P y = y) ∧
        ∀ Y : Submodule ℂ M, (∀ s, ∀ y ∈ Y, ρ s y ∈ Y) → ∀ y ∈ Y, P y ∈ Y := by
    classical
    have : Fintype (S ⧸ U) := Fintype.ofFinite _
    have hc : (Fintype.card (S ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    refine ⟨(Fintype.card (S ⧸ U) : ℂ)⁻¹ • ∑ q : S ⧸ U, ρ q.out, fun y hy s => ?_, fun y hy => ?_, fun Y hY y hy => ?_⟩
    · simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
      congr 1
      refine Fintype.sum_equiv (MulAction.toPerm s) _ _ fun q => ?_
      have h1 : (((s • q : S ⧸ U).out : S) : S ⧸ U) = ((s * q.out : S) : S ⧸ U) := by
        rw [QuotientGroup.out_eq']
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have h2 := hy _ (QuotientGroup.eq.1 h1)
      change ρ s (ρ q.out y) = ρ (s • q : S ⧸ U).out y
      conv_rhs => rw [← h2]
      rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, mul_inv_cancel_left]
    · simp only [LinearMap.smul_apply, LinearMap.sum_apply, hy, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    · simp only [LinearMap.smul_apply, LinearMap.sum_apply]
      exact Y.smul_mem _ (Y.sum_mem fun q _ => hY _ y hy)

  have averageIntoEigenspaces {M : Type} [AddCommGroup M] [Module ℂ M] {G : Type} [Group G] (ρ : Representation ℂ G M) (K : Subgroup G) {κ : Type 1} (Y : κ → Submodule ℂ M)
      (hst : ∀ i, ∀ k ∈ K, ∀ y ∈ Y i, ρ k y ∈ Y i)
      (hfin : ∀ i, ∀ y ∈ Y i, ∃ U : Subgroup G, U.relIndex K ≠ 0 ∧ y ∈ fixd ρ U) {F : M} (hF : F ∈ ⨆ i, Y i) :
      F ∈ ⨆ i, Y i ⊓ matchingEigenvectors ρ K F := by
    classical
    by_cases h0 : F = 0
    · rw [h0]; exact zero_mem _
    have hinj : ∀ a b : ℂ, a • F = b • F → a = b := fun a b h => smul_left_injective ℂ h0 h
    have hne : ∀ (g : G) (a : ℂ), ρ g F = a • F → a ≠ 0 := fun g a h ha => h0 (by
      have : ρ g⁻¹ (ρ g F) = F := by rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl
      rw [← this, h, ha, zero_smul, map_zero])
    let S : Subgroup G :=
      { carrier := {k | k ∈ K ∧ ∃ a : ℂ, ρ k F = a • F}
        one_mem' := ⟨K.one_mem, 1, by simp⟩
        mul_mem' := by
          rintro g h ⟨hg, a, ha⟩ ⟨hh, b, hb⟩
          exact ⟨K.mul_mem hg hh, b * a, by rw [map_mul, mul_apply_eq_comp, hb, map_smul, ha, smul_smul]⟩
        inv_mem' := by
          rintro g ⟨hg, a, ha⟩
          refine ⟨K.inv_mem hg, a⁻¹, ?_⟩
          have : ρ g⁻¹ (ρ g F) = F := by rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl
          rw [ha, map_smul] at this
          conv_rhs => rw [← this, smul_smul, inv_mul_cancel₀ (hne g a ha), one_smul] }
    have hS : ∀ s : S, ∃ a : ℂ, ρ s F = a • F := fun s => s.2.2
    choose χ hχ using hS
    let ρ' : Representation ℂ S M :=
      { toFun := fun s => (χ s)⁻¹ • ρ s
        map_one' := by
          have : χ 1 = 1 := hinj _ _ (by rw [← hχ]; simp)
          simp [this]
        map_mul' := fun s t => by
          have : χ (s * t) = χ t * χ s := hinj _ _ (by
            rw [← hχ, Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hχ, map_smul, hχ, smul_smul])
          simp [this, smul_smul, mul_comm] }
    have hρ' : ∀ s y, ρ' s y = (χ s)⁻¹ • ρ s y := fun _ _ => rfl
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp Y F).1 hF
    choose U hU hfix using fun i => hfin i (f i) (hf i)
    have hrel : (⨅ i : f.support, U i).relIndex K ≠ 0 := Subgroup.relIndex_iInf_ne_zero fun i => hU i
    have hrel' : (⨅ i : f.support, U i).relIndex S ≠ 0 :=
      fun h => hrel (Subgroup.relIndex_eq_zero_of_le_right (show S ≤ K from fun s hs => hs.1) h)
    have : ((⨅ i : f.support, U i).subgroupOf S).FiniteIndex := ⟨hrel'⟩
    obtain ⟨P, hP1, hP2, hP3⟩ := averagingProjection ρ' ((⨅ i : f.support, U i).subgroupOf S)
    have hfi : ∀ s ∈ (⨅ i : f.support, U i).subgroupOf S, ∀ i ∈ f.support, ρ s (f i) = f i := fun s hs i hi =>
      hfix i _ (Subgroup.mem_iInf.1 (Subgroup.mem_subgroupOf.1 hs) ⟨i, hi⟩)
    have hχ1 : ∀ s ∈ (⨅ i : f.support, U i).subgroupOf S, χ s = 1 := fun s hs => hinj _ _ (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hχ, one_smul, ← hsum, Finsupp.sum, map_sum]
      exact Finset.sum_congr rfl (hfi s hs))
    have hPF : P F = F := hP2 F fun s => by
      rw [hρ', hχ, smul_smul, inv_mul_cancel₀ (hne _ _ (hχ s)), one_smul]
    have : F = ∑ i ∈ f.support, P (f i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← hPF, ← hsum]; rfl
    have key : ∀ i ∈ f.support, P (f i) ∈ ⨆ i, Y i ⊓ matchingEigenvectors ρ K F := fun i hi => by
      refine Submodule.mem_iSup_of_mem i ⟨hP3 _ (fun s y hy => ?_) _ (hf i), fun k hk a ha => ?_⟩
      · exact (Y i).smul_mem _ (hst i s s.2.1 y hy)
      · have h1 := hP1 (f i) (fun s hs => by rw [hρ', hχ1 s hs, hfi s hs i hi]; simp) ⟨k, hk, a, ha⟩
        have h2 : χ ⟨k, hk, a, ha⟩ = a := hinj _ _ (by rw [← hχ, ← ha])
        rw [hρ', h2] at h1
        conv_rhs => rw [← h1, smul_smul, mul_inv_cancel₀ (hne k a ha), one_smul]
    have h3 := Submodule.sum_mem _ key
    rwa [← this] at h3

  have intersectLocalEigenspaces {M : Type} [AddCommGroup M] [Module ℂ M] {J : Type} [Fintype J] {G : J → Type} [∀ j, Group (G j)] (ρ : ∀ j, Representation ℂ (G j) M)
      (K : ∀ j, Subgroup (G j)) (hc : ∀ j j', j ≠ j' → ∀ g g' y, ρ j g (ρ j' g' y) = ρ j' g' (ρ j g y))
      {κ : Type 1} (Y : κ → Submodule ℂ M)
      (hst : ∀ j i, ∀ k ∈ K j, ∀ y ∈ Y i, ρ j k y ∈ Y i)
      (hfin : ∀ j i, ∀ y ∈ Y i, ∃ U : Subgroup (G j), U.relIndex (K j) ≠ 0 ∧ y ∈ fixd (ρ j) U) {F : M} (hF : F ∈ ⨆ i, Y i) :
      F ∈ ⨆ i, Y i ⊓ ⨅ j, matchingEigenvectors (ρ j) (K j) F := by
    classical
    have key : ∀ s : Finset J, F ∈ ⨆ i, Y i ⊓ ⨅ j ∈ s, matchingEigenvectors (ρ j) (K j) F := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hF
      | insert j s hj ih =>
        have := averageIntoEigenspaces (ρ j) (K j) (fun i => Y i ⊓ ⨅ j ∈ s, matchingEigenvectors (ρ j) (K j) F) (fun i k hk y hy => ⟨hst j i k hk y hy.1, ?_⟩)
          (fun i y hy => hfin j i y hy.1) ih
        · refine IsConcreteLE.le_iff.1 (iSup_mono fun i => le_of_eq ?_) this
          rw [Finset.iInf_insert, inf_assoc, inf_comm (matchingEigenvectors (ρ j) (K j) F)]
        · have h2 := hy.2
          simp only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢
          intro j' hj'
          exact matchingEigenvectors_stable _ _ _ _ (fun g y => hc j' j (fun h => hj (h ▸ hj')) g k y) (h2 j' hj')
    simpa using key Finset.univ

  have smoothSummand {M : Type} [AddCommGroup M] [Module ℂ M] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G M}
      {Y : Submodule ℂ M} {σ : SmIrr G} (h : IsoSum ρ Y σ) {y : M} (hy : y ∈ Y) :
      (∀ g, ρ g y ∈ Y) ∧ ∀ K : Subgroup G, IsCompact (K : Set G) → ∃ U : Subgroup G, U.relIndex K ≠ 0 ∧ y ∈ fixd ρ U := by
    refine Submodule.iSup_induction _ (motive := fun y => (∀ g, ρ g y ∈ Y) ∧
      ∀ K : Subgroup G, IsCompact (K : Set G) → ∃ U : Subgroup G, U.relIndex K ≠ 0 ∧ y ∈ fixd ρ U) (h hy) ?_ ?_ ?_
    · rintro ⟨f, hf, hle⟩ _ ⟨v, rfl⟩
      refine ⟨fun g => hle ⟨_, hf g v⟩, fun K hK => ?_⟩
      let T : Subgroup G :=
        { carrier := {g | σ.ρ g v = v}
          one_mem' := by simp
          mul_mem' := fun {a b} (ha : σ.ρ a v = v) (hb : σ.ρ b v = v) => by
            change σ.ρ (a * b) v = v
            rw [map_mul, mul_apply_eq_comp, hb, ha]
          inv_mem' := fun {a} (ha : σ.ρ a v = v) => by
            change σ.ρ a⁻¹ v = v
            conv_lhs => rw [← ha]
            rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl }
      have : CompactSpace K := isCompact_iff_compactSpace.1 hK
      have ho : IsOpen (T.subgroupOf K : Set K) := (σ.smooth v).preimage continuous_subtype_val
      have := Subgroup.quotient_finite_of_isOpen _ ho
      refine ⟨T, Subgroup.index_ne_zero_of_finite, fun u (hu : σ.ρ u v = v) => ?_⟩
      change ρ u (f v) = f v
      rw [← hf, hu]
    · exact ⟨fun g => by simp, fun K _ => ⟨⊤, by simp, zero_mem _⟩⟩
    · intro a b ha hb
      refine ⟨fun g => by rw [LinearMap.map_add]; exact add_mem (ha.1 g) (hb.1 g), fun K hK => ?_⟩
      obtain ⟨U, hU, h1⟩ := ha.2 K hK
      obtain ⟨U', hU', h2⟩ := hb.2 K hK
      exact ⟨U ⊓ U', Subgroup.relIndex_inf_ne_zero hU hU', add_mem (fun u hu => h1 u hu.1) (fun u hu => h2 u hu.2)⟩

  have decomposeGeneralizedEigenspace {M : Type} [AddCommGroup M] [Module ℂ M] {κ : Type 1} (Y : κ → Submodule ℂ M) (W : Submodule ℂ M) [FiniteDimensional ℂ W] (T : Module.End ℂ M)
      (hW : ∀ y ∈ W, T y ∈ W) (hY : ∀ i, ∀ y ∈ Y i, T y ∈ Y i) (h : W ≤ ⨆ i, Y i ⊓ W) (μ : ℂ) :
      W ⊓ T.maxGenEigenspace μ ≤ ⨆ i, Y i ⊓ (W ⊓ T.maxGenEigenspace μ) := by
    have h1 : ∀ i, Y i ⊓ W ≤ ⨆ ν, (Y i ⊓ W) ⊓ T.maxGenEigenspace ν := fun i => by
      have : FiniteDimensional ℂ (Y i ⊓ W : Submodule ℂ M) := Submodule.finiteDimensional_of_le inf_le_right
      have hm : ∀ y ∈ Y i ⊓ W, T y ∈ Y i ⊓ W := fun y hy => ⟨hY i y hy.1, hW y hy.2⟩
      have h0 := congrArg (Submodule.map (Y i ⊓ W).subtype) (Module.End.iSup_maxGenEigenspace_eq_top (T.restrict hm))
      rw [Submodule.map_iSup, Submodule.map_subtype_top] at h0
      refine h0.ge.trans (iSup_mono fun ν => ?_)
      exact (Submodule.inf_genEigenspace T (Y i ⊓ W) hm).ge
    have h2 : W ≤ (⨆ i, Y i ⊓ (W ⊓ T.maxGenEigenspace μ)) ⊔ ⨆ ν ≠ μ, T.maxGenEigenspace ν := by
      refine h.trans (iSup_le fun i => (h1 i).trans (iSup_le fun ν => ?_))
      by_cases hν : ν = μ
      · subst hν
        rw [inf_assoc]
        exact le_sup_of_le_left (le_iSup (fun i => Y i ⊓ (W ⊓ T.maxGenEigenspace ν)) i)
      · exact le_sup_of_le_right (inf_le_right.trans (le_iSup₂ (f := fun ν (_ : ν ≠ μ) => T.maxGenEigenspace ν) ν hν))
    have h3 : (⨆ i, Y i ⊓ (W ⊓ T.maxGenEigenspace μ)) ≤ T.maxGenEigenspace μ :=
      iSup_le fun i => inf_le_right.trans inf_le_right
    refine (inf_le_inf_right _ h2).trans ?_
    rw [sup_inf_assoc_of_le _ h3, (T.independent_maxGenEigenspace μ).symm.eq_bot, sup_bot_eq]

  have uOp_preserves {M : Type} [AddCommGroup M] [Module ℂ M] {G : Type} [Group G] (I : Iwa G) (π : Representation ℂ G M) (a : G) (Y : Submodule ℂ M)
      (hY : ∀ g, ∀ y ∈ Y, π g y ∈ Y) : ∀ y ∈ Y, I.uOp π a y ∈ Y := by
    unfold Iwa.uOp
    refine finsum_induction (fun φ : Module.End ℂ M => ∀ y ∈ Y, φ y ∈ Y) (fun y _ => by simp)
      (fun φ ψ h h' y hy => add_mem (h y hy) (h' y hy)) fun q => hY _

  let stabilizer {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (y : M) : Subgroup G := {
    carrier := {g | π g y = y}
    one_mem' := by simp
    mul_mem' {a b} (ha : π a y = y) (hb : π b y = y) := by
      change π (a * b) y = y
      rw [map_mul, mul_apply_eq_comp, hb, ha]
    inv_mem' {a} (ha : π a y = y) := by
      change π a⁻¹ y = y
      conv_lhs => rw [← ha]
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl }

  have mem_fixed_iff {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (y : M) (U : Subgroup G) :
      y ∈ fixd π U ↔ U ≤ stabilizer π y := Iff.rfl

  have stableUnderProduct {J M : Type} [Fintype J] [DecidableEq J] {G : J → Type} [∀ j, Group (G j)] [AddCommGroup M] [Module ℂ M]
      (π : Representation ℂ (∀ j, G j) M) (Y : Submodule ℂ M) (h : ∀ j g, ∀ y ∈ Y, π (Pi.mulSingle j g) y ∈ Y) :
      ∀ g, ∀ y ∈ Y, π g y ∈ Y := by
    let S : Subgroup (∀ j, G j) :=
      { carrier := {g | (∀ y ∈ Y, π g y ∈ Y) ∧ ∀ y ∈ Y, π g⁻¹ y ∈ Y}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => ⟨fun y hy => by rw [map_mul]; exact ha.1 _ (hb.1 y hy),
          fun y hy => by rw [mul_inv_rev, map_mul]; exact hb.2 _ (ha.2 y hy)⟩
        inv_mem' := fun {a} ha => ⟨ha.2, by simpa using ha.1⟩ }
    intro g
    have : g ∈ S := Subgroup.pi_mem_of_mulSingle_mem g fun j => ⟨h j _, by rw [← Pi.mulSingle_inv]; exact h j _⟩
    exact this.1

  have commuteActions (u : H.X.Ub) (b : GV n H.Sl) (F : Fin H.m → H.X.Fn ℂ d) :
      H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m b F) = H.X.rpF ℂ d H.m b (H.X.raF d (H.τC ι) u F) := by
    ext i g k
    change ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec fun j => F j (g * ((u : H.Ga), 1) * (1, b)) k) i =
      ((H.τC ι u : Matrix (Fin H.m) (Fin H.m) ℂ).mulVec fun j => F j (g * (1, b) * ((u : H.Ga), 1)) k) i
    simp [mul_assoc]

  have preserveFixed (U : Subgroup H.X.Ub) (b : GV n H.Sl) :
      ∀ F ∈ fixd (H.X.raF d (H.τC ι)) U, H.X.rpF ℂ d H.m b F ∈ fixd (H.X.raF d (H.τC ι)) U := fun F hF u hu => by
    rw [commuteActions, hF u hu]

  have preserveBig (b : GV n H.Sl) :
      ∀ F ∈ H.Big ι ξ, H.X.rpF ℂ d H.m b F ∈ H.Big ι ξ := fun F hF => by
    refine ⟨fun i hi γ g => ?_, preserveFixed _ b F hF.2⟩
    have := hF.1 i hi γ (g * (1, b))
    rw [← mul_assoc] at this
    exact this

  let e := c0
  have memClassical (F : Fin H.m → H.X.Fn ℂ d) : F ∈ H.ClAt θ ι x.toRingHom lam ξ K e ↔
      F ∈ H.Big ι ξ ∧ F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) ∧ F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N ∧
        F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) ∧ ∀ v i y,
        H.X.rpF ℂ d H.m (eV n H.Sl v i y : H.X.I.T) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F := by
    simp only [HSet.ClAt, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, and_assoc]

  have fixedByIwahori (c0 : ℕ) (he : c0 ≤ e)
      (triv : ∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (y : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (c0 + 1) →
        H.finPart θ x.toRingHom lam v i y = 1) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.ClAt θ ι x.toRingHom lam ξ K e) :
      F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e) := by
    classical
    obtain ⟨-, -, h1, h2, h3⟩ := (memClassical F).1 hF
    rw [mem_fixed_iff] at h1 h2 ⊢
    refine sup_le (sup_le h1 fun t ht => ?_) h2
    refine Subgroup.pi_mem_of_mulSingle_mem t fun v => ?_
    have htv : t v ∈ (glIwa ((H.Sl v).adicCompletion L) n).Tc c0 :=
      (glIwa ((H.Sl v).adicCompletion L) n).Tc_anti he (ht v trivial)
    obtain ⟨y, hy, hy'⟩ := (glBridge ((H.Sl v).adicCompletion L) n ℂ (Representation.trivial ℂ _ ℂ)).2.2.2.2.2.2.2.2.2
      ⟨t v, (glIwa _ n).Tc_le c0 htv⟩
    have hy1 : t v = _ := hy
    rw [hy1]
    change MonoidHom.mulSingle (fun v : H.V => GLw n (H.Sl v)) v _ ∈ _
    rw [map_list_prod, List.map_ofFn]
    refine Subgroup.list_prod_mem _ fun g hg => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
    have := h3 v i (y i)
    rw [triv v i (y i) (hy' c0 htv i), map_one, inv_one, one_smul] at this
    exact this

  have preserveClassical (c0 : ℕ) (he : c0 ≤ e)
      (triv : ∀ v i (y : Uo ((H.Sl v).adicCompletion L)), (y : ((H.Sl v).adicCompletion L)ˣ) ∈ Uc _ (c0 + 1) →
        H.finPart θ x.toRingHom lam v i y = 1) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.ClAt θ ι x.toRingHom lam ξ K e) :
      H.uzC ι lam d F ∈ H.ClAt θ ι x.toRingHom lam ξ K e := by
    refine Submodule.smul_mem _ _ ?_
    have h0 := (uOpLevel _ H.X.I ℂ _ (H.X.rpF ℂ d H.m) e).1 _ H.X.I.z_mem F (fixedByIwahori c0 he triv F hF)
    obtain ⟨hb, hl, h1, h2, h3⟩ := (memClassical F).1 hF
    refine (memClassical _).2 ⟨uOp_preserves _ _ _ _ preserveBig F hb, uOp_preserves _ _ _ _ (preserveFixed _) F hl,
      fun u hu => h0 u (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu)), fun u hu => h0 u (Subgroup.mem_sup_right hu),
      fun v i y => ?_⟩
    rw [(uOpMul _ H.X.I ℂ _ (H.X.rpF ℂ d H.m) _ _ H.X.I.z_mem H.X.I.z_mem F h1).2.2.2.1 _ (eV n H.Sl v i y).2, h3, map_smul]

  have iwa_le_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n e : ℕ) :
      (glIwa k n).N ≤ KO k (Fin n) ∧ (glIwa k n).Nm e ≤ KO k (Fin n) ∧ (glIwa k n).T ≤ KO k (Fin n) := by
    refine ⟨inf_le_right, fun g hg => ?_, fun g hg => ?_⟩
    · obtain ⟨h, -, rfl⟩ := hg.2
      exact ⟨h, rfl⟩
    · have h1 : g ∈ (glIwa k n).Iw 0 := Subgroup.mem_sup_left (Subgroup.mem_sup_right hg)
      rw [(glBridge k n ℂ (Representation.trivial ℂ _ ℂ)).2.2.2.2.2.1] at h1
      exact iwahori_le_KO k _ h1

  have memClassicalOfLocalEigenspaces (F y : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.ClAt θ ι x.toRingHom lam ξ K e) (hy : y ∈ H.Big ι ξ)
      (hq : ∀ q, y ∈ matchingEigenvectors (H.atW ι d (H.wq q)) (K.1 q) F)
      (hv : ∀ v, y ∈ matchingEigenvectors (H.atV d v) (KO ((H.Sl v).adicCompletion L) (Fin n)) F) : y ∈ H.ClAt θ ι x.toRingHom lam ξ K e := by
    classical
    obtain ⟨hb, hl, h1, h2, h3⟩ := (memClassical F).1 hF
    have key : ∀ U : ∀ v, Subgroup (GLw n (H.Sl v)), (∀ v, U v ≤ KO ((H.Sl v).adicCompletion L) (Fin n)) →
        F ∈ fixd (H.X.rpF ℂ d H.m) (Subgroup.pi Set.univ U) → y ∈ fixd (H.X.rpF ℂ d H.m) (Subgroup.pi Set.univ U) := by
      intro U hU h
      rw [mem_fixed_iff, Subgroup.pi_le_iff] at h ⊢
      rintro v _ ⟨g, hg, rfl⟩
      have := hv v g (hU v hg) 1 (by rw [one_smul]; exact h v ⟨g, hg, rfl⟩)
      rw [one_smul] at this
      exact this
    refine (memClassical _).2 ⟨hy, ?_, key _ (fun v => (iwa_le_KO _ n e).1) h1, key _ (fun v => (iwa_le_KO _ n e).2.1) h2,
      fun v i z => hv v (eT _ n i z : GLw n (H.Sl v)) ((iwa_le_KO _ n e).2.2 (eT _ n i z).2) _ (h3 v i z)⟩
    rw [mem_fixed_iff] at hl ⊢
    refine sup_le hy.2 (iSup_le fun q => ?_)
    rintro _ ⟨g, hg, rfl⟩
    have := hq q g hg 1 (by
      rw [one_smul]
      exact hl (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem q ⟨g, hg, rfl⟩)))
    rw [one_smul] at this
    exact this

  have partStable (Y : H.Part ι lam ξ) : ∀ g, ∀ y ∈ Y.Y, H.X.rpF ℂ d H.m g y ∈ Y.Y := by
    classical
    exact stableUnderProduct (G := fun v : H.V => GLw n (H.Sl v)) (H.X.rpF ℂ d H.m) Y.Y fun v g z hz => (smoothSummand (Y.isoL v) hz).1 g

  have partUzStable (Y : H.Part ι lam ξ) : ∀ y ∈ Y.Y, H.uzC ι lam d y ∈ Y.Y := fun y hy =>
    Submodule.smul_mem _ _ (uOp_preserves H.X.I (H.X.rpF ℂ d H.m) H.X.I.z Y.Y (partStable Y) y hy)

  have commuteAtDistinctQ (hH : H.Ax) (q q' : H.Q) (hq : q ≠ q') (g : GLw n (H.wq q)) (g' : GLw n (H.wq q'))
      (y : Fin H.m → H.X.Fn ℂ d) :
      H.atW ι d (H.wq q) g (H.atW ι d (H.wq q') g' y) = H.atW ι d (H.wq q') g' (H.atW ι d (H.wq q) g y) := by
    change H.X.raF d (H.τC ι) _ (H.X.raF d (H.τC ι) _ y) = H.X.raF d (H.τC ι) _ (H.X.raF d (H.τC ι) _ y)
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul]
    exact congrArg (fun z : H.X.Ub => H.X.raF d (H.τC ι) z y) (hH.Q_Q q q' hq g g').eq

  have commuteAtDistinctV (v v' : H.V) (hv : v ≠ v') (g : GLw n (H.Sl v)) (g' : GLw n (H.Sl v'))
      (y : Fin H.m → H.X.Fn ℂ d) : H.atV d v g (H.atV d v' g' y) = H.atV d v' g' (H.atV d v g y) := by
    classical
    change H.X.rpF ℂ d H.m _ (H.X.rpF ℂ d H.m _ y) = H.X.rpF ℂ d H.m _ (H.X.rpF ℂ d H.m _ y)
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul]
    exact congrArg (fun z => H.X.rpF ℂ d H.m z y) (Pi.mulSingle_commute (f := fun v : H.V => GLw n (H.Sl v)) hv g g').eq

  have commuteAtQV (q : H.Q) (v : H.V) (g : GLw n (H.wq q)) (g' : GLw n (H.Sl v))
      (y : Fin H.m → H.X.Fn ℂ d) : H.atW ι d (H.wq q) g (H.atV d v g' y) = H.atV d v g' (H.atW ι d (H.wq q) g y) :=
    commuteActions (H.sec (H.wq q) g) _ y

  have decomposeClassicalVector (hH : H.Ax) {κ : Type 1} (Y : κ → H.Part ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d)
      (hF : F ∈ H.ClAt θ ι x.toRingHom lam ξ K e) (h0 : F ∈ ⨆ i, (Y i).Y) : F ∈ ⨆ i, (Y i).Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K e := by
    have hQ := intersectLocalEigenspaces (fun q : H.Q => H.atW ι d (H.wq q)) K.1 (commuteAtDistinctQ hH)
      (fun i => (Y i).Y) (fun q i k _ y hy => (smoothSummand ((Y i).isoQ q) hy).1 k)
      (fun q i y hy => (smoothSummand ((Y i).isoQ q) hy).2 _ (K.2 q).2) h0
    have hV := intersectLocalEigenspaces (fun v : H.V => H.atV d v) (fun v => KO ((H.Sl v).adicCompletion L) (Fin n)) (commuteAtDistinctV)
      (fun i => (Y i).Y ⊓ ⨅ q : H.Q, matchingEigenvectors (H.atW ι d (H.wq q)) (K.1 q) F)
      (fun v i k _ y hy => ⟨(smoothSummand ((Y i).isoL v) hy.1).1 k, (Submodule.mem_iInf _).2 fun q =>
        matchingEigenvectors_stable (H.atW ι d (H.wq q)) (K.1 q) F (H.atV d v k) (fun g z => commuteAtQV q v g k z)
          ((Submodule.mem_iInf _).1 hy.2 q)⟩)
      (fun v i y hy => (smoothSummand ((Y i).isoL v) hy.1).2 _ GlobalTheory.SplitFlip.isCompact_KO) hQ
    refine IsConcreteLE.le_iff.1 (iSup_mono fun i y hy => ?_) hV
    exact ⟨hy.1.1, memClassicalOfLocalEigenspaces F y hF ((Y i).le hy.1.1) ((Submodule.mem_iInf _).1 hy.1.2)
      ((Submodule.mem_iInf _).1 hy.2)⟩

  have h1 : H.ClAt θ ι x.toRingHom lam ξ K c0 ≤
      ⨆ Y : {Y : H.Part ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    intro F hF
    have hF' := (memClassical F).1 hF
    exact decomposeClassicalVector hH (fun Y : {Y : H.Part ι lam ξ // P lam d ξ Y} => Y.1) F hF
      (hP lam hlam d ξ hs.alg F hF'.1 ⟨K, hF'.2.1⟩ ⟨c0, fixedByIwahori c0 le_rfl hs.triv F hF⟩)
  refine le_antisymm (iSup_le fun μ => ?_) (iSup_le fun _ => inf_le_right)
  have := hs.fin K c0 le_rfl
  have h2 := decomposeGeneralizedEigenspace (fun Y : {Y : H.Part ι lam ξ // P lam d ξ Y} => Y.1.Y) (H.ClAt θ ι x.toRingHom lam ξ K c0) (H.uzC ι lam d)
    (preserveClassical c0 le_rfl hs.triv) (fun Y => partUzStable Y.1) h1 μ.1
  have h3 : H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1 ≤ H.OrdAt θ ι x.toRingHom lam ξ K c0 :=
    le_iSup (fun μ : {μ : ℂ // ‖ι.symm μ‖ = 1} =>
      H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1) μ
  exact h2.trans (iSup_mono fun Y => inf_le_inf_left _ h3)

open TensorProduct in
set_option synthInstance.maxHeartbeats 200000 in
theorem partPt : GlobalTheory.Mem.LiteralAutomorphy.LitN → PartPt := by
  intro _ L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ y hy
  have : Finite (ResidueField c.O) := by
    have : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    have : Finite (ResidueField ℤ_[l]) := IsCNL.finite
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  have : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hComm, hfin, hfree, hK⟩ := hiComm L Ω l n c H hH A θ hθ K
  have := (hK a).2.1
  obtain ⟨e, -, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem
    A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) hComm

  let Y₀ := H.X.Ord (H.τA A) θ (H.lev K)
  let Y₁ := H.MK θ a K
  let W := Fin H.m → H.X.Fn ℂ d
  let χ := ι.toRingHom.comp x.toRingHom
  let : Algebra A ℂ := χ.toAlgebra
  let : Module A W := Module.compHom W χ
  have : IsScalarTower A ℂ W := ⟨fun b z F => mul_smul (χ b) z F⟩
  let s : Y₀ →ₗ[A] W :=
    { toFun := fun f => sp f
      map_add' := fun f g => hsp.add K _ f.2 _ g.2
      map_smul' := fun b f => hsp.smul K _ f.2 b }
  let baseChange := s.liftBaseChange ℂ
  have hs : Function.Injective baseChange := by
    let b := Module.Free.chooseBasis A Y₀
    have hb : baseChange = Finsupp.linearCombination ℂ (fun i => sp (b i)) ∘ₗ
        (b.baseChange ℂ).repr.toLinearMap :=
      (b.baseChange ℂ).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
          Finsupp.linearCombination_single, Module.Basis.baseChange_apply, LinearMap.liftBaseChange_tmul]
        rfl
    rw [hb, LinearMap.coe_comp]
    exact Function.Injective.comp (hsp.indep K _ b) (b.baseChange ℂ).repr.injective
  let O := LinearMap.range baseChange
  have hO : O = H.OrdAt θ ι x.toRingHom lam ξ K c0 := by
    change LinearMap.range (s.liftBaseChange ℂ) = _
    rw [LinearMap.range_liftBaseChange, ← hsp.span K c0 le_rfl, Set.image_eq_range]
    rfl
  have : FiniteDimensional ℂ O := Module.Finite.equiv (LinearEquiv.ofInjective baseChange hs)
  let op₀ (i : H.Op) : Module.End A Y₀ := (H.op A i).restrict (hComm.1 i)
  have intertwines (i : H.Op) : H.opC ι lam d i ∘ₗ baseChange =
      baseChange ∘ₗ (op₀ i).baseChange ℂ := by
    refine TensorProduct.AlgebraTensorModule.ext fun z f => ?_
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
      baseChange, map_smul]
    exact congrArg (z • ·) (hsp.op K i _ f.2).symm
  let Ψ := LinearEquiv.ofInjective baseChange hs
  let opO (i : H.Op) : Module.End ℂ O :=
    (Ψ.conjRingEquiv : Module.End ℂ (ℂ ⊗[A] Y₀) ≃+* Module.End ℂ O) ((op₀ i).baseChange ℂ)
  have opO_apply (i : H.Op) (F : O) : (opO i F : W) = H.opC ι lam d i F := by
    obtain ⟨v, rfl⟩ := Ψ.surjective F
    change (Ψ ((op₀ i).baseChange ℂ (Ψ.symm (Ψ v))) : W) = H.opC ι lam d i (Ψ v : W)
    rw [Ψ.symm_apply_apply]
    exact (LinearMap.congr_fun (intertwines i) v).symm
  have opO_commute (i j : H.Op) : Commute (opO i) (opO j) := by
    have hc : Commute (op₀ i) (op₀ j) :=
      LinearMap.ext fun f => Subtype.ext (hComm.2 i j f f.2)
    exact (hc.map (Module.End.baseChangeHom A ℂ Y₀)).map Ψ.conjRingEquiv

  let incl : Y₁ →ₗ[A] Y₀ := Submodule.inclusion inf_le_left
  let proj : Y₀ →ₗ[A] Y₁ := LinearMap.codRestrict _ (Y₀.subtype ∘ₗ e)
    (fun f => (hY _).2 (LinearMap.congr_fun hi.eq f))
  have hproj : proj ∘ₗ incl = LinearMap.id :=
    LinearMap.ext fun f => Subtype.ext
      (congrArg (fun g : Y₀ => (g : H.X.Fn A H.m)) ((hY (incl f)).1 f.2))
  have hincl : Function.Injective (incl.baseChange ℂ) := by
    refine Function.LeftInverse.injective (g := proj.baseChange ℂ) fun v => ?_
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hproj,
      LinearMap.baseChange_id, LinearMap.id_apply]
  let z : H.TK θ a K →ₐ[A] ℂ :=
    { toRingHom := ι.toRingHom.comp y.toRingHom
      commutes' := fun b => congrArg ι (RingHom.congr_fun hy b) }
  obtain ⟨v, hv, hvEig⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig
    (M := ↥(H.MK θ a K)) z
  let F := Ψ (incl.baseChange ℂ v)
  have hF : F ≠ 0 := fun h => hv (hincl (Ψ.map_eq_zero_iff.mp h))
  have hEig (i : H.Op) : opO i F = z (H.gen θ a K i) • F := by
    have hi : op₀ i ∘ₗ incl = incl ∘ₗ Algebra.lsmul A A Y₁ (H.gen θ a K i) :=
      LinearMap.ext fun f => Subtype.ext rfl
    have Hbase := LinearMap.congr_fun (congrArg (fun f : Y₁ →ₗ[A] Y₀ => f.baseChange ℂ) hi) v
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      hvEig, map_smul] at Hbase
    change Ψ ((op₀ i).baseChange ℂ (Ψ.symm (Ψ (incl.baseChange ℂ v)))) = _
    rw [Ψ.symm_apply_apply, Hbase, map_smul]

  let J := {Y : H.Part ι lam ξ // P lam d ξ Y}
  let Z (j : J) := j.1.Y.comap O.subtype
  have hZ : ⨆ j, Z j = ⊤ := by
    apply Submodule.map_injective_of_injective O.subtype_injective
    rw [Submodule.map_iSup, Submodule.map_subtype_top]
    simp_rw [Z, Submodule.map_comap_subtype, inf_comm O]
    exact (hO.symm ▸ ord_parts H hH θ ι hP x lam d ξ c0 sp hsp hlam K).symm
  have stable (j : J) (i : H.Op) (G : O) (hG : G ∈ Z j) : opO i G ∈ Z j := by
    classical
    have stableAtV (v : H.V) (g : GLw n (H.Sl v)) : ∀ G ∈ j.1.Y, H.atV d v g G ∈ j.1.Y := by
      intro G hG
      refine (iSup_le (a := j.1.Y.comap (H.atV d v g)) ?_) (j.1.isoL v hG)
      rintro f _ ⟨t, rfl⟩
      change H.atV d v g (f.1 t) ∈ j.1.Y
      rw [← f.2.1]
      exact f.2.2 ⟨_, rfl⟩
    let S : Subgroup (GV n H.Sl) :=
      { carrier := {g | (∀ G ∈ j.1.Y, H.X.rpF ℂ d H.m g G ∈ j.1.Y) ∧
          ∀ G ∈ j.1.Y, H.X.rpF ℂ d H.m g⁻¹ G ∈ j.1.Y}
        one_mem' := ⟨fun G hG => by simpa using hG, fun G hG => by simpa using hG⟩
        mul_mem' := fun {g g'} hg hg' => ⟨fun G hG => by rw [map_mul]; exact hg.1 _ (hg'.1 _ hG),
          fun G hG => by rw [mul_inv_rev, map_mul]; exact hg'.2 _ (hg.2 _ hG)⟩
        inv_mem' := fun {g} hg => ⟨hg.2, by simpa using hg.1⟩ }
    change (opO i G : W) ∈ j.1.Y
    rw [opO_apply]
    rcases i with i | i
    · change sphOp (H.atW ι d i.1.1) (i.2 + 1) G ∈ _
      rw [j.1.sph i.1 _ G hG]
      exact j.1.Y.smul_mem _ hG
    · refine j.1.Y.smul_mem _ ?_
      refine finsum_induction (p := fun φ : Module.End ℂ W => φ G ∈ j.1.Y) (zero_mem _)
        (fun _ _ => add_mem) fun q => ?_
      exact (Subgroup.pi_mem_of_mulSingle_mem (H := S) _ fun v =>
        ⟨stableAtV v _, by rw [← Pi.mulSingle_inv]; exact stableAtV v _⟩).1 G hG
  obtain ⟨φ, hφ, hφEig⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.quotOfEig
    opO opO_commute (fun i => z (H.gen θ a K i)) F hF hEig
  obtain ⟨j, hj⟩ : ∃ j, φ ∘ₗ (Z j).subtype ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hφ (LinearMap.ker_eq_top.1 (top_le_iff.1 (hZ ▸ iSup_le fun j G hG => ?_)))
    exact LinearMap.congr_fun (hn j) ⟨G, hG⟩
  obtain ⟨G, hG, hGEig⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot
    (fun i => (opO i).restrict (stable j i))
    (fun i k => LinearMap.ext fun G => Subtype.ext (LinearMap.congr_fun (opO_commute i k).eq G))
    (fun i => z (H.gen θ a K i)) _ hj (fun i G => hφEig i G)
  refine ⟨j.1, G, j.2, fun h => hG (Subtype.ext (Subtype.ext h)), ⟨G.2, hO ▸ G.1.2⟩, fun i => ?_⟩
  rw [← opO_apply]
  exact congrArg (fun f : Z j => (f.1 : W)) (hGEig i)

end UpperTheory.V.Z.Ord
