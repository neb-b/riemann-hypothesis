module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SphComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2HeckeMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2HeckeMap :
    ∀ (A M M' ι ι' : Type) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] (Y : Submodule A M) (Y' : Submodule A M') (op : ι → Module.End A M) (op' : ι' → Module.End A M') [Fact (CommOn Y op)] [Fact (CommOn Y' op')] (φ : Y →ₗ[A] Y') (j : ι' → ι), Function.Injective φ → (∀ i (y : Y), ((φ ((heckeGen Y op (j i) : Module.End A Y) y) : Y') : M') = op' i (φ y)) → ∃ ψ : heckeAlg Y' op' →ₐ[A] heckeAlg Y op, (∀ i, ψ (heckeGen Y' op' i) = heckeGen Y op (j i)) ∧ ∀ (t : heckeAlg Y' op') (y : Y), φ ((ψ t : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
  intro A M M' ι ι' _ _ _ _ _ Y Y' op op' _ _ φ j hφ hop
  have uniq : ∀ (t : Module.End A Y') (s s' : heckeAlg Y op),
      (∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)) → (∀ y : Y, φ ((s' : Module.End A Y) y) = t (φ y)) → s = s' := by
    intro t s s' h h'
    exact Subtype.ext (LinearMap.ext fun y => hφ ((h y).trans (h' y).symm))
  have ex : ∀ t : heckeAlg Y' op', ∃ s : heckeAlg Y op,
      ∀ y : Y, φ ((s : Module.End A Y) y) = (t : Module.End A Y') (φ y) := by
    rintro ⟨t, ht⟩
    change ∃ s : heckeAlg Y op, ∀ y : Y, φ ((s : Module.End A Y) y) = t (φ y)
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, hi⟩ := hx
      exact ⟨heckeGen Y op (j i), fun y => Subtype.ext ((hop i y).trans (hi (φ y)).symm)⟩
    | algebraMap r =>
      refine ⟨algebraMap A _ r, fun y => ?_⟩
      change φ (r • y) = r • φ y
      exact map_smul φ r y
    | add a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s + s', fun y => ?_⟩
      change φ ((s : Module.End A Y) y + (s' : Module.End A Y) y) = a (φ y) + b (φ y)
      rw [map_add (f := _), hs, hs']
    | mul a b _ _ ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s * s', fun y => ?_⟩
      change φ ((s : Module.End A Y) ((s' : Module.End A Y) y)) = a (b (φ y))
      rw [hs, hs']
  choose f hf using ex
  refine ⟨{ toFun := f
            map_one' := uniq _ _ _ (hf 1) fun y => rfl
            map_mul' := fun a b => uniq _ _ _ (hf (a * b)) fun y => ?_
            map_zero' := uniq _ _ _ (hf 0) fun y => map_zero φ
            map_add' := fun a b => uniq _ _ _ (hf (a + b)) fun y => ?_
            commutes' := fun r => uniq _ _ _ (hf (algebraMap A _ r)) fun y => map_smul φ r y }, fun i => ?_, hf⟩
  · change φ ((f a : Module.End A Y) ((f b : Module.End A Y) y)) = (a : Module.End A Y') ((b : Module.End A Y') (φ y))
    rw [hf, hf]
  · change φ ((f a : Module.End A Y) y + (f b : Module.End A Y) y) = (a : Module.End A Y') (φ y) + (b : Module.End A Y') (φ y)
    rw [map_add (f := _), hf, hf]
  · exact uniq _ _ _ (hf (heckeGen Y' op' i)) fun y => Subtype.ext (hop i y)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2IwLev
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Loc
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
  (C : Subgroup 𝓀[k]ˣ)

private theorem iwLev_loc : IsOpen (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) ∧ IsCompact (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) ∧
    AlgebraTools.iwC k n C ≤ AlgebraTools.iwC k n ⊤ := by
  have h1 := (AlgebraTools.memIwC k n C).1
  have h2 := (AlgebraTools.memIwC k n C).2.1
  have hle : AlgebraTools.iwC k n C ≤ AlgebraTools.iwC k n ⊤ := by
    intro g hg
    rw [h2]
    exact ((h1 g).1 hg).1
  have hopen : IsOpen (AlgebraTools.iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (show KOne k (Fin n) ≤ AlgebraTools.iwC k n C from le_sup_left.trans le_sup_left)
      GlobalTheory.StepData.isOpen_KOne
  refine ⟨hopen, ?_, hle⟩
  refine IsCompact.of_isClosed_subset GlobalTheory.SplitFlip.isCompact_KO (Subgroup.isClosed_of_isOpen _ hopen) ?_
  intro g hg
  exact GlobalTheory.SmGL.iwahori_le_KO k (Fin n) ((h1 g).1 hg).1

private theorem iwLev_conj {x g : GL (Fin n) k} (hx : x ∈ AlgebraTools.iwC k n C) (hg : g ∈ AlgebraTools.iwC k n ⊤) :
    g * x * g⁻¹ ∈ AlgebraTools.iwC k n C := by
  have h2 := (AlgebraTools.memIwC k n C).2.1
  have h3 := (AlgebraTools.memIwC k n C).2.2.1
  rw [h2] at hg
  exact h3 g hg x hx

end Loc

theorem UpperTheory.V.Hi.levelUR2IwLev :
    ∀ (l : ℕ) (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L), (∀ j C, IsOpen (AlgebraTools.iwC ((w j).adicCompletion L) n C : Set (GLw n (w j))) ∧ IsCompact (AlgebraTools.iwC ((w j).adicCompletion L) n C : Set (GLw n (w j))) ∧ AlgebraTools.iwC ((w j).adicCompletion L) n C ≤ AlgebraTools.iwC ((w j).adicCompletion L) n ⊤) ∧ ((Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)).Normal := by
  intro l L _ _ n q w
  refine ⟨fun j C => iwLev_loc _ n C, ?_⟩
  have hle : Pa.UIw1 l n w ≤ Pa.UIw n w := by
    intro g hg
    simp only [Pa.UIw, Pa.UIw1, Subgroup.mem_pi] at hg ⊢
    intro j hj
    exact (iwLev_loc _ n _).2.2 (hg j hj)
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro h g hh hg
  simp only [Pa.UIw, Pa.UIw1, Subgroup.mem_pi] at hh hg ⊢
  intro j hj
  exact iwLev_conj _ n _ (hh j hj) (hg j hj)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.MemCongruenceSubgroupIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem integers_isLocalRing : IsLocalRing 𝒪[k] := (inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing
attribute [local instance] integers_isLocalRing

private theorem valuation_unif_eq_uniformizer : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  have h0 : x ≠ 0 := by
    rintro rfl
    exact uniformizer_pos.ne (by simpa using hx)
  exact Classical.epsilon_spec (p := fun x : kˣ => valuation k (x : k) = uniformizer k) ⟨Units.mk0 x h0, hx⟩

private theorem mem_maximal_pow_iff_valuation (c : ℕ) (x : 𝒪[k]) :
    x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c ↔ valuation k (x : k) ≤ uniformizer k ^ c := by
  have hI := Valuation.integer.integers (valuation k)
  let p : 𝒪[k] := ⟨unif k, (valuation_unif_eq_uniformizer.trans_lt uniformizer_lt_one).le⟩
  have hp : valuation k (algebraMap 𝒪[k] k p) = uniformizer k := valuation_unif_eq_uniformizer
  have e : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {p} := by
    ext y
    rw [← IsLocalRing.residue_eq_zero_iff, GlobalTheory.StepData.residue_eq_zero_iff_lt, Ideal.mem_span_singleton,
      hI.dvd_iff_le, hp, le_uniformizer_iff]
    rfl
  rw [e, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hI.dvd_iff_le, map_pow, map_pow, hp]
  rfl

private theorem mem_Kc_iff' {c : ℕ} {g : GL (Fin n) k} :
    g ∈ Kc k n c ↔ g ∈ KO k (Fin n) ∧ ∀ i j, valuation k ((g.val - 1) i j) ≤ uniformizer k ^ c := by
  have key : ∀ u : GL (Fin n) 𝒪[k],
      u ∈ (Matrix.GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).ker ↔
      ∀ i j, valuation k (((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u).val - 1) i j) ≤ uniformizer k ^ c := by
    intro u
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
    refine forall₂_congr fun i j => ?_
    have e : ((1 : GL (Fin n) (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ c)).val) i j =
        Ideal.Quotient.mk _ ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) := by
      simp only [Units.val_one, Matrix.one_apply]; split_ifs <;> simp
    rw [e]
    refine (Ideal.Quotient.eq.trans (mem_maximal_pow_iff_valuation c _)).trans (iff_of_eq ?_)
    congr 2
    simp only [Matrix.sub_apply, Matrix.one_apply]; split_ifs <;> simp <;> rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, (key u).1 hu⟩
  · rintro ⟨⟨u, rfl⟩, hu⟩
    exact ⟨u, (key u).2 hu, rfl⟩

private theorem congruence_subgroup_isOpen (c : ℕ) : IsOpen (Kc k n c : Set (GL (Fin n) k)) := by
  have e : (Kc k n c : Set (GL (Fin n) k)) = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin n) k => (g.val - 1) i j) ⁻¹' {x | valuation k x ≤ uniformizer k ^ c} := by
    ext g; simp only [SetLike.mem_coe, mem_Kc_iff', Set.mem_iInter, Set.mem_inter_iff]; rfl
  rw [e]
  refine GlobalTheory.SplitFlip.isOpen_KO.inter <|
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.preimage ?_ ?_
  · have := Units.continuous_val (M := Matrix (Fin n) (Fin n) k)
    fun_prop
  · have h0 : (valuation k).restrict ((unif k : k) ^ c) ≠ 0 := by simp
    simpa only [Valuation.restrict_le_iff, map_pow (valuation k), valuation_unif_eq_uniformizer] using Valuation.isOpen_closedBall h0

end SlopeTestRemainingChoices

private theorem eigenspace_one_eq_fixed {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M)
    (K : Subgroup H) : GlobalTheory.PRep.eig ρ K 1 = fixd ρ K := by
  ext v
  constructor
  · intro hv u hu
    have h := hv ⟨u, hu⟩
    simpa using h
  · intro hv u
    have h := hv u u.2
    simpa using h

theorem UpperTheory.V.Hi.partUR2Abs :
    ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GLw n w) M) (Z : Submodule ℂ M) (τ : SmIrr (GLw n w)), IsoSum ρ Z τ →
    (∀ K : Subgroup (GLw n w), IsCompact (K : Set (GLw n w)) → Z ⊓ fixd ρ K ≠ ⊥ → fixd τ.ρ K ≠ ⊥) ∧
    (∀ (j : ℕ) (a : ℂ), (∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v) → ∀ z ∈ Z ⊓ fixd ρ (KO (w.adicCompletion L) (Fin n)), sphOp ρ j z = a • z) ∧
    (∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (ρ' : Representation ℂ (GLw n w) M') (f : M →+ M'), (∀ g v, f (ρ g v) = ρ' g (f v)) → ∀ (j : ℕ) v, f (sphOp ρ j v) = sphOp ρ' j (f v)) ∧
    ∀ c : ℕ, IsCompact (Kc (w.adicCompletion L) n c : Set (GLw n w)) := by
  intro L _ _ n w M _ _ ρ Z τ hZ
  have hnat : ∀ (N N' : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup N'] [Module ℂ N']
      (σ : Representation ℂ (GLw n w) N) (σ' : Representation ℂ (GLw n w) N') (f : N →+ N'),
      (∀ g v, f (σ g v) = σ' g (f v)) → ∀ (j : ℕ) v, f (sphOp σ j v) = sphOp σ' j (f v) := by
    intro N N' _ _ _ _ σ σ' f hf j v
    exact (dcSum ℂ _ N σ _ _ _ ((sphComm _ n ℂ N σ).1 _)).2.2.2 ℂ N' σ' f hf v
  have key := fun (K : Subgroup (GLw n w)) (hK : IsCompact (K : Set (GLw n w))) =>
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repScalar ρ τ.ρ τ.smooth Z hZ K 1 hK (by simp)
  simp only [eigenspace_one_eq_fixed] at key
  refine ⟨fun K hK => (key K hK).1, fun j a ha => ?_, fun M' _ _ ρ' => hnat M M' ρ ρ', fun c => ?_⟩
  · refine (key _ GlobalTheory.SplitFlip.isCompact_KO).2 (sphOp ρ j) (sphOp τ.ρ j) a (fun f v _ => ?_) ha
    exact (hnat _ _ τ.ρ ρ f.1.toAddMonoidHom f.2.1 j v).symm
  · exact GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (congruence_subgroup_isOpen c))
      fun g hg => (mem_Kc_iff'.1 hg).1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2MemSpan
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem UpperTheory.V.Hi.partUR2Mem_span {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ}
    {V : s.Lev} (ι : Qbar l ≃+* ℂ) (m : ℕ)
    {lam : Wt L l n} {d : ℕ} (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (σ : Submodule ℂ (UA L n → ℂ))
    (F : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ))
    (h : F ∈ Submodule.span ℂ {F : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) | ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ}) :
    ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    intro i ℓ
    have : toForm ι e ((0 : Fin m → (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ)) i) ℓ = 0 := by
      funext g
      simp only [toForm, Pi.zero_apply, map_zero]
    rw [this]; exact σ.zero_mem
  | add x y _ _ hx hy =>
    intro i ℓ
    have : toForm ι e ((x + y) i) ℓ = toForm ι e (x i) ℓ + toForm ι e (y i) ℓ := by
      funext g
      simp only [toForm, Pi.add_apply, map_add (f := _)]
    rw [this]; exact σ.add_mem (hx i ℓ) (hy i ℓ)
  | smul a x _ hx =>
    intro i ℓ
    have : toForm ι e ((a • x) i) ℓ = a • toForm ι e (x i) ℓ := by
      funext g
      simp only [toForm, Pi.smul_apply, map_smul]
    rw [this]; exact σ.smul_mem a (hx i ℓ)

theorem UpperTheory.V.Hi.partUR2Mem :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ : Submodule ℂ (UA L n → ℂ)) (F : Fin m → (hset Q τ₀).X.Fn ℂ d),
    F ∈ YOf Q ι τ₀ e ξ σ ↔ F ∈ (hset Q τ₀).Big ι ξ ∧ ∀ i ℓ, toForm ι e (F i) ℓ ∈ σ := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V Q c ι m τ₀ lam d e ξ σ F
  constructor
  · intro h
    exact ⟨h.1, UpperTheory.V.Hi.partUR2Mem_span ι m e σ F h.2⟩
  · intro h
    exact ⟨h.1, Submodule.subset_span h.2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ProjectiveTransportAlongEquiv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem UpperTheory.V.Hi.projective_transport_along_equiv {Λ₀ Λ V₀ V Q : Type} [CommRing Λ₀] [CommRing Λ] [AddCommGroup V₀] [AddCommGroup V]
    [Module Λ₀ V₀] [Module Λ V] [Group Q] (e : Λ₀ ≃+* Λ) (φ : V ≃+ V₀) (hφ : ∀ a v, φ (e a • v) = a • φ v)
    (ρ' : Representation Λ Q V) (hP : Module.Projective (MonoidAlgebra Λ Q) ρ'.asModule) :
    ∃ ρ'' : Representation Λ₀ Q V₀, (∀ q v, ρ'' q v = φ (ρ' q (φ.symm v))) ∧
      Module.Projective (MonoidAlgebra Λ₀ Q) ρ''.asModule := by
  have hφ' : ∀ (a : Λ₀) v, φ.symm (a • v) = e a • φ.symm v := fun a v => by
    apply φ.injective
    rw [hφ, φ.apply_symm_apply, φ.apply_symm_apply]
  let ρ'' : Representation Λ₀ Q V₀ :=
    { toFun := fun q =>
        { toFun := fun v => φ (ρ' q (φ.symm v))
          map_add' := fun x y => by simp only [map_add (f := _)]
          map_smul' := fun a v => by rw [hφ', map_smul, hφ]; rfl }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp }
  refine ⟨ρ'', fun _ _ => rfl, ?_⟩
  let E : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ₀ Q := MonoidAlgebra.mapRingEquiv Q e.symm
  haveI := RingHomInvPair.of_ringEquiv E
  haveI := RingHomInvPair.of_ringEquiv_symm E
  let ψ : ρ'.asModule ≃+ ρ''.asModule :=
    (ρ'.asModuleEquiv.toAddEquiv.trans φ).trans ρ''.asModuleEquiv.symm.toAddEquiv
  have hψ : ∀ (r : MonoidAlgebra Λ Q) (x : ρ'.asModule), ψ (r • x) = E r • ψ x := by
    intro r x
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [add_smul, map_add (f := _), map_add (f := _), add_smul, ha, hb]
    | single g a =>
      have hE : E (MonoidAlgebra.single g a) = MonoidAlgebra.single g (e.symm a) := by
        simp [E]
      rw [hE, Representation.single_smul, Representation.single_smul]
      change φ (a • ρ' g (ρ'.asModuleEquiv x)) = e.symm a • φ (ρ' g (φ.symm (φ (ρ'.asModuleEquiv x))))
      rw [φ.symm_apply_apply, ← hφ, e.apply_symm_apply]
  let Ψ : ρ'.asModule ≃ₛₗ[(E : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ₀ Q)] ρ''.asModule :=
    { ψ with map_smul' := hψ }
  exact Module.Projective.of_equiv Ψ

theorem UpperTheory.V.Hi.levelUR2ProjTr :
    ∀ (Λ₀ Λ R P G : Type) [CommRing Λ₀] [CommRing Λ] [CommRing R] [Algebra Λ₀ R] [AddCommGroup P] [Module R P] [Module Λ₀ P] [IsScalarTower Λ₀ R P] [Module Λ P] [Group G] (e : Λ₀ ≃+* Λ), (∀ (a : Λ₀) (p : P), a • p = e a • p) → ∀ (ρ : Representation Λ G P) (ρR : Representation R G P), (∀ g p, ρR g p = ρ g p) → ∀ (U U₁ : Subgroup G) [(U₁.subgroupOf U).Normal], (Module.Finite Λ (fixd ρ U₁) → Module.Finite Λ₀ (fixd ρR U₁)) ∧ ∀ ρ' : Representation Λ (U ⧸ U₁.subgroupOf U) (fixd ρ U₁), (∀ (u : U) f, (ρ' (u : U ⧸ U₁.subgroupOf U) f).1 = ρ u f) → Module.Projective (MonoidAlgebra Λ (U ⧸ U₁.subgroupOf U)) ρ'.asModule → ∃ ρ'' : Representation Λ₀ (U ⧸ U₁.subgroupOf U) (fixd ρR U₁), (∀ (u : U) f, (ρ'' (u : U ⧸ U₁.subgroupOf U) f : P) = ρR u f) ∧ Module.Projective (MonoidAlgebra Λ₀ (U ⧸ U₁.subgroupOf U)) ρ''.asModule := by
  intro Λ₀ Λ R P G _ _ _ _ _ _ _ _ _ _ e he ρ ρR hρ U U₁ _
  have hmem : ∀ p : P, p ∈ fixd ρ U₁ ↔ p ∈ fixd ρR U₁ := fun p =>
    forall_congr' fun u => forall_congr' fun _ => by rw [hρ]
  let φ : fixd ρ U₁ ≃+ fixd ρR U₁ :=
    { toFun := fun v => ⟨v.1, (hmem _).1 v.2⟩
      invFun := fun v => ⟨v.1, (hmem _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ (a : Λ₀) v, φ (e a • v) = a • φ v := fun a v => Subtype.ext (he a v.1).symm
  refine ⟨fun hfin => ?_, fun ρ' h' hP => ?_⟩
  · let f : fixd ρ U₁ →ₛₗ[(e.symm : Λ →+* Λ₀)] fixd ρR U₁ :=
      { toFun := φ
        map_add' := φ.map_add
        map_smul' := fun a v => by
          rw [← hφ]
          simp }
    haveI : RingHomSurjective (e.symm : Λ →+* Λ₀) := ⟨e.symm.surjective⟩
    exact Module.Finite.of_surjective f φ.surjective
  · obtain ⟨ρ'', h1, h2⟩ := UpperTheory.V.Hi.projective_transport_along_equiv e φ hφ ρ' hP
    refine ⟨ρ'', fun u f => ?_, h2⟩
    rw [h1, hρ]
    exact h' u (φ.symm f)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WeightVariablesExist
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem weight_variables_exist (l : ℕ) [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ)
    (r : Resid F O n) (d : F.Vl → ℕ) (A : ∀ v, W.LocAb l (F.Gv v) (F.Iv v) (d v)) (Λ : LamObj r) (D : ℕ)
    (hD : ∑ v, d v = D) :
    ∃ (v : Fin (n * D) → F.Vl) (i : Fin (n * D) → Fin n) (γ : ∀ k, F.Gv (v k)) (c : Fin (n * D) → O)
      (e : MvPowerSeries (Empty ⊕ Fin (n * D)) O ≃ₐ[O] Λ.Λ), ∀ k, ∃ hγ : γ k ∈ F.Iv (v k),
      residue O (c k) * (r.psib (v k) (i k) (γ k) : ResidueField O) = 1 ∧
      e (MvPowerSeries.X (.inr k)) = algebraMap O Λ.Λ (c k) * (Λ.κ (v k) (i k) ⟨γ k, hγ⟩ : Λ.Λˣ) - 1 := by
  obtain ⟨e, ψ₀, hψ₀, he⟩ := (W.lam_ex_free l F O n r d A).2 Λ
  have hc : Fintype.card (Σ v : F.Vl, Fin n × Fin (d v)) = n * D := by
    rw [Fintype.card_sigma, ← hD, Finset.mul_sum]
    simp
  let ε : Fin (n * D) ≃ (Σ v : F.Vl, Fin n × Fin (d v)) := (Fintype.equivFinOfCardEq hc).symm
  choose g hgI hg using fun (v : F.Vl) (j : Fin (d v)) => ((A v).inertia (Pi.single j 1, 0)).2 rfl
  let ε' : Empty ⊕ Fin (n * D) ≃ (Σ v : F.Vl, Fin n × Fin (d v)) :=
    (@Equiv.emptySum Empty (Fin (n * D)) ⟨Empty.elim⟩).trans ε
  refine ⟨fun k => (ε k).1, fun k => (ε k).2.1, fun k => g (ε k).1 (ε k).2.2,
    fun k => ((ψ₀ (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2))⁻¹ : Oˣ),
    (MvPowerSeries.renameEquiv O ε').trans e, fun k => ⟨hgI _ _, ?_, ?_⟩⟩
  · have h1 := (hψ₀ (ε k).1 (ε k).2.1).red (g (ε k).1 (ε k).2.2)
    have h2 : ∀ x : O, Alg.res O O x = residue O x := fun x => (Alg.res O O).commutes x
    rw [h2] at h1
    show residue O _ * ((r.psib (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2) : (ResidueField O)ˣ) : ResidueField O) = 1
    rw [← h1, ← map_mul, Units.inv_mul, map_one]
  · have h1 := he (ε k).1 (ε k).2.1 (ε k).2.2 ⟨g (ε k).1 (ε k).2.2, hgI _ _⟩ (hg _ _)
    have h2 : MvPowerSeries.renameEquiv O ε' (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (ε k) := by
      exact MvPowerSeries.rename_X _ _
    show e (MvPowerSeries.renameEquiv O ε' (MvPowerSeries.X (.inr k))) =
      algebraMap O Λ.Λ ((ψ₀ (ε k).1 (ε k).2.1 (g (ε k).1 (ε k).2.2))⁻¹ : Oˣ) *
        ((Λ.κ (ε k).1 (ε k).2.1 ⟨g (ε k).1 (ε k).2.2, hgI _ _⟩ : Λ.Λˣ) : Λ.Λ) - 1
    rw [h1, h2, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul, add_sub_cancel_left]

theorem UpperTheory.V.Hi.levelUR2WtVars :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (c : Coef l) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r), Pa.LocCFT s → ∃ (wt : Pa.WtVars (Pa.locOf r) c.O n (n * Module.finrank ℚ (Lp L))) (e : Pa.abelian₂ c.O Empty (n * Module.finrank ℚ (Lp L)) ≃ₐ[c.O] Λ.Λ), ∀ k, ∃ hγ : wt.γ k ∈ V.frame.Iv (wt.v k), residue c.O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField c.O) = 1 ∧ e (MvPowerSeries.X (.inr k)) = algebraMap c.O Λ.Λ (wt.c k) * (Λ.κ (wt.v k) (wt.i k) ⟨wt.γ k, hγ⟩ : Λ.Λˣ) - 1 := by
  intro l hl L Ω _ _ _ _ _ _ s n V c r _ Λ h
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField ℤ_[l]) l :=
    charP_of_injective_ringHom (f := (PadicInt.residueField (p := l)).symm.toRingHom)
      (PadicInt.residueField (p := l)).symm.injective l
  haveI : CharP (ResidueField c.O) l :=
    charP_of_injective_ringHom (algebraMap (ResidueField ℤ_[l]) (ResidueField c.O)).injective l
  obtain ⟨d₀, hd, hA⟩ := h
  let d : V.frame.Vl → ℕ := d₀
  have hsum : ∑ v : V.frame.Vl, d v = Module.finrank ℚ (Lp L) :=
    (finsum_eq_sum_of_fintype (α := V.frame.Vl) d).symm.trans hd
  obtain ⟨v, i, γ, cc, e, H⟩ := weight_variables_exist l V.frame c.O n r d (fun v => (hA v).some) Λ _ hsum
  exact ⟨⟨v, i, γ, cc⟩, e, H⟩
end

