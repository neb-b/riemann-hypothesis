module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.ThetaFin
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem thetaFin_mono {C : Subgroup 𝓀[k]ˣ} {x : kˣ} (h : x ∈ unitsC k C) : x ∈ unitsC k ⊤ := by
  obtain ⟨d, -, rfl⟩ := h
  exact ⟨d, trivial, rfl⟩

private theorem thetaFin_one {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (ρ : Representation A (GL (Fin n) k) M) (C : Subgroup 𝓀[k]ˣ) (θ) (hθ : IsTheta ρ C θ) (t : Fin n → kˣ)
    (ht : ∀ i, t i ∈ unitsC k C) : θ t = 1 := by
  have hd : Dom t := fun a b _ => le_of_eq (by
    rw [((memIwC k n ⊤).2.2.2 _).1 (thetaFin_mono (ht a)), ((memIwC k n ⊤).2.2.2 _).1 (thetaFin_mono (ht b))])
  have hm : diagT k (Fin n) t ∈ iwC k n C := Subgroup.mem_sup_right ⟨_, fun i' _ => ht i', rfl⟩
  have hn : diagT k (Fin n) t ∈ Subgroup.normalizer (iwC k n C : Set (GL (Fin n) k)) := Subgroup.le_normalizer hm
  apply Units.ext
  rw [hθ t hd]
  ext v
  rw [(hkNorm A _ M ρ _ _ (heckePairIwC k n C).1 hn).1 v]
  exact v.2 _ hm

end Loc

theorem UpperTheory.V.Th.thetaFin :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (C C' : Subgroup 𝓀[k]ˣ) (θ), IsTheta ρ C θ → ∀ δ : kˣ, IsGenMod k C' δ → ∀ i : Fin n, ∃ m : ℕ, 0 < m ∧ θ (Pi.mulSingle i δ) ^ m = 1 := by
  intro k _ _ _ _ n A M _ _ _ ρ C C' θ hθ δ hδ i
  obtain ⟨d, rfl, -⟩ := hδ
  refine ⟨Nat.card 𝓀[k]ˣ, Nat.card_pos, ?_⟩
  rw [← map_pow]
  refine thetaFin_one ρ C θ hθ _ fun j => ?_
  rw [Pi.pow_apply]
  by_cases e : j = i
  · subst e
    rw [Pi.mulSingle_eq_same]
    refine ⟨d ^ Nat.card 𝓀[k]ˣ, ?_, map_pow _ _ _⟩
    show Units.map (residue 𝒪[k]).toMonoidHom _ ∈ C
    rw [map_pow, pow_card_eq_one']
    exact one_mem _
  · rw [Pi.mulSingle_eq_of_ne e, one_pow]
    exact one_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.Transport
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ot_inv {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (e : G.Hom G') (hi : Function.Injective e.p) :
    ∃ k : G'.Hom G, ∀ g, k.p (e.p g) = g := by
  let E : G.Γ ≃* G'.Γ := MulEquiv.ofBijective e.p ⟨hi, e.surj⟩
  have hE : ∀ g, E.symm (e.p g) = g := fun g => E.symm_apply_apply g
  have hc : Continuous E.symm := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := E.toEquiv) e.cont
  refine ⟨⟨E.symm.toMonoidHom, hc, E.symm.surjective, fun g => ?_, ?_, fun g => ?_, fun v g => ?_, fun v g => ?_⟩, hE⟩
  · obtain ⟨g, rfl⟩ := e.surj g
    exact (congrArg G.η (hE g)).trans (e.η g).symm
  · rw [← e.c]; exact hE _
  · obtain ⟨g, rfl⟩ := e.surj g
    exact (congrArg G.ε (hE g)).trans (e.ε g).symm
  · rw [← e.φ]; exact hE _
  · rw [← e.φu]; exact hE _

private theorem ot_tr_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (y : MonoidAlgebra A H) : (D.comap φ).tr y = D.tr (MonoidAlgebra.mapDomainRingHom A φ y) := by
  have : (D.comap φ).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A φ y) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g r => simp
  unfold GDet.tr GDet.lam
  rw [this]

private theorem ot_comap_comap {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [Group K] (D : GDet n A G)
    (φ : H →* G) (ψ : K →* H) : (D.comap φ).comap ψ = D.comap (φ.comp ψ) := by
  refine GDet.ext fun B _ _ x => ?_
  change D.D B (MonoidAlgebra.mapDomainRingHom B φ (MonoidAlgebra.mapDomainRingHom B ψ x)) =
    D.D B (MonoidAlgebra.mapDomainRingHom B (φ.comp ψ) x)
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp

private theorem ot_single {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g : H) (a : A) :
    MonoidAlgebra.mapDomainRingHom A φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (φ g) a := by simp

private theorem mapDomain_partial_charpoly_element {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G) (g t : H) (u : Fin n → A)
    (i : Fin n) (y : A) (E : ℕ) : MonoidAlgebra.mapDomainRingHom A φ (twoPowerModulus E g t u i y) = twoPowerModulus E (φ g) (φ t) u i y := by
  unfold twoPowerModulus
  rw [map_mul, map_pow, map_list_prod, List.map_ofFn, map_sub, map_sub, ot_single, ot_single, map_one, map_one]
  congr 4
  funext k
  rw [Function.comp_apply]
  split_ifs
  · exact map_one _
  · rw [map_sub, ot_single, ot_single, map_one]

private theorem ot_pair {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (k : G'.Hom G) {O : Type} [CommRing O]
    [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid G.frame O n} {r' : Resid G'.frame O n} (hc : Glob.Compat k r' r)
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) :
    ∃ p' : Pair r' R, p'.D = p.D.comap k.p₀ ∧ p'.ψ = p.ψ := by
  let f : FHom G'.frame G.frame :=
    ⟨k.p, k.cont, k.η, k.c, k.ε, id, fun _ => MonoidHom.id _, fun _ => continuous_id, fun v g => (k.φ v g).symm,
      fun _ _ hg => hg⟩
  have hf : f.Compat r' r := by
    refine ⟨hc.1, fun v i => by rw [hc.2.1]; rfl, fun v i g hg => by rw [hc.2.2]; rfl, fun u g hg => Or.inr ⟨u, ?_, ?_⟩⟩
    · obtain ⟨x, hx, rfl⟩ := hg.1
      exact ⟨x, hx, Subtype.ext (k.φu u x).symm⟩
    · refine Subgroup.mem_iInf.2 fun i => ?_
      have := Subgroup.mem_iInf.1 hg.2 i
      rw [hc.1 i] at this
      exact this
  obtain ⟨p', h1, h2⟩ := exists_determinantPair_pullback l G'.frame G.frame f O n r' r hf (fun h0 => (p.isEmpty_of_zero h0).1) R p
  exact ⟨p', h1, funext fun v => funext fun i => h2 v i⟩

theorem UpperTheory.V.Th.opTransportX :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (G G' : Glob l L) (e : G.Hom G') (h : G.Hom G0) (h' : G'.Hom G0) (q N : ℕ) (A : OpMod b h q N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ), Function.Injective e.p → (∀ g, h'.p (e.p g) = h.p g) → OpRelX A Nq ph ta ex → ∃ A' : OpMod b h' q N, OpRelX A' Nq (fun j => e.p₀ (ph j)) (fun j => e.p₀ (ta j)) ex := by
  intro l _ L G0 O _ _ _ _ _ n r B _ _ _ u J D b G G' e h h' q N A Nq ph ta ex hi hh hA
  obtain ⟨k, hk⟩ := ot_inv e hi
  have hk0 : ∀ g, k.p₀ (e.p₀ g) = g := fun g => Subtype.ext (hk g)
  have hh0 : ∀ g, h'.p₀ (e.p₀ g) = h.p₀ g := fun g => Subtype.ext (hh g)
  have hcomp : h.p₀.comp k.p₀ = h'.p₀ := by
    ext g : 2
    obtain ⟨g, hg⟩ := g
    obtain ⟨g, rfl⟩ := e.surj g
    change h.p (k.p (e.p g)) = h'.p (e.p g)
    rw [hk, hh]
  obtain ⟨r', hr'⟩ := UpperTheory.V.Pa.Core.resPull l L G' G k n O A.rN
  obtain ⟨p', hD, hψ⟩ := ot_pair k hr' A.p
  have hcp : Glob.Compat h' r' r := by
    refine ⟨fun i => ?_, hr'.2.1.trans A.compat.2.1, hr'.2.2.trans A.compat.2.2⟩
    rw [hr'.1 i, A.compat.1 i, ← hcomp]
    rfl
  have hβ : p'.Maps A.β.toRingHom (u.D.comap h'.p₀) u.ψ := by
    refine ⟨?_, fun v i => by rw [hψ]; exact A.β_pair.2 v i⟩
    rw [hD, ← hcomp, ← ot_comap_comap, ← A.β_pair.1]
    rfl
  have hm : p'.D.map (MvPolynomial.C : A.R →+* PUY A.R q n) =
      (A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).comap k.p₀ := by
    rw [hD]; rfl
  refine ⟨{ rN := r', compat := hcp, R := A.R, p := p', segmentWeightExponent := fun j => by rw [hψ]; exact A.segmentWeightExponent j,
            β := A.β, β_pair := hβ, M1 := A.M1, fin1 := A.fin1, Mw := A.Mw, act1 := A.act1, actw := A.actw,
            a := A.a, le_a := A.le_a, ρ := A.ρ, ρ_gen := A.ρ_gen, proj := A.proj, tr := A.tr, tr_surj := A.tr_surj,
            tr_ker := A.tr_ker, tr_u := A.tr_u }, ?_, fun j i => ?_⟩
  · have := hA.two
    simp only [hh0]
    exact this
  · have := hA.rel2 j i
    change A.act1 (fEl Nq (uV A.R) ^ ex * (p'.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr
      (twoPowerModulus ex (e.p₀ (ph j)) (e.p₀ (ta j)) (uV A.R j) i (yV A.R j i))) = 0
    rw [hm, ot_tr_comap, mapDomain_partial_charpoly_element, hk0, hk0]
    exact this
end

