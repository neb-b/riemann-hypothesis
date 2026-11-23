module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0271
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacquetBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem hasFiniteLength_twist_iff (ρ : Representation F G V) (χ : G →* Fˣ) :
    HasFiniteLength (twist ρ χ) ↔ HasFiniteLength ρ := by
  let φ : Subrepresentation (twist ρ χ) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have h1 := S.apply_mem_toSubmodule g hv
        rw [twist_apply] at h1
        have h2 := S.toSubmodule.smul_mem ((χ g : F)⁻¹) h1
        rwa [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h2⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        rw [twist_apply]
        exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  rw [hasFiniteLength_iff_wellFounded, hasFiniteLength_iff_wellFounded]
  exact and_congr ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedGT,
    fun _ => φ.toOrderEmbedding.wellFoundedGT⟩ ⟨fun _ => φ.symm.toOrderEmbedding.wellFoundedLT,
    fun _ => φ.toOrderEmbedding.wellFoundedLT⟩

theorem hasFiniteLength_of_surjective {ρ : Representation F G V} {σ : Representation F G W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (h : HasFiniteLength ρ) :
    HasFiniteLength σ :=
  IsFiniteLength.of_surjective h
    (f := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f) hf

end General

section Blocks

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem mem_unipRad_iff_blk {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ g ∈ parab R e ∧
      ∀ i j, blk e i = blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  refine and_congr_right fun _ => ⟨fun h i j hij => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    subst hij
    rw [h a x y]
    simp [Matrix.one_apply, e.injective.eq_iff]
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply, e.injective.eq_iff]


omit [LinearOrder α] in
theorem leviEmb_apply_of_blk_ne [DecidableEq α] (e : (Σ a, m a) ≃ n) (g : Levi R m) {i j : n}
    (h : blk e i ≠ blk e j) : (leviEmb R e g : Matrix n n R) i j = 0 := by
  letI : DecidableEq α := Classical.typeDecidableEq α
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  have hab : a ≠ b := by simpa using h
  simpa [leviEmb, Matrix.reindex_apply] using
    (Matrix.blockDiagonal'_apply_ne (fun c => (g c : Matrix (m c) (m c) R)) x y hab)

theorem leviEmb_leviProj_of_blk (e : (Σ a, m a) ≃ n) (p : parab R e)
    (h : ∀ i j, blk e i ≠ blk e j → ((p : GL n R) : Matrix n n R) i j = 0) :
    leviEmb R e (leviProj R e p) = p := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨⟨a, x⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective j
  by_cases hab : a = b
  · subst hab
    simp [leviEmb, Matrix.reindex_apply, leviProj_apply]
  · have hblk : blk e (e ⟨a, x⟩) ≠ blk e (e ⟨b, y⟩) := by simpa using hab
    rw [leviEmb_apply_of_blk_ne e _ hblk, h _ _ hblk]

theorem leviProj_eq_of_coe_eq (e : (Σ a, m a) ≃ n) (p : parab R e) (g : Levi R m)
    (h : (p : GL n R) = leviEmb R e g) : leviProj R e p = g := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, h]
  simp [leviEmb, Matrix.reindex_apply]

end Blocks

section Transport

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_of_transport (e : (Σ a, m a) ≃ n) (e' : (Σ b, m' b) ≃ n')
    (Φ : GL n' k →* GL n k) (Ψ : Levi k m' →* Levi k m) (hΨ : Function.Surjective Ψ)
    (hU : ∀ u ∈ unipRad k e', Φ u ∈ unipRad k e)
    (hL : ∀ g, Φ (leviEmb k e' g) = leviEmb k e (Ψ g)) (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e' (π.comp Φ))) : HasFiniteLength (jacU e π) := by
  have hle : twKer (π.comp Φ) (unipRad k e') 1 ≤ twKer π (unipRad k e) 1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    exact Submodule.subset_span ⟨⟨Φ u, hU u u.2⟩, v, by simp⟩
  let f : (jacU e' (π.comp Φ)).IntertwiningMap ((jacU e π).comp Ψ) :=
    ⟨(twKer (π.comp Φ) (unipRad k e') 1).mapQ (twKer π (unipRad k e) 1) LinearMap.id hle,
      fun g => by
        ext v
        show Submodule.Quotient.mk (π (Φ (leviEmb k e' g)) v) =
          (Submodule.Quotient.mk (π (leviEmb k e (Ψ g)) v) : Jacquet π (unipRad k e))
        rw [hL]⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  rw [← hasFiniteLength_comp_iff _ Ψ hΨ]
  exact hasFiniteLength_of_surjective f hf h

end Transport

section Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β n n' : Type} {m : α → Type} {m' : β → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [LinearOrder β]
  [∀ b, Fintype (m' b)] [∀ b, DecidableEq (m' b)] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem hasFiniteLength_jacU_reindex (e : (Σ b, m' b) ≃ n') (ψ : n' ≃ n)
    (π : Representation ℂ (GL n k) V)
    (h : HasFiniteLength (jacU e (π.comp
      (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom))) :
    HasFiniteLength (jacU (e.trans ψ) π) := by
  set Φ : GL n' k →* GL n k := (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom
  have hΦ : ∀ (g : GL n' k) (i j : n), (Φ g : Matrix n n k) i j = (g : Matrix n' n' k) (ψ.symm i) (ψ.symm j) :=
    fun _ _ _ => rfl
  refine hasFiniteLength_jacU_of_transport (e.trans ψ) e Φ (MonoidHom.id _) Function.surjective_id
    (fun u hu => ?_) (fun g => ?_) π h
  · rw [mem_unipRad] at hu ⊢
    refine ⟨mem_parab_iff.2 fun a b x y hab => ?_, fun a x y => ?_⟩
    · rw [hΦ]
      simpa using mem_parab_iff.1 hu.1 a b x y hab
    · rw [hΦ]
      simpa using hu.2 a x y
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [hΦ]
    rfl

end Stages

end GlobalTheory.JacquetBlocks

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantSubspaceMobiusInverseCharpolyPrimaryEq
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL.Primary

theorem finrank_comap_of_surjective {F V U : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup U] [Module F U] (π : V →ₗ[F] U) (hπ : Function.Surjective π)
    (A : Submodule F U) :
    Module.finrank F (A.comap π) = Module.finrank F (LinearMap.ker π) + Module.finrank F A := by
  have h := LinearMap.finrank_range_add_finrank_ker (π.domRestrict (A.comap π))
  rw [LinearMap.range_domRestrict, Submodule.map_comap_eq_of_surjective hπ, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_comap π)).finrank_eq] at h
  omega

theorem additive_pow {F : Type} [Field F] {s : F[X] → ℂ} (hs : IsAdditive s) {f : F[X]} (hf : f.Monic)
    (j : ℕ) : s (f ^ j) = j * s f := by
  induction j with
  | zero =>
    have := hs 1 1 monic_one monic_one
    rw [mul_one] at this
    simpa using this
  | succ j ih => rw [pow_succ, hs _ _ (hf.pow j) hf, ih]; push_cast; ring

theorem additive_restrict {F V : Type} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {s : F[X] → ℂ} (hs : IsAdditive s) {g : Module.End F V} {f : F[X]} {m : ℕ} (hf : f.Monic)
    (hi : Irreducible f) (hc : LinearMap.charpoly g = f ^ m) (A : Submodule F V) (hA : ∀ x ∈ A, g x ∈ A) :
    (f.natDegree : ℂ) * s (LinearMap.charpoly (g.restrict hA)) = (Module.finrank F A : ℂ) * s f := by
  have h1 : LinearMap.charpoly (g.restrict hA) ∣ f ^ m :=
    hc ▸ ⟨_, charpoly_eq_restrict_mul_mapQ A g hA⟩
  obtain ⟨j, -, hj⟩ := (dvd_prime_pow hi.prime m).1 h1
  have h2 : LinearMap.charpoly (g.restrict hA) = f ^ j :=
    eq_of_monic_of_associated (LinearMap.charpoly_monic _) (hf.pow j) hj
  have h3 := LinearMap.charpoly_natDegree (g.restrict hA)
  rw [h2, hf.natDegree_pow] at h3
  rw [h2, additive_pow hs hf, ← h3]
  push_cast; ring

theorem eq_top_of_nilpotent {F V : Type} [Field F] [AddCommGroup V] [Module F V] (N : Module.End F V)
    {m : ℕ} (hN : N ^ m = 0) (W : Submodule F V) (hW : ∀ x ∈ W, N x ∈ W)
    (h : ∀ v, ∃ w ∈ W, ∃ u, v = w + N u) : W = ⊤ := by
  have hp : ∀ (j : ℕ), ∀ x ∈ W, (N ^ j) x ∈ W := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih => intro x hx; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hW x hx)
  have key : ∀ (j : ℕ) (v : V), ∃ w ∈ W, ∃ u, v = w + (N ^ j) u := by
    intro j
    induction j with
    | zero => intro v; exact ⟨0, W.zero_mem, v, by simp⟩
    | succ j ih =>
      intro v
      obtain ⟨w, hw, u, rfl⟩ := ih v
      obtain ⟨w', hw', u', rfl⟩ := h u
      refine ⟨w + (N ^ j) w', W.add_mem hw (hp j w' hw'), u', ?_⟩
      rw [map_add (f := _), pow_succ, Module.End.mul_apply, add_assoc]
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨w, hw, u, rfl⟩ := key m v
  simpa [hN] using hw

theorem aeval_mem {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V)
    (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : F[X]) : ∀ x ∈ W, aeval g p x ∈ W := by
  first
  | exact @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
  | exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem
  | (apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialEvaluationMembership.aeval_apply_mem ..)

theorem mem_image_of_mem_span {F V : Type} [Field F] [AddCommGroup V] [Module F V] (g : Module.End F V)
    (f : F[X]) {t : ℕ} (π : V →ₗ[F] (Fin t → AdjoinRoot f)) (hπ : ∀ v, π (g v) = AdjoinRoot.root f • π v)
    (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (y : Fin t → AdjoinRoot f)
    (hy : y ∈ Submodule.span (AdjoinRoot f) (π '' W)) : ∃ w ∈ W, π w = y := by
  have key : ∀ (p : F[X]) (v : V), π (aeval g p v) = AdjoinRoot.mk f p • π v := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      intro v
      rw [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, algebraMap_smul]
      simp
    | add p q hp hq => intro v; simp [hp, hq, add_smul]
    | monomial n a h =>
      intro v
      rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, aeval_X, h, hπ, map_mul (AdjoinRoot.mk f) _ X,
        AdjoinRoot.mk_X, smul_smul]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, W.zero_mem, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    exact ⟨w + w', W.add_mem hw hw', map_add _ _ _⟩
  | smul k x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective k
    exact ⟨_, aeval_mem g W hW p w hw, key p w⟩

end GlobalTheory.CuspGL.Primary

namespace GlobalTheory.CuspGL


open Primary in
theorem psi_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ (g : Module.End F V) (f : F[X]) (m t : ℕ), f.Monic → Irreducible f → 0 < m → LinearMap.charpoly g = f ^ m → Module.finrank F (LinearMap.ker (aeval g f)) = f.natDegree * t → psi s V g = s f * ∏ i ∈ Finset.Ico 1 t, (1 - (Nat.card F : ℂ) ^ (f.natDegree * i)) := by
  intro F _ _ V _ _ _ s hs g f m t hf hi hm hc ht
  classical
  haveI : Fact (Irreducible f) := ⟨hi⟩
  have he : 0 < f.natDegree := hi.natDegree_pos
  have he' : (f.natDegree : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  obtain ⟨t', π, hsurj, hπ, hker, ht'⟩ := _root_.GlobalTheory.exists_surjective_pi_adjoinRoot_ker_eq_range F V g f
  obtain rfl : t' = t := Nat.eq_of_mul_eq_mul_left he (ht'.symm.trans ht)
  haveI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hi.ne_zero).finite
  have hK : Module.finrank F (AdjoinRoot f) = f.natDegree := (AdjoinRoot.powerBasis hi.ne_zero).finrank
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite F
  have hcard : Nat.card (AdjoinRoot f) = Nat.card F ^ f.natDegree := by
    rw [← hK]; exact Module.natCard_eq_pow_finrank
  have hN : (aeval g f) ^ m = 0 := by rw [← map_pow, ← hc, LinearMap.aeval_self_charpoly]
  have nak : ∀ W : Submodule F V, (∀ x ∈ W, g x ∈ W) →
      Submodule.span (AdjoinRoot f) (π '' W) = ⊤ → W = ⊤ := by
    intro W hW h
    refine eq_top_of_nilpotent (aeval g f) hN W (aeval_mem g W hW f) fun v => ?_
    obtain ⟨w, hw, hw'⟩ := mem_image_of_mem_span g f π hπ W hW (π v) (h ▸ Submodule.mem_top)
    have : v - w ∈ LinearMap.ker π := by rw [LinearMap.mem_ker, map_sub, hw', sub_self]
    rw [hker] at this
    obtain ⟨u, hu⟩ := this
    exact ⟨w, hw, u, by rw [hu]; abel⟩
  have htpos : 0 < t' := by
    rcases Nat.eq_zero_or_pos t' with rfl | h
    · exfalso
      have h1 := nak ⊥ (by simp) (Subsingleton.elim _ _)
      have h2 := LinearMap.charpoly_natDegree g
      rw [hc, hf.natDegree_pow, ← finrank_top, ← h1, finrank_bot] at h2
      exact (Nat.mul_pos hm he).ne' h2
    · exact h
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Submodule F V) := Finite.of_injective _ SetLike.coe_injective
  haveI : Finite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f)) :=
    Finite.of_injective _ SetLike.coe_injective
  letI := Fintype.ofFinite (Submodule F V)
  letI := Fintype.ofFinite (Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f))
  let P : Submodule F V → ℂ := fun W => if h : ∀ x ∈ W, g x ∈ W then psi s W (g.restrict h) else 0
  let Φ : Submodule F V → Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f) :=
    fun W => Submodule.span (AdjoinRoot f) (π '' W)
  let G : Submodule (AdjoinRoot f) (Fin t' → AdjoinRoot f) → ℂ :=
    fun B => ∑ W ∈ Finset.univ.filter (fun W => Φ W = B), P W
  have hrk : Module.finrank (AdjoinRoot f) (Fin t' → AdjoinRoot f) = t' := by simp
  have main := GlobalTheory.T.mobiusInversion_affine_finrank_subspaces (AdjoinRoot f) (Fin t' → AdjoinRoot f) G
    ((Module.finrank F (LinearMap.ker π) : ℂ) * s f / f.natDegree) (s f) (by rw [hrk]; exact htpos) (by
      intro A
      have hA : ∀ x ∈ (A.restrictScalars F).comap π, g x ∈ (A.restrictScalars F).comap π := by
        intro x hx
        rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at hx ⊢
        rw [hπ]; exact A.smul_mem _ hx
      have hle : ∀ W, Φ W ≤ A ↔ W ≤ (A.restrictScalars F).comap π := fun W => by
        rw [Submodule.span_le, Set.image_subset_iff]; rfl
      have h1 := finsum_psi_le F V s _ g hA
      have h2 := additive_restrict hs hf hi hc _ hA
      rw [finrank_comap_of_surjective π hsurj] at h2
      have h3 : Module.finrank F (A.restrictScalars F) = f.natDegree * Module.finrank (AdjoinRoot f) A := by
        rw [← hK, Module.finrank_mul_finrank]; rfl
      rw [h3] at h2
      have h4 : ∑ᶠ B : {B // B ≤ A}, G B.1 =
          ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W := by
        rw [finsum_eq_sum_of_fintype,
          ← Finset.sum_subtype (Finset.univ.filter (fun B => B ≤ A)) (by simp) G,
          Finset.sum_fiberwise_eq_sum_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext W; simp [hle]
      have h5 : ∑ᶠ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W},
          psi s W.1 (g.restrict W.2.2) =
          ∑ W ∈ Finset.univ.filter (fun W => W ≤ (A.restrictScalars F).comap π), P W := by
        have : ∀ W : {W : Submodule F V // W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W},
          psi s W.1 (g.restrict W.2.2) = P W.1 := fun W => by simp only [P]; rw [dite_eq_left W.2.2]
        rw [finsum_congr this, finsum_eq_sum_of_fintype,
          ← Finset.sum_subtype (Finset.univ.filter
            (fun W => W ≤ (A.restrictScalars F).comap π ∧ ∀ x ∈ W, g x ∈ W)) (by simp) P]
        refine Finset.sum_subset (fun W => by simp; tauto) fun W hW hW' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW hW'
        exact dif_neg fun h => hW' ⟨hW, h⟩
      rw [h4, ← h5, h1]
      push_cast at h2
      field_simp
      linear_combination h2)
  have hG : G ⊤ = psi s V g := by
    have htop : ∀ x ∈ (⊤ : Submodule F V), g x ∈ (⊤ : Submodule F V) := fun _ _ => trivial
    have h1 : G ⊤ = P ⊤ := by
      refine Finset.sum_eq_single_of_mem ⊤ ?_ fun W hW hW' => ?_
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Φ]
        rw [Submodule.top_coe, Set.image_univ, hsurj.range_eq, Submodule.span_univ]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
        exact dif_neg fun h => hW' (nak W h hW)
    rw [h1]
    simp only [P]
    rw [dite_eq_left htop, ← psi_conj F s _ _ Submodule.topEquiv]
    congr 1
  rw [← hG, main, hrk, hcard]
  simp only [Nat.cast_pow, ← pow_mul]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainMonicRootsOfIsIndEtaleLocalStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O], IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  first | (exact @GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (exact GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (intros; apply GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFamConstLevelOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isFam_const_of_isMF (ι : Type) (act : ι → SL(2, ℤ) → ι) (k : ℤ) (F : ℍ → ℂ)
    (h : IsMF k F) : IsFam act k fun _ => F := by
  intro i γ
  funext τ
  have hne : UpperHalfPlane.denom γ τ ^ k ≠ 0 := zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)
  rw [ModularForm.SL_slash_apply]
  beta_reduce
  rw [h.smul_eq γ τ, zpow_neg, mul_right_comm, mul_inv_cancel₀ hne, one_mul]

theorem isFam_const_E4 (ι : Type) (act : ι → SL(2, ℤ) → ι) : IsFam act 4 (fun _ => ⇑E₄) :=
  isFam_const_of_isMF ι act 4 _ ⟨E₄, fun _ => rfl⟩

theorem isFam_const_E6 (ι : Type) (act : ι → SL(2, ℤ) → ι) : IsFam act 6 (fun _ => ⇑E₆) :=
  isFam_const_of_isMF ι act 6 _ ⟨E₆, fun _ => rfl⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCover
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue Opposite

theorem GlobalTheory.HilbGlue.isSheaf_hilbFunctor {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (hilbFunctor z r) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique (GlobalTheory.T.hilbert_point_glue_open_cover z r Y 𝒰 x fun i j R b c h => hx i j R b c h)
    fun y y' h h' => _root_.GlobalTheory.HilbGlue.HPt.ext_openCover z r Y 𝒰 y y' fun i => (h i).trans (h' i).symm

theorem GlobalTheory.HilbGlue.isHilbRep_of_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z →
    LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) →
    IsHilbRep z r := by
  intro S Z z _ _ _ r hS
  have hloc : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧ ∃ (T : Scheme.{0}) (y : HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, HPt.map c y = x := fun s => by
    obtain ⟨W, hs, hW⟩ := hS s
    exact ⟨W, hs, _root_.GlobalTheory.HilbGlue.isHilbRep_restrict_local z r W hW⟩
  have hloc' := hloc
  choose W hsW T y π _ hπ huniq using hloc
  have hrep : (hilbFunctor z r).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover (hilbFunctor z r) (GlobalTheory.HilbGlue.isSheaf_hilbFunctor z r) (hilbProj z r) W
      (eq_top_iff.2 fun s _ => TopologicalSpace.Opens.mem_iSup.2 ⟨s, hsW s⟩) T y π hπ huniq
  obtain ⟨H, u, hu⟩ : ∃ (H : Scheme.{0}) (u : HPt z r H), ∀ (T : Scheme.{0}) (x : HPt z r T),
      ∃! c : T ⟶ H, HPt.map c u = x := by
    obtain ⟨H, ⟨e⟩⟩ := hrep.has_representation
    have h : ∀ {T : Scheme.{0}} (c : T ⟶ H), HPt.map c (e.homEquiv (𝟙 H)) = e.homEquiv c :=
      fun c => (e.homEquiv_eq c).symm
    exact ⟨H, e.homEquiv (𝟙 H), fun T x => ⟨e.homEquiv.symm x, (h _).trans (e.homEquiv.apply_symm_apply x),
      fun c hc => e.homEquiv.eq_symm_apply.2 ((h c).symm.trans hc)⟩⟩
  have hprop : IsProper u.1 := GlobalTheory.T.isProper_of_represents_hilbertFunctor_of_local z r H u hu hloc'
  obtain ⟨h, I⟩ := u
  refine ⟨H, h, I.1.subscheme, I.1.subschemeι, hprop, inferInstance, I.2.1, I.2.2.1, I.2.2.2, ?_⟩
  intro T g V v _ h1 h2 h3
  have hv' : IsFinFlatRk (v ≫ pullback.snd z g) r := ⟨h1, h2, h3⟩
  obtain ⟨c, hc, hcu⟩ := hu T (mkPt g v hv')
  have key : ∀ (f : T ⟶ H) (hf : f ≫ h = g), HPt.map f ⟨h, I⟩ = mkPt g v hv' ↔
      ∃ w : V ⟶ I.1.subscheme, IsPullback v w (bc z f h g hf) I.1.subschemeι := by
    intro f hf
    rw [mkPt, HPt.map_eq_mk_iff f ⟨h, I⟩ hf]
    exact GlobalTheory.HilbGlue.comap_eq_ker_iff (bc z f h g hf) I.1 v
  have hcg : c ≫ h = g := congrArg Sigma.fst hc
  exact ⟨c, ⟨hcg, (key c hcg).1 hc⟩, fun f ⟨hf, hw⟩ => hcu f ((key f hf).2 hw)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoQuotientPowFreeOverRegularLocalRingStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modDepthGE_two_quotient_pow_free_over_regularLocalRing : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] [Nontrivial B] (k : ℕ), 1 ≤ k → ReciprocityTheory.CA.ModDepthGE R (B ⧸ (Ideal.span {f}).map (algebraMap R B) ^ k) 2 := by
  first | (exact @GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (exact GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing) | (intros; apply GlobalTheory.modDepthGE_two_quotient_pow_of_free_of_isRegularLocalRing  <;> assumption)
end

