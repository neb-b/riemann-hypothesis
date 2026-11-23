module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharpolyMemVirtualCharactersGLStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterShintaniPsiLift
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_eq_of_exists {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (h : ∃ γ, IsNorm s δ γ) (f : GL (Fin n) F → ℂ) :
    shLift s f δ = f h.choose := by
  unfold shLift
  rw [dite_eq_left h]

theorem exists_virt_psi_lift : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ k n : ℕ, ∃ X ∈ Virt ℂ ℂ (GHat F F' n), (∀ g, X (inl g) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n g) ∧ ∀ δ, X (inl δ * inr s) = shLift s (psiG (rootSum (pullθ ι θ) k) n) δ := by
  intro F F' _ _ _ _ s hp hs ι θ hθ k
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  have hcard : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := by
    exact IsGalois.card_aut_eq_finrank F F'
  have hgen : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
    haveI : Fact (Module.finrank F F').Prime := ⟨hp⟩
    rw [zpowers_eq_top_of_prime_card hcard hs]; intro t; trivial
  have hlift1 : ∀ (m : ℕ) (δ : GL (Fin m) F'), shLift s (fun _ : GL (Fin m) F => (1 : ℂ)) δ = 1 := by
    intro m δ
    exact shLift_eq_of_exists s δ (GlobalTheory.T.every_element_is_norm F F' s hgen m δ) _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hZ : ∀ a : Fin n, ∃ Z ∈ Virt ℂ ℂ (GHat F F' n),
      (∀ δ, Z (inl δ) = hc a (n - a)
        (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n δ) ∧
      ∀ δ, Z (inl δ * inr s) = hcTw (s : F' →+* F') a (n - a)
        (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ => 1) n δ := by
    intro a
    obtain ⟨Xa, hXa, h1, h2⟩ := ih a a.2
    obtain ⟨Z, hZv, hZe⟩ := GlobalTheory.T.exists_virtualCharacter_twistedHarishChandraInductionGL F F' a (n - a) n (by omega) Xa hXa
    refine ⟨Z, hZv, fun δ => ?_, fun δ => ?_⟩
    · have e := hZe 1 δ
      simp only [map_one, mul_one] at e
      have e2 : (fun d => Xa (inl d)) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a :=
        funext h1
      rw [e2] at e
      exact e
    · rw [hZe s δ]
      have e2 : (fun d => Xa (inl d * inr s)) = shLift s (psiG (rootSum (pullθ ι θ) k) a) := funext h2
      rw [e2]
  choose Z hZv hZ1 hZ2 using hZ
  obtain ⟨A, hA, hA1, hA2⟩ := GlobalTheory.T.exists_tensorInduction_virtualCharacter_prime (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s
    (by rw [hcard]; exact hp) hs (fun x => rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F')))
    (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F' θ hθ n k)
  refine ⟨A - ∑ a : Fin n, Z a, sub_mem hA (sum_mem fun a _ => hZv a), fun g => ?_, fun δ => ?_⟩
  · simp only [Pi.sub_apply, Finset.sum_apply, hA1, hZ1]
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F' _ n g]
    rw [Fin.sum_univ_eq_sum_range (fun a => hc a (n - a)
        (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n g) n]
    congr 1
    unfold chG
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [galAct_apply, ← Matrix.charpoly_map]
    congr 2
  · simp only [Pi.sub_apply, Finset.sum_apply, hA2, hZ2]
    have hex := GlobalTheory.T.every_element_is_norm F F' s hgen n δ
    rw [shLift_eq_of_exists s δ hex, GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n, ← shLift_eq_of_exists s δ hex (chG _ n),
      GlobalTheory.T.shintaniLift_charpoly_rootPowerSum_eq_norm F F' s hgen ι θ k n δ]
    rw [Fin.sum_univ_eq_sum_range (fun a => hcTw (s : F' →+* F') a (n - a)
        (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ => 1) n δ) n]
    congr 1
    · unfold chG nrm
      rw [hcard]
    · refine Finset.sum_congr rfl fun a ha => ?_
      have han : n = a + (n - a) := by have := Finset.mem_range.1 ha; omega
      rw [← shLift_eq_of_exists s δ hex (hc a (n - a) (psiG (rootSum (pullθ ι θ) k) a) (fun _ => 1) n),
        GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted F F' s hgen a (n - a) n han _ _
          ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 a (fun _ => 1) (fun _ => 1)).2.2 _).1 (fun _ _ => rfl)]
      congr 1
      funext x
      exact (hlift1 _ x).symm

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersion
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDivGroup

variable {p : ℕ} {k : Type} [CommRing k]

def liftClosed {K G H : PDivGroup p k} (i : K ⟶ G) (hi : ∀ n : ℕ, Function.Surjective (i.app n))
    (f : H ⟶ G) (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) : H ⟶ K :=
  ⟨fun n => liftSurj (i.app n) (hi n) (f.app n) (hf n), fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi (n + 1) b
    change H.res n (liftSurj (i.app (n + 1)) (hi (n + 1)) (f.app (n + 1)) (hf (n + 1))
        (i.app (n + 1) a)) =
      liftSurj (i.app n) (hi n) (f.app n) (hf n) (K.res n (i.app (n + 1) a))
    rw [liftSurj_apply, res_app, res_app, liftSurj_apply]⟩

theorem liftClosed_comp {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (f : H ⟶ G)
    (hf : ∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) :
    liftClosed i hi f hf ≫ i = f :=
  Hom.ext (funext fun n => BialgHom.ext fun a => liftSurj_apply (i.app n) (hi n) (f.app n) (hf n) a)

theorem cancel_closed {K G H : PDivGroup p k} (i : K ⟶ G)
    (hi : ∀ n : ℕ, Function.Surjective (i.app n)) (g g' : H ⟶ K) (h : g ≫ i = g' ≫ i) :
    g = g' :=
  Hom.ext (funext fun n => BialgHom.ext fun b => by
    obtain ⟨a, rfl⟩ := hi n b
    have := DFunLike.congr_fun (congrArg (fun u : H ⟶ G => u.app n) h) a
    simpa using this)

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.factor_closedImmersion : ∀ (p : ℕ) (k : Type) [CommRing k] (K G : PDivGroup p k) (i : K ⟶ G), (∀ n : ℕ, Function.Surjective (i.app n)) → (∀ (H : PDivGroup p k) (f : H ⟶ G), (∀ n : ℕ, RingHom.ker (i.app n) ≤ RingHom.ker (f.app n)) → ∃ g : H ⟶ K, g ≫ i = f) ∧ ∀ (H : PDivGroup p k) (g g' : H ⟶ K), g ≫ i = g' ≫ i → g = g' :=
  fun _ _ _ _ _ i hi => ⟨fun _ f hf => ⟨liftClosed i hi f hf, liftClosed_comp i hi f hf⟩,
    fun _ g g' h => cancel_closed i hi g g' h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCommonFixedLeOneOfCommutingHecke
section
open Module

namespace GlobalTheory.CommutingHecke

theorem fixed_mem_of_stable {ι : Type} [Finite ι] {H : ι → Type} [∀ c, Monoid (H c)] {V : Type}
    [AddCommGroup V] [Module ℂ V] (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V)
    (hea : ∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g))
    (haa : ∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h))
    (hirr : ∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (E : Submodule ℂ V) (hE : E ≠ ⊥) (hst : ∀ c g, ∀ v ∈ E, e c (a c g v) ∈ E)
    (v : V) (hv : ∀ c, e c v = v) : v ∈ E := by
  classical
  haveI := Fintype.ofFinite ι
  let Y : Finset ι → Submodule ℂ V := fun s =>
    sInf {Y | E ≤ Y ∧ ∀ c ∈ s, ∀ g, ∀ v ∈ Y, a c g v ∈ Y}
  have hEY : ∀ s, E ≤ Y s := fun s => le_sInf fun _ h => h.1
  have hYst : ∀ s, ∀ c ∈ s, ∀ g, ∀ v ∈ Y s, a c g v ∈ Y s := by
    intro s c hc g v hv
    simp only [Y, Submodule.mem_sInf] at hv ⊢
    exact fun p hp => hp.2 c hc g v (hv p hp)
  have hind : ∀ s, v ∈ Y s → v ∈ E := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro h
      have : Y ∅ ≤ E := sInf_le ⟨le_rfl, by simp⟩
      exact this h
    | insert c s hc ih =>
      intro h
      apply ih
      let Z : Submodule ℂ V := ⨅ g, (Y s).comap (e c * a c g)
      have hZ : ∀ w, w ∈ Z ↔ ∀ g, e c (a c g w) ∈ Y s := by
        intro w
        simp [Z, Submodule.mem_iInf]
      have hle : Y (insert c s) ≤ Z := by
        refine sInf_le ⟨fun w hw => (hZ w).2 fun g => hEY s (hst c g w hw), ?_⟩
        intro c' hc' g w hw
        rw [hZ] at hw ⊢
        intro g'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · have := hw (g' * g)
          rwa [map_mul, Module.End.mul_apply] at this
        · have hne : c ≠ c' := fun h => hc (h ▸ hc')
          have h1 : a c g' (a c' g w) = a c' g (a c g' w) :=
            LinearMap.congr_fun (haa c c' hne g' g).eq w
          have h2 : e c (a c' g (a c g' w)) = a c' g (e c (a c g' w)) :=
            LinearMap.congr_fun (hea c c' hne g).eq _
          rw [h1, h2]
          exact hYst s c' hc' g _ (hw g')
      have := (hZ v).1 (hle h) 1
      rwa [map_one, Module.End.one_apply, hv] at this
  apply hind Finset.univ
  rcases hirr (Y Finset.univ) (fun c => hYst _ c (Finset.mem_univ c)) with h | h
  · exact absurd (le_bot_iff.1 (h ▸ hEY _)) hE
  · rw [h]; trivial

theorem finrank_fixed_le_one (ι : Type) [Finite ι] (H : ι → Type) [∀ c, Monoid (H c)] (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : ∀ c, H c →* Module.End ℂ V) (e : ι → Module.End ℂ V)
    (hee : ∀ c, e c * e c = e c)
    (hea : ∀ c c', c ≠ c' → ∀ g, Commute (e c) (a c' g))
    (hec : ∀ c c', c ≠ c' → Commute (e c) (e c'))
    (haa : ∀ c c', c ≠ c' → ∀ g h, Commute (a c g) (a c' h))
    (hhk : ∀ c g h, e c * a c g * e c * a c h * e c = e c * a c h * e c * a c g * e c)
    (hirr : ∀ Y : Submodule ℂ V, (∀ c g, ∀ v ∈ Y, a c g v ∈ Y) → Y = ⊥ ∨ Y = ⊤)
    (W : Submodule ℂ V) (hW : ∀ v ∈ W, ∀ c, e c v = v) : finrank ℂ W ≤ 1 := by
  classical
  let W0 : Submodule ℂ V := ⨅ c, LinearMap.eqLocus (e c) LinearMap.id
  have hW0 : ∀ v, v ∈ W0 ↔ ∀ c, e c v = v := by
    intro v
    simp [W0, Submodule.mem_iInf]
  have hpres : ∀ c g, ∀ v ∈ W0, e c (a c g v) ∈ W0 := by
    intro c g v hv
    rw [hW0] at hv ⊢
    intro c'
    by_cases h : c' = c
    · subst h
      exact LinearMap.congr_fun (hee c') _
    · have h1 : e c' (e c (a c g v)) = e c (e c' (a c g v)) :=
        LinearMap.congr_fun (hec c' c h).eq _
      have h2 : e c' (a c g v) = a c g (e c' v) := LinearMap.congr_fun (hea c' c h g).eq _
      rw [h1, h2, hv]
  have hcomm : ∀ c g c' h, ∀ v ∈ W0,
      e c (a c g (e c' (a c' h v))) = e c' (a c' h (e c (a c g v))) := by
    intro c g c' h v hv
    rw [hW0] at hv
    by_cases hc : c = c'
    · subst hc
      have := LinearMap.congr_fun (hhk c g h) v
      simpa only [Module.End.mul_apply, hv] using this
    · have : Commute (e c * a c g) (e c' * a c' h) :=
        Commute.mul_left ((hec c c' hc).mul_right (hea c c' hc h))
          ((hea c' c (Ne.symm hc) g).symm.mul_right (haa c c' hc g h))
      exact LinearMap.congr_fun this.eq v
  have hWle : W ≤ W0 := fun v hv => (hW0 v).2 (hW v hv)
  refine le_trans (Submodule.finrank_mono hWle) ?_
  by_cases hbot : W0 = ⊥
  · rw [hbot]; simp
  haveI : Nontrivial W0 := Submodule.nontrivial_iff_ne_bot.2 hbot
  have hscal : ∀ c g, ∃ μ : ℂ, ∀ v ∈ W0, e c (a c g v) = μ • v := by
    intro c g
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue
      ((e c * a c g).restrict (p := W0) (q := W0) (hpres c g))
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : e c (a c g w) = μ • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨μ, fun v hv => ?_⟩
    have := fixed_mem_of_stable a e hea haa hirr (W0 ⊓ Module.End.eigenspace (e c * a c g) μ)
      ?_ ?_ v ((hW0 v).1 hv)
    · exact Module.End.mem_eigenspace_iff.1 this.2
    · rw [Submodule.ne_bot_iff]
      exact ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, fun h => hw.2 (Subtype.ext h)⟩
    · intro c' h u hu
      refine ⟨hpres c' h u hu.1, Module.End.mem_eigenspace_iff.2 ?_⟩
      have hu2 : e c (a c g u) = μ • u := Module.End.mem_eigenspace_iff.1 hu.2
      rw [Module.End.mul_apply, hcomm c g c' h u hu.1, hu2, map_smul, map_smul]
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hbot
  have hle : W0 ≤ ℂ ∙ w := by
    intro v hv
    refine fixed_mem_of_stable a e hea haa hirr (ℂ ∙ w) (by simpa using hw0) ?_ v ((hW0 v).1 hv)
    intro c g u hu
    obtain ⟨μ, hμ⟩ := hscal c g
    rw [hμ u ((Submodule.span_singleton_le_iff_mem _ _).2 hw hu)]
    exact Submodule.smul_mem _ _ hu
  exact le_trans (Submodule.finrank_mono hle) (finrank_span_singleton hw0).le

end GlobalTheory.CommutingHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenInfKerLeOfSemidirectSplit
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.BadCount.Lift

open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ]

theorem isSplit_injective {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) : Function.Injective ι := by
  intro a b hab
  have := congrArg π hab
  rwa [h.1, h.1] at this

theorem inv_mul_mem_ker {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (γ : Γ) :
    (ι (π γ))⁻¹ * γ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, h.1, inv_mul_cancel]

theorem commute_single {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (x : MonoidAlgebra ℂ G)
    (r : Γ) (hr : r ∈ π.ker) (c : ℂ) :
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x) (MonoidAlgebra.single r c) := by
  refine MonoidAlgebra.induction_on (motive := fun x =>
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x) (MonoidAlgebra.single r c)) x ?_ ?_ ?_
  · intro m
    show _ * _ = _ * _
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, h.2 m r hr]
  · intro x y hx hy
    rw [map_add (f := _)]
    exact hx.add_left hy
  · intro a x hx
    rw [map_smul]
    exact hx.smul_left a

theorem asAlgebraHom_map {V : Type} [AddCommGroup V] [Module ℂ V] (ι : G →* Γ)
    (ρ : Representation ℂ Γ V) (e : MonoidAlgebra ℂ G) :
    ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι e) =
      Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e := by
  refine MonoidAlgebra.induction_on (motive := fun e =>
    ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι e) =
      Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) e ?_ ?_ ?_
  · intro m
    simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]
  · intro x y hx hy
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  · intro a x hx
    rw [map_smul, map_smul, map_smul, hx]

variable [Fintype Γ]

def eR (π : Γ →* G) : MonoidAlgebra ℂ Γ :=
  ∑ r : π.ker, MonoidAlgebra.single (r : Γ) ((Nat.card π.ker : ℂ)⁻¹)

theorem coeff_map_mul_eR {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (x : MonoidAlgebra ℂ G)
    (γ : Γ) :
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x * eR π).coeff γ =
      x.coeff (π γ) * (Nat.card π.ker : ℂ)⁻¹ := by
  unfold eR
  rw [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [MonoidAlgebra.mul_single_apply]
  let r0 : π.ker := ⟨(ι (π γ))⁻¹ * γ, inv_mul_mem_ker h γ⟩
  have key : ∀ r : π.ker, (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x).coeff (γ * (r : Γ)⁻¹) =
      if r = r0 then x.coeff (π γ) else 0 := by
    intro r
    rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.coeff_mapDomain]
    split_ifs with hr
    · have : γ * (r : Γ)⁻¹ = ι (π γ) := by
        subst hr
        simp [r0]
      rw [this, Finsupp.mapDomain_apply_of_injective (isSplit_injective h)]
    · apply Finsupp.mapDomain_notin_range
      rintro ⟨g, hg⟩
      apply hr
      have hr1 : π (r : Γ) = 1 := r.2
      have hg' : g = π γ := by
        have := congrArg π hg
        rwa [h.1, map_mul, map_inv, hr1, inv_one, mul_one] at this
      subst hg'
      apply Subtype.ext
      show (r : Γ) = (ι (π γ))⁻¹ * γ
      rw [hg]
      group
  simp_rw [key, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def comapEquiv {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G) :
    P × π.ker ≃ P.comap π where
  toFun x := ⟨ι x.1 * x.2, by
    have hr1 : π (x.2 : Γ) = 1 := x.2.2
    simp [Subgroup.mem_comap, h.1, hr1]⟩
  invFun γ := (⟨π γ, γ.2⟩, ⟨(ι (π γ))⁻¹ * γ, inv_mul_mem_ker h γ⟩)
  left_inv x := by
    have hr1 : π (x.2 : Γ) = 1 := x.2.2
    ext <;> simp [h.1, hr1]
  right_inv γ := by
    ext
    simp

theorem card_comap {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G) :
    Nat.card (P.comap π) = Nat.card P * Nat.card π.ker := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (comapEquiv h P)).symm

end GlobalTheory.BadCount.Lift

namespace GlobalTheory.BadCount.Lift

open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ]

theorem lvlIdem_comap [Fintype G] {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G)
    (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ) (hl : ∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) :
    Formalism.L2.DIV.lvlIdem (P.comap π) lamb =
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι (Formalism.L2.DIV.lvlIdem P lam) * eR π := by
  have hcard := card_comap h P
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.L2.DIV.lvlIdem, eR, map_sum, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single, Finset.sum_mul_sum, MonoidAlgebra.single_mul_single]
  rw [← Fintype.sum_prod_type' (f := fun (i : P) (j : π.ker) =>
    MonoidAlgebra.single (ι (i : G) * (j : Γ))
      ((Nat.card P : ℂ)⁻¹ * ((lam i⁻¹ : ℂˣ) : ℂ) * (Nat.card π.ker : ℂ)⁻¹))]
  refine (Fintype.sum_equiv (comapEquiv h P) _ _ (fun x => ?_)).symm
  have hr1 : π (x.2 : Γ) = 1 := x.2.2
  have hx : lamb ((comapEquiv h P) x)⁻¹ = lam x.1⁻¹ := by
    rw [hl]
    congr 1
    apply Subtype.ext
    simp [comapEquiv, h.1, hr1]
  simp only [hx, hcard, Nat.cast_mul, mul_inv]
  congr 1
  ring

end GlobalTheory.BadCount.Lift


open scoped Classical in
theorem GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit : ∀ (G Γ V : Type) [Group G] [Fintype G] [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G) (ι : G →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup G) (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ G) (b : Fin 2 → MonoidAlgebra ℂ G) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → (∀ k, b k * b k = b k) → (∀ k a, b k * a = a * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff 1 = (s k : ℂ) / (Nat.card P : ℂ)) → (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  intro G Γ V _ _ _ _ _ _ _ π ι h ρ P lam lamb hl H n e b s c hEmb hcard hidem hcent hsum hsupp hcoeff
  let ιA := MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι
  have hL := GlobalTheory.BadCount.Lift.lvlIdem_comap h P lam lamb hl
  have hR : (Nat.card π.ker : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hP : (Nat.card P : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hprod : ∀ k, ιA (b k) * Formalism.L2.DIV.lvlIdem (P.comap π) lamb =
      ιA (b k * Formalism.L2.DIV.lvlIdem P lam) * GlobalTheory.BadCount.Lift.eR π := by
    intro k
    rw [hL, map_mul, mul_assoc]
  have hco : ∀ k γ, (ιA (b k) * Formalism.L2.DIV.lvlIdem (P.comap π) lamb).coeff γ =
      (b k * Formalism.L2.DIV.lvlIdem P lam).coeff (π γ) * (Nat.card π.ker : ℂ)⁻¹ := by
    intro k γ
    rw [hprod]
    exact GlobalTheory.BadCount.Lift.coeff_map_mul_eR h _ γ
  have key := _root_.GlobalTheory.BadCount.finrank_eig_inf_ker_le Γ V ρ (P.comap π) lamb (fun k => (H k).comap π) n (ιA e) (fun k => ιA (b k)) s c
    hEmb hcard
    (fun k => by rw [← map_mul, hidem])
    (fun k => by
      rw [hL]
      refine Commute.mul_right ?_ ?_
      · exact Commute.map (show Commute (b k) (Formalism.L2.DIV.lvlIdem P lam) from hcent k _) ιA
      · unfold GlobalTheory.BadCount.Lift.eR
        refine Commute.sum_right _ _ _ (fun r _ => ?_)
        exact GlobalTheory.BadCount.Lift.commute_single h _ r r.2 _)
    (by rw [← map_one ιA, ← map_sub, hsum, map_sub, map_add (f := _), map_mul])
    (fun k γ hne => by
      rw [hco] at hne
      show π γ ∈ H k
      apply hsupp k
      intro h0
      apply hne
      rw [h0, zero_mul])
    (fun k => by
      rw [hco, map_one, hcoeff, GlobalTheory.BadCount.Lift.card_comap h P, Nat.cast_mul]
      field_simp)
  rwa [GlobalTheory.BadCount.Lift.asAlgebraHom_map] at key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealLatticeHasNonrealMultiplier
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.LatOfMult

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → (∀ a : 𝓞 K, MulStable Λ (ι a)) ∧ MulStable Λ (ι δ) ∧ (ι δ).im ≠ 0 ∧ IsIntegral ℤ δ := by
  intro K _ _ d δ ι 𝔞 Λ hd hδ hL
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ x ∈ (𝔞 : Set K), ι x = z := by
    intro z
    have := congrArg (fun S : Set ℂ => z ∈ S) hL
    simpa using this
  have hstab : ∀ a : 𝓞 K, MulStable Λ (ι a) := by
    intro a ω hω
    obtain ⟨x, hx, rfl⟩ := (hmem ω).1 hω
    refine (hmem _).2 ⟨(a : K) * x, ?_, by simp⟩
    have h1 : a • x ∈ (𝔞 : Submodule (𝓞 K) K) := Submodule.smul_mem _ a hx
    rwa [Algebra.smul_def] at h1
  have hint : IsIntegral ℤ δ := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hδ]
  refine ⟨hstab, ?_, ?_, hint⟩
  · exact hstab ⟨δ, hint⟩
  · intro him
    have h2 : (ι δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
    have h3 := congrArg Complex.re h2
    simp [pow_two, Complex.mul_re, him] at h3
    have : (0:ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg (ι δ).re]

end GlobalTheory.LatOfMult
end

