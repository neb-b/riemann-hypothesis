module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinCoordsArithVar
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_const_mul {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (a : ℂ) (f : GL (Fin n) F → ℂ) (δ : GL (Fin n) F') :
    shLift s (fun x => a * f x) δ = a * shLift s f δ := by
  unfold shLift
  split_ifs <;> simp

theorem shLift_cusp_kills_J : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ n k : ℕ, 0 < n → Module.finrank F F' ∣ n → Reg (Nat.card F) n k →
    Kills (shLift s (cusp (pullθ ι θ) n k)) (J θ (liftL (Nat.card F) (Module.finrank F F') [(n, k)]) n) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ n k hn hln hreg
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : Module.Finite F F' := Module.Finite.of_finite
  haveI : IsGalois F F' := inferInstance
  have hΓ : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := IsGalois.card_aut_eq_finrank F F'
  haveI : Finite (F' ≃ₐ[F] F') := Nat.finite_of_card_ne_zero (by rw [hΓ]; exact hl.ne_zero)
  letI : Fintype (F' ≃ₐ[F] F') := Fintype.ofFinite _
  haveI : Fact (Nat.card (F' ≃ₐ[F] F')).Prime := ⟨hΓ ▸ hl⟩
  have hgen : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
    intro t
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Subgroup.zpowers s) with h | h
    · exact absurd (Subgroup.zpowers_eq_bot.1 h) hs
    · rw [h]; exact Subgroup.mem_top t

  have hθ' : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → pullθ ι θ x = pullθ ι θ y → x = y := by
    intro x y hx hy hxy
    apply ι.toRingHom.injective
    exact hθ (ι x) (ι y) ((map_ne_zero ι.toRingHom).2 hx) ((map_ne_zero ι.toRingHom).2 hy) hxy
  set l := Module.finrank F F' with hldef
  set q := Nat.card F with hqdef
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hcardF' : Nat.card F' = q ^ l := Module.natCard_eq_pow_finrank

  obtain ⟨X, hX, hXg, hXs⟩ := GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift F F' s hl hs ι θ hθ k n
  set c : ℂ := (-1) ^ (n - 1) with hc
  have hc2 : c = 1 ∨ c = -1 := neg_one_pow_eq_or ℂ (n - 1)
  set X' : GHat F F' n → ℂ := fun g => c * X g with hX'
  have hX'v : X' ∈ Virt ℂ ℂ (GHat F F' n) := by
    rcases hc2 with h | h
    · have : X' = X := by funext g; simp [hX', h]
      rw [this]; exact hX
    · have : X' = -X := by funext g; simp [hX', h]
      rw [this]; exact neg_mem hX
  have hcusp : cusp (pullθ ι θ) n k = fun x => c * psiG (rootSum (pullθ ι θ) k) n x := rfl
  have hX's : ∀ δ, X' (inl δ * inr s) = shLift s (cusp (pullθ ι θ) n k) δ := by
    intro δ
    rw [hcusp, shLift_const_mul, ← hXs δ]

  obtain ⟨hchar, hnorm⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F (pullθ ι θ) hθ' n k hn hreg
  have hclc : IsCl (cusp (pullθ ι θ) n k) := by
    intro x y
    rw [hcusp]
    simp only
    rw [((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 0) (fun _ => 0)).2.2 (rootSum (pullθ ι θ) k)).1 x y]
  have hiso := GlobalTheory.T.shintaniLiftClassFunction_isometry F F' s hgen n _ _ hclc hclc
  rw [hnorm] at hiso
  have hGne : (Nat.card (GL (Fin n) F) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := GL (Fin n) F)).ne'
  have hnorm' : ∑ᶠ δ, X' (inl δ * inr s) * star (X' (inl δ * inr s)) = (Nat.card (GL (Fin n) F') : ℂ) := by
    simp only [hX's]
    apply mul_left_cancel₀ hGne
    rw [hiso, mul_comm]

  obtain ⟨hdeg, hlift⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [(n, k)] hq2 hl.pos (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨hn, hln, hreg⟩)
  have hdegn : deg (liftL q l [(n, k)]) = n := by rw [hdeg]; simp [deg]
  have hYchar : IsChar ℂ ℂ (J θ (liftL q l [(n, k)]) n) := by
    apply GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F' θ hθ _ _ n hdegn.symm
    intro p hp
    rw [hcardF']
    exact hlift p hp
  have hYst : ∀ g, J θ (liftL q l [(n, k)]) n (galAct F F' n s g) = J θ (liftL q l [(n, k)]) n g :=
    GlobalTheory.T.harishChandraProduct_shintaniLift_galois F F' θ s [(n, k)] n hdegn.symm

  obtain ⟨m, hm⟩ := hln
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm; omega
    · exact h
  obtain ⟨z, hz, hzsum⟩ := GlobalTheory.T.cuspidal_galois_pairing_eq_pm_one_prime_degree F F' s hl hs ι θ hθ m k n hm0 hm hreg
  have hpair : ∑ᶠ g, X' (inl g) * star (J θ (liftL q l [(n, k)]) n g)
      = ((if c = 1 then z else -z : ℤ) : ℂ) * (Nat.card (GL (Fin n) F') : ℂ) := by
    have : (fun g : GL (Fin n) F' => X' (inl g) * star (J θ (liftL q l [(n, k)]) n g))
        = fun g => c * (X (inl g) * star (J θ (liftL q l [(n, k)]) n g)) := by
      funext g; simp only [hX']; ring
    rw [this, ← mul_finsum]
    simp only [hXg]
    rw [hzsum]
    rcases hc2 with h | h
    · rw [h]; simp
    · rw [h]; have : (-1 : ℂ) ≠ 1 := by norm_num
      simp [this]
  have hndvd : ¬ ((Nat.card (F' ≃ₐ[F] F') : ℤ) ∣ (if c = 1 then z else -z)) := by
    rw [hΓ]
    intro hd
    have hd' : (l : ℤ) ∣ z := by
      split_ifs at hd
      · exact hd
      · exact (dvd_neg).1 hd
    have h1 : (l : ℤ) ∣ 1 := by
      rcases hz with h | h
      · rwa [h] at hd'
      · rw [h] at hd'; exact (dvd_neg).1 hd'
    have : l ∣ 1 := by exact_mod_cast h1
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  have hK := GlobalTheory.T.twisted_virtualCharacter_norm_one_support (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (hΓ ▸ hl) hs X' hX'v hnorm'
    (J θ (liftL q l [(n, k)]) n) hYchar hYst _ hpair hndvd
  have hfun : (fun δ => X' (inl δ * inr s)) = shLift s (cusp (pullθ ι θ) n k) := funext hX's
  rw [hfun] at hK
  exact hK

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
section
noncomputable section

open NumberField Topology

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)


omit [_root_.NumberField.IsTotallyComplex E] in
theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

theorem IsAutForm.continuous {φ : Sm E a} (h : IsAutForm φ) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hmul : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hN : {g : GA E a | Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ := by
    refine (h.level.preimage (continuous_mapFin.comp hmul)).mem_nhds ?_
    simp
  have heq : φ.1 =ᶠ[𝓝 g₀] fun g => chart φ.1 g₀ (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
    filter_upwards [hN] with g hg
    rw [chart_val]
    have hk : ∀ x, φ.1 (x * finGL E a (Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) = φ.1 x :=
      fun x => congrArg (fun ψ : Sm E a => ψ.1 x) hg
    conv_lhs => rw [← mul_inv_cancel_left g₀ g, ← infGL_mul_finGL (g₀⁻¹ * g), ← mul_assoc, hk]
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (chart φ.1 g₀) (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ (val_mem_invSet _)).continuousAt
  exact ContinuousAt.comp (f := fun g : GA E a => toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) hc
    (Units.continuous_val.comp (continuous_mapInf.comp hmul)).continuousAt

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockGLHomConjPermMatrixOfBlocksMatch
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.Proof.BlockConj

theorem range_blockEnum {r d : ℕ} (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (k : Fin r) :
    k ∈ Set.range (blockEnum b c h) ↔ b k = c := by
  have h1 : Set.range (blockEnum b c h) = (block b c : Set (Fin r)) :=
    Finset.range_orderEmbOfFin (block b c) h
  rw [h1]
  simp [block]

theorem blockHom_conj_permGL (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ) (w : Equiv.Perm (Fin r))
    (hw : ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) (i : Fin r) :
    (block b (b i)).card = (block b' (b' (w i))).card ∧
    ∀ (d : ℕ) (h : (block b (b i)).card = d) (h' : (block b' (b' (w i))).card = d),
      ∃ π : GL (Fin d) F, ∀ g : GL (Fin d) F,
        (blockHom F b' (b' (w i)) h' (π * g * π⁻¹) : GL (Fin r) F) * permGL F w =
          permGL F w * (blockHom F b (b i) h g : GL (Fin r) F) := by
  refine ⟨?_, fun d h h' => ?_⟩
  · refine Finset.card_equiv w fun k => ?_
    simp [block, hw k i]
  · set e := blockEnum b (b i) h with he
    set e' := blockEnum b' (b' (w i)) h' with he'
    have hr : ∀ k, k ∈ Set.range e ↔ w k ∈ Set.range e' := fun k => by
      rw [he, he', range_blockEnum, range_blockEnum, hw k i]
    have hex : ∀ a, ∃ a', e' a' = w (e a) := fun a => (hr (e a)).1 ⟨a, rfl⟩
    choose p hp using hex
    have hinj : Function.Injective p := fun a a' haa => by
      apply e.injective
      apply w.injective
      rw [← hp, ← hp, haa]
    let π₀ : Equiv.Perm (Fin d) := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj)
    have hπ : ∀ a, e' (π₀ a) = w (e a) := hp
    refine ⟨permGL F π₀, fun g => ?_⟩
    refine eq_mul_inv_iff_mul_eq.1 ?_
    ext k l
    obtain ⟨k, rfl⟩ := w.surjective k
    obtain ⟨l, rfl⟩ := w.surjective l
    rw [conj_permGL_apply]
    show extendMat e' ((permGL F π₀ * g * (permGL F π₀)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) (w k) (w l)
      = extendMat e (g : Matrix (Fin d) (Fin d) F) k l
    by_cases hkl : k ∈ Set.range e ∧ l ∈ Set.range e
    · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := hkl
      rw [← hπ, ← hπ, extendMat_in, extendMat_in, conj_permGL_apply]
    · rw [not_and_or] at hkl
      rw [extendMat_out _ _ _ _ hkl, extendMat_out _ _ _ _ (by rwa [← hr, ← hr])]
      simp [Matrix.one_apply]

end GlobalTheory.Proof.BlockConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDetEqLinearCombinationNatNodes
section
open NumberField GlobalTheory.CuspRep

noncomputable section

open Polynomial Finset

namespace GlobalTheory.CuspRep

theorem eval_eq_sum_lagrange_nodes (b : ℕ) (u : ℂ) (f : ℂ[X]) (hf : f.degree < ((b + 1 : ℕ) : WithBot ℕ)) :
    f.eval u = ∑ j : Fin (b + 1),
      (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u * f.eval ((j : ℕ) : ℂ) := by
  have hinj : Set.InjOn (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) (univ : Finset (Fin (b + 1))) := by
    intro x _ y _ h
    exact Fin.ext (by simpa using h)
  have e := Lagrange.eq_interpolate (s := univ) hinj (f := f) (by simpa using hf)
  conv_lhs => rw [e]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, mul_comm]

theorem cap_eq_sum_nodes (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (τ : E →+* ℂ) (u : ℂ) :
    ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ) := by
  obtain ⟨c, -, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ (Sm E b)) b (Eop τ)
  have hcap : ∀ v : ℂ, cap (a := b) τ v =
      ∑ i ∈ range (b + 1), ((X + C (((b : ℂ) - 1) / 2)) ^ i).eval v • c i := by
    intro v
    rw [cap, hc]
    simp only [eval_pow, eval_add, eval_X, eval_C]
  refine ⟨fun j => (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u, ?_⟩
  simp_rw [hcap, smul_sum, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_smul, ← eval_eq_sum_lagrange_nodes]
  have hi' : i < b + 1 := mem_range.1 hi
  rw [degree_pow, degree_X_add_C]
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast hi'

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenforms
section
open NumberField

namespace GlobalTheory.CuspRep

theorem Zalg_acts_by_scalar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (c : (E →+* ℂ) → ℂ → ℂ) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a →
    ∃ s : ℂ, ∀ φ : GlobalTheory.CuspRep.Sm E a, (∀ τ u, GlobalTheory.CuspRep.cap τ u φ = c τ u • φ) → z φ = s • φ := by
  intro E _ _ _ a c z hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨c τ u, fun φ hφ => hφ τ u⟩
  | algebraMap r => exact ⟨r, fun φ _ => by simp [Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, fun φ hφ => by rw [LinearMap.add_apply, hs φ hφ, ht φ hφ, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s * t, fun φ hφ => by rw [Module.End.mul_apply, ht φ hφ, map_smul, hs φ hφ, smul_smul, mul_comm]⟩

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
section
open NumberField GlobalTheory.CuspRep Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CuspRep.JointCont

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem map_unip {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : BlockIx a r → R) :
    Matrix.GeneralLinearGroup.map f (unip x) = unip (fun p => f (x p)) := by
  apply Units.ext
  ext i j
  change f ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) = (1 + nilM fun p => f (x p) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add (f := _)]
  split_ifs <;> simp

theorem continuous_nilM {R : Type} [CommRing R] [TopologicalSpace R] :
    Continuous (fun x : BlockIx a r → R => (nilM x : Matrix (Fin a) (Fin a) R)) := by
  refine continuous_matrix fun i j => ?_
  simp only [nilM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_unip {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun x : BlockIx a r → R => unip x) :=
  Units.continuous_iff.2 ⟨continuous_const.add continuous_nilM, continuous_const.sub continuous_nilM⟩

theorem continuous_pInf : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem chart_mul_finGL_of_fix (φ : Sm E a) (h : GA E a) (k : GL (Fin a) (Af E)) (hk : finRep E a k φ = φ) :
    chart φ.1 (h * finGL E a k) = chart φ.1 h := by
  rw [← chart_rt_fin]
  congr 1
  funext z
  exact congrArg (fun ψ : Sm E a => ψ.1 z) hk

def infPart (g : GA E a) (x : BlockIx a r → Ad E) : GL (Fin a) (Cinf E) :=
  unip (fun p => pInf E (x p)) * Matrix.GeneralLinearGroup.map (pInf E) g

def finPart (g : GA E a) (x : BlockIx a r → Ad E) : GL (Fin a) (Af E) :=
  unip (fun p => pFin E (x p)) * Matrix.GeneralLinearGroup.map (pFin E) g

theorem unip_mul_eq (g : GA E a) (x : BlockIx a r → Ad E) :
    unip x * g = finGL E a (finPart g x) * infGL E a (infPart g x) := by
  refine ga_ext ?_ ?_ <;>
    simp only [finPart, infPart, map_mul, map_unip, pInf_finGL, pInf_infGL, pFin_finGL, pFin_infGL, one_mul, mul_one]

theorem continuous_infPart (g : GA E a) : Continuous (fun x : BlockIx a r → Ad E => toL (infPart g x).val) := by
  have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p)) :=
    continuous_pi fun p => continuous_pInf.comp (continuous_apply p)
  have h2 : Continuous (fun x : BlockIx a r → Ad E =>
      ((infPart g x : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))) :=
    Units.continuous_val.comp ((continuous_unip.comp h1).mul continuous_const)
  exact h2

theorem continuous_finPart (g : GA E a) : Continuous (fun x : BlockIx a r → Ad E => finPart g x) := by
  have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pFin E (x p)) :=
    continuous_pi fun p => continuous_pFin.comp (continuous_apply p)
  exact (continuous_unip.comp h1).mul continuous_const

theorem eventually_chart_eq (φ : Sm E a) (hφ : IsAutForm φ) (g : GA E a) (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, chart φ.1 (unip x * g) =
      chart φ.1 (finGL E a (finPart g x₀)) ∘ lmul (toL (infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (finPart g x₀)⁻¹ * finPart g x) := continuous_const.mul (continuous_finPart g)
  have h1 : finRep E a ((finPart g x₀)⁻¹ * finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.level.mem_nhds h1)] with x hx
  have hx' : finRep E a ((finPart g x₀)⁻¹ * finPart g x) φ = φ := hx
  rw [unip_mul_eq, ← mul_inv_cancel_left (finPart g x₀) (finPart g x), map_mul, mul_assoc, ← infGL_comm,
    ← mul_assoc, chart_mul_finGL_of_fix φ _ _ hx', chart_mul]

theorem chart_unipotent_translate_continuousOn (φ : Sm E a) (hφ : IsAutForm φ) (g : GA E a) (X : Lie E a) :
    ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E a => chart φ.1 (unip p.1 * g) p.2)
        (Set.univ ×ˢ invSet E a) ∧
      ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E a => fderiv ℝ (chart φ.1 (unip p.1 * g)) p.2 X)
        (Set.univ ×ˢ invSet E a) := by
  have hP : Continuous (fun p : (BlockIx a r → Ad E) × Lie E a => lmul (toL (infPart g p.1).val) p.2) := by
    have := ((continuous_infPart g).comp continuous_fst).matrix_mul
      (continuous_snd : Continuous fun p : (BlockIx a r → Ad E) × Matrix (Fin a) (Fin a) (Cinf E) => p.2)
    exact this
  have hQ : Continuous (fun p : (BlockIx a r → Ad E) × Lie E a => lmul (toL (infPart g p.1).val) X) := by
    have := ((continuous_infPart g).comp continuous_fst).matrix_mul
      (continuous_const : Continuous fun _ : (BlockIx a r → Ad E) × Lie E a => (Matrix.of X))
    exact this
  have hinv : ∀ p : (BlockIx a r → Ad E) × Lie E a, p.2 ∈ invSet E a →
      lmul (toL (infPart g p.1).val) p.2 ∈ invSet E a := fun p hp => (infPart g p.1).isUnit.mul hp
  constructor
  · rintro ⟨x₀, y₀⟩ ⟨-, hy₀⟩
    set f₀ := chart φ.1 (finGL E a (finPart g x₀))
    have hf₀ : ContDiffOn ℝ ∞ f₀ (invSet E a) := φ.2 _
    have hA : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E a => f₀ (lmul (toL (infPart g p.1).val) p.2))
        (x₀, y₀) :=
      ContinuousAt.comp (g := f₀) (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (hinv (x₀, y₀) hy₀)))
        hP.continuousAt
    refine (hA.congr ?_).continuousWithinAt
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually (eventually_chart_eq φ hφ g x₀)] with p hp
    rw [hp]; rfl
  · rintro ⟨x₀, y₀⟩ ⟨-, hy₀⟩
    set f₀ := chart φ.1 (finGL E a (finPart g x₀))
    have hf₀ : ContDiffOn ℝ ∞ f₀ (invSet E a) := φ.2 _
    have hD : ContinuousOn (fun z => fderiv ℝ f₀ z) (invSet E a) :=
      hf₀.continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
    have hA : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E a =>
        fderiv ℝ f₀ (lmul (toL (infPart g p.1).val) p.2) (lmul (toL (infPart g p.1).val) X)) (x₀, y₀) :=
      ContinuousAt.clm_apply
        (ContinuousAt.comp (g := fun z => fderiv ℝ f₀ z)
          (hD.continuousAt (isOpen_invSet.mem_nhds (hinv (x₀, y₀) hy₀))) hP.continuousAt)
        hQ.continuousAt
    refine (hA.congr ?_).continuousWithinAt
    have hy : ∀ᶠ p : (BlockIx a r → Ad E) × Lie E a in 𝓝 (x₀, y₀), p.2 ∈ invSet E a :=
      (continuous_snd.tendsto (x₀, y₀)).eventually (isOpen_invSet.mem_nhds hy₀)
    filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually (eventually_chart_eq φ hφ g x₀), hy]
      with p hp hp2
    have hd : DifferentiableAt ℝ f₀ (lmul (toL (infPart g p.1).val) p.2) :=
      (hf₀.contDiffAt (isOpen_invSet.mem_nhds (hinv p hp2))).differentiableAt (by simp)
    change _ = fderiv ℝ (chart φ.1 (unip p.1 * g)) p.2 X
    rw [hp, fderiv_comp _ hd (lmul _).differentiableAt, ContinuousLinearMap.fderiv]
    rfl

theorem chart_jointCont : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ (g : GlobalTheory.CuspRep.GA E a) (X : GlobalTheory.CuspRep.Lie E a), ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g) p.2) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) ∧ ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => fderiv ℝ (GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g)) p.2 X) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) :=
  fun _ _ _ _ _ _ φ hφ g X => chart_unipotent_translate_continuousOn φ hφ g X

end GlobalTheory.CuspRep.JointCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginNoethStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divConst_origin_noeth_alt : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  first | (exact @GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (exact GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (intros; apply GlobalTheory.VertUnitsNoeth.divConst_origin_noeth <;> assumption)
end

