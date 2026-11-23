module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
section
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SplitField

def EndSpanned {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (W : Submodule L (Fin a → L)) : Prop :=
  ∀ φ : W →ₗ[L] W, ∃ X ∈ Submodule.span L (Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)),
    ∀ w : W, X.mulVec (w : Fin a → L) = (φ w : Fin a → L)

end GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ} (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) : mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  refine MonoidHom.ext fun x => Units.ext ?_
  ext i k
  simp [mapRep]

theorem exists_finite_field {K : Type} [Field K] (S : Set (AlgebraicClosure K)) (hS : S.Finite) : ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (f : K' →+* AlgebraicClosure K), (∀ x : K, f (algebraMap K K' x) = algebraMap K (AlgebraicClosure K) x) ∧ S ⊆ Set.range f := by
  haveI := hS.to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact ⟨IntermediateField.adjoin K S, inferInstance, inferInstance, hfd, (IntermediateField.adjoin K S).val.toRingHom,
    fun x => rfl, fun x hx => ⟨⟨x, IntermediateField.subset_adjoin K S hx⟩, rfl⟩⟩

theorem mem_span_of_map_mem_span {L E ι : Type} [Field L] [Field E] [Fintype ι] (f : L →+* E) (S : Set (ι → L)) (y : ι → L) (h : (f ∘ y) ∈ Submodule.span E ((fun v => f ∘ v) '' S)) : y ∈ Submodule.span L S := by
  classical
  by_contra hy
  have hq : (Submodule.span L S).mkQ y ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual L ((ι → L) ⧸ Submodule.span L S), ψ ((Submodule.span L S).mkQ y) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff L _).1 hc)
  set l : (ι → L) →ₗ[L] L := ψ ∘ₗ (Submodule.span L S).mkQ with hl
  have hlS : ∀ s ∈ S, l s = 0 := by
    intro s hs
    simp [hl, (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span hs)]
  let c : ι → L := fun i => l (fun j => if i = j then 1 else 0)
  have hlc : ∀ v, l v = ∑ i, v i * c i := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ l v]
    simp [c, smul_eq_mul]
  let Λ : (ι → E) →ₗ[E] E := ∑ i, f (c i) • LinearMap.proj i
  have hΛ : ∀ v, Λ (f ∘ v) = f (l v) := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Λ, hlc, map_sum, mul_comm]
  have hker : Submodule.span E ((fun v => f ∘ v) '' S) ≤ LinearMap.ker Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    simp [hΛ, hlS s hs]
  have h1 := hker h
  rw [LinearMap.mem_ker, hΛ] at h1
  exact hψ ((map_eq_zero f).1 h1)

theorem mulVec_mem_of_mem_span {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (W : Submodule L (Fin a → L)) (hW : IsInv τ W) {X : Matrix (Fin a) (Fin a) L}
    (hX : X ∈ Submodule.span L (Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) :
    ∀ w ∈ W, X.mulVec w ∈ W := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hW g
  | zero => intro w _; simp
  | add x y _ _ hx hy => intro w hw; rw [Matrix.add_mulVec]; exact W.add_mem (hx w hw) (hy w hw)
  | smul c x _ hx => intro w hw; rw [Matrix.smul_mulVec]; exact W.smul_mem c (hx w hw)

theorem isIrrSub_of_endSpanned {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (W : Submodule L (Fin a → L)) (hne : W ≠ ⊥) (hinv : IsInv τ W) (hE : EndSpanned τ W) : IsIrrSub τ W := by
  classical
  refine ⟨hne, hinv, fun W' hle hinv' => ?_⟩
  by_cases h0 : W' = ⊥
  · exact Or.inl h0
  right
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff W').1 h0
  refine le_antisymm hle fun u hu => ?_
  have hx' : (⟨x, hle hx⟩ : W) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual L W, φ ⟨x, hle hx⟩ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx' ((Module.forall_dual_apply_eq_zero_iff L _).1 hc)
  obtain ⟨X, hX, hXw⟩ := hE (((φ ⟨x, hle hx⟩)⁻¹ • φ).smulRight (⟨u, hu⟩ : W))
  have h1 := hXw ⟨x, hle hx⟩
  simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ, one_smul] at h1
  rw [← h1]
  exact mulVec_mem_of_mem_span τ W' hinv' hX x hx

end GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem map_mulVec_mem_of_mem_span {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (U : Submodule E (Fin a → E)) (hU : IsInv (mapRep f τ) U) {X : Matrix (Fin a) (Fin a) L}
    (hX : X ∈ Submodule.span L (Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) :
    ∀ u ∈ U, (X.map f).mulVec u ∈ U := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hU g
  | zero => intro u _; rw [Matrix.map_zero _ (map_zero f), Matrix.zero_mulVec]; exact U.zero_mem
  | add x y _ _ hx hy => intro u hu; rw [Matrix.map_add _ (map_add f), Matrix.add_mulVec]; exact U.add_mem (hx u hu) (hy u hu)
  | smul c x _ hx =>
    intro u hu
    have : (c • x).map f = f c • x.map f := by ext i j; simp
    rw [this, Matrix.smul_mulVec]; exact U.smul_mem _ (hx u hu)

theorem absIrrSub_of_endSpanned {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (W : Submodule L (Fin a → L)) (hne : W ≠ ⊥) (hinv : IsInv τ W) (hE : EndSpanned τ W) : AbsIrrSub τ W := by
  unfold AbsIrrSub
  set f := algebraMap L (AlgebraicClosure L) with hf
  have hmap : ∀ (M : Matrix (Fin a) (Fin a) L) (v : Fin a → L),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v
    funext i
    exact (RingHom.map_mulVec f M v i).symm
  have hrep : ∀ g, ((mapRep f τ g : GL (Fin a) (AlgebraicClosure L)) : Matrix (Fin a) (Fin a) (AlgebraicClosure L))
      = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).map f := fun g => rfl
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hne
    refine (Submodule.ne_bot_iff _).2 ⟨f ∘ v, Submodule.subset_span ⟨v, hv, rfl⟩, ?_⟩
    intro h
    apply hv0
    funext i
    have := congrFun h i
    simpa using this
  · intro g u hu
    show ((mapRep f τ g : GL (Fin a) (AlgebraicClosure L)) : Matrix (Fin a) (Fin a) (AlgebraicClosure L)).mulVec u ∈ _
    rw [hrep]
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [hmap]
      exact Submodule.subset_span ⟨_, hinv g v hv, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx
  · intro U hU hinvU
    have key : ∀ φ : W →ₗ[L] W, ∃ M : Matrix (Fin a) (Fin a) L,
        (∀ u ∈ U, (M.map f).mulVec u ∈ U) ∧ ∀ w : W, M.mulVec w = (φ w : Fin a → L) := by
      intro φ
      obtain ⟨X, hX, hXw⟩ := hE φ
      exact ⟨X, map_mulVec_mem_of_mem_span f τ U hinvU hX, hXw⟩
    by_cases h0 : U = ⊥
    · exact Or.inl h0
    right
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).1 h0
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu0 (funext h)
    refine le_antisymm hU (Submodule.span_le.2 ?_)
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨M, h1, h2⟩ := key
      (((LinearMap.proj j : (Fin a → L) →ₗ[L] L).comp W.subtype).smulRight (⟨w, hw⟩ : W))
    have h3 : ∀ x ∈ Submodule.span (AlgebraicClosure L) ((fun v => f ∘ v) '' (W : Set (Fin a → L))),
        (M.map f).mulVec x = x j • (f ∘ w) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        rw [hmap]
        have := h2 ⟨v, hv⟩
        simp only at this
        rw [this]
        funext i
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, Pi.add_apply, add_smul]
      | smul c x _ hx => rw [Matrix.mulVec_smul, hx, Pi.smul_apply, smul_eq_mul, mul_smul]
    have h4 := h1 u hu
    rw [h3 u (hU hu)] at h4
    exact (U.smul_mem_iff hj).1 h4

theorem endSpanned_of_isoSub {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (W U : Submodule L (Fin a → L)) (hW : IsInv τ W) (hiso : IsoSub τ W U) (hE : EndSpanned τ U) : EndSpanned τ W := by
  obtain ⟨e, he⟩ := hiso
  intro φ
  obtain ⟨X, hX, hXw⟩ := hE ((e : W →ₗ[L] U) ∘ₗ φ ∘ₗ (e.symm : U →ₗ[L] W))
  refine ⟨X, hX, fun w => ?_⟩
  have key : ∀ v : W, ∃ h : X.mulVec (v : Fin a → L) ∈ W, ((e ⟨_, h⟩ : U) : Fin a → L) = X.mulVec (e v : Fin a → L) := by
    clear hXw
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v
      exact ⟨hW g v v.2, he g v _⟩
    | zero =>
      intro v
      refine ⟨by simp, ?_⟩
      simp only [Matrix.zero_mulVec]
      have : (⟨0, W.zero_mem⟩ : W) = 0 := rfl
      rw [this, e.map_zero]; rfl
    | add x y hx' hy' hx hy =>
      intro v
      obtain ⟨h1, e1⟩ := hx v
      obtain ⟨h2, e2⟩ := hy v
      refine ⟨by rw [Matrix.add_mulVec]; exact W.add_mem h1 h2, ?_⟩
      have : (⟨(x + y).mulVec v, by rw [Matrix.add_mulVec]; exact W.add_mem h1 h2⟩ : W) = ⟨_, h1⟩ + ⟨_, h2⟩ := by
        ext1; simp [Matrix.add_mulVec]
      rw [this, map_add (f := _), Submodule.coe_add, e1, e2, Matrix.add_mulVec]
    | smul c x hx' hx =>
      intro v
      obtain ⟨h1, e1⟩ := hx v
      refine ⟨by rw [Matrix.smul_mulVec]; exact W.smul_mem c h1, ?_⟩
      have : (⟨(c • x).mulVec v, by rw [Matrix.smul_mulVec]; exact W.smul_mem c h1⟩ : W) = c • ⟨_, h1⟩ := by
        ext1; simp [Matrix.smul_mulVec]
      rw [this, map_smul, Submodule.coe_smul, e1, Matrix.smul_mulVec]
  obtain ⟨h, hk⟩ := key w
  have h2 := hXw (e w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2
  rw [h2] at hk
  have := e.injective (Subtype.ext hk)
  exact congrArg Subtype.val this
end GlobalTheory.SplitField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDeterminedBySplitComponentsOfBaseChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.PtOfLocSplit

theorem eventually_splitOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    ∀ᶠ w in Filter.cofinite, IsSplitPl H w → SplitOut N i w := by
  have hl : (N.l i).Prime := Fact.out
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by simpa using hl.ne_zero
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  filter_upwards [hfin.eventually_cofinite_notMem, (N.S i).eventually_cofinite_notMem,
    (N.Q i).eventually_cofinite_notMem] with w h1 h2 h3 hw using ⟨hw, h1, h2, h3⟩

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.PtOfLoc N A i := by
  intro R H what₂ N A i hBC hSp hRep P P' x hx hloc
  have hPP : P = P' := _root_.GlobalTheory.RowTie.repDet_split R H what₂ N A i hBC hSp hRep P P' <| by
    filter_upwards [eventually_splitOut N i] with w hw hs using hloc w (hw hs)
  rw [hPP]; exact hx

end GlobalTheory.PtOfLocSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.RowThetaParam

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpSum_zero_left {w : PlE H} (a : A.LP w) : A.lpSum (A.lpZero w) a = a := by
  rw [A.lpSum_comm, A.lpSum_zero]

theorem isoLoc_cons (p : Part A.CG) (L : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (p :: L) w = A.lpSum (spehLoc N A p w) (isoLoc N A L w) := rfl

theorem isoLoc_nil (w : PlE H) : isoLoc N A [] w = A.lpZero w := rfl

theorem isoLoc_append (L L' : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (L ++ L') w = A.lpSum (isoLoc N A L w) (isoLoc N A L' w) := by
  induction L with
  | nil => rw [List.nil_append, isoLoc_nil, lpSum_zero_left]
  | cons p L ih => rw [List.cons_append, isoLoc_cons, isoLoc_cons, ih, A.lpSum_assoc]

theorem isoLoc_perm {L L' : List (Part A.CG)} (h : L.Perm L') (w : PlE H) :
    isoLoc N A L w = isoLoc N A L' w := by
  induction h with
  | nil => rfl
  | cons p _ ih => rw [isoLoc_cons, isoLoc_cons, ih]
  | swap p q L =>
    rw [isoLoc_cons, isoLoc_cons, isoLoc_cons, isoLoc_cons, ← A.lpSum_assoc, ← A.lpSum_assoc,
      A.lpSum_comm (spehLoc N A q w)]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem lpChar_zero (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) {w : PlE H} (χ : A.LP w)
    (hχ : A.lpDim χ = 1) : A.lpChar (A.lpZero w) χ = A.lpZero w := by
  have h1 := (hLP w (A.lpZero w) (A.lpZero w) χ χ 0 hχ hχ).1
  rw [A.lpSum_zero] at h1
  symm
  apply hC w _ _ (A.lpChar (A.lpZero w) χ)
  rw [lpSum_zero_left, ← h1]

theorem foldr_tw (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) {a : ℕ} (π : A.CG a) (χ : A.CG 1)
    (w : PlE H) {α : Type} (c : α → ℝ) (l : List α) :
    l.foldr (fun k acc => A.lpSum (A.lpTw (A.locG (A.tw π χ) w) (c k)) acc) (A.lpZero w) =
      A.lpChar (l.foldr (fun k acc => A.lpSum (A.lpTw (A.locG π w) (c k)) acc) (A.lpZero w))
        (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction l with
  | nil => exact (lpChar_zero N A hLP hC _ hd).symm
  | cons k l ih =>
    simp only [List.foldr_cons]
    rw [ih, A.locG_tw, (hLP w _ _ _ _ (c k) hd hd).1, (hLP w (A.locG π w) (A.locG π w) _ _ (c k) hd hd).2.1]

theorem spehLoc_tw (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) (p : Part A.CG) (χ : A.CG 1)
    (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  exact foldr_tw N A hLP hC p.π χ w (fun k => ((p.d : ℝ) - 1) / 2 - k) _

theorem isoLoc_twistIso (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b) (L : List (Part A.CG)) (χ : A.CG 1)
    (w : PlE H) :
    isoLoc N A (twistIso N A L χ) w = A.lpChar (isoLoc N A L w) (A.locG χ w) := by
  have hd : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction L with
  | nil => exact (lpChar_zero N A hLP hC _ hd).symm
  | cons p L ih =>
    show A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A L χ) w) = _
    rw [ih, spehLoc_tw N A hLP hC, isoLoc_cons, (hLP w _ _ _ _ 0 hd hd).1]

theorem eta_pair (w : PlE H) :
    A.lpChar (A.locG A.etaT w) (A.locG A.etaTinv w) = A.lpUnr w {1} ∧
    A.lpChar (A.locG A.etaTinv w) (A.locG A.etaT w) = A.lpUnr w {1} := by
  have hu := A.etaT_unr w
  obtain ⟨hu', hf'⟩ := A.etaTinv_def w
  have hcard := A.frobEig_card _ hu
  rw [A.locG_dim] at hcard
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 hcard
  have hb0 : b ≠ 0 := by
    intro h
    apply A.frobEig_ne_zero _ hu
    rw [hb, h]
    exact Multiset.mem_singleton_self 0
  rw [hb, Multiset.map_singleton] at hf'
  have d1 := A.locG_dim A.etaT w
  have d2 := A.locG_dim A.etaTinv w
  constructor
  · have hun := A.unr_char _ _ d2 hu hu'
    rw [A.unr_eq_lpUnr _ hun, A.frobEig_char _ _ b⁻¹ hu hu' d2 hf', hb, Multiset.map_singleton,
      mul_inv_cancel₀ hb0]
  · have hun := A.unr_char _ _ d1 hu' hu
    rw [A.unr_eq_lpUnr _ hun, A.frobEig_char _ _ b hu' hu d1 hb, hf', Multiset.map_singleton,
      inv_mul_cancel₀ hb0]

theorem lpChar_eta_inv (hLP : SumRepresentations.At.TieLP N A) {w : PlE H} (a : A.LP w) :
    A.lpChar (A.lpChar a (A.locG A.etaT w)) (A.locG A.etaTinv w) = a ∧
    A.lpChar (A.lpChar a (A.locG A.etaTinv w)) (A.locG A.etaT w) = a := by
  have d1 := A.locG_dim A.etaT w
  have d2 := A.locG_dim A.etaTinv w
  constructor
  · rw [(hLP w a a _ _ 0 d1 d2).2.2.2.1, (eta_pair N A w).1, (hLP w a a _ _ 0 d1 d2).2.2.2.2.1]
  · rw [(hLP w a a _ _ 0 d2 d1).2.2.2.1, (eta_pair N A w).2, (hLP w a a _ _ 0 d2 d1).2.2.2.2.1]

theorem tw_eta_inv (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b)
    (hAN : ∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')
    {a : ℕ} (ha : 1 ≤ a) (π : A.CG a) : A.tw (A.tw π A.etaT) A.etaTinv = π := by
  have h := hAN [⟨a, A.tw (A.tw π A.etaT) A.etaTinv, 1⟩] [⟨a, π, 1⟩]
    (by simp [ha]) (by simp [ha]) (Filter.Eventually.of_forall fun w => by
      show isoLoc N A (twistIso N A (twistIso N A [⟨a, π, 1⟩] A.etaT) A.etaTinv) w = _
      rw [isoLoc_twistIso N A hLP hC, isoLoc_twistIso N A hLP hC, (lpChar_eta_inv N A hLP _).1])
  rw [List.singleton_perm_singleton] at h
  injection h with _ h2

theorem twistIso_eta_inv (hLP : SumRepresentations.At.TieLP N A)
    (hC : ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b)
    (hAN : ∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
      (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')
    (L : List (Part A.CG)) (hL : ∀ p ∈ L, 1 ≤ p.a) :
    twistIso N A (twistIso N A L A.etaT) A.etaTinv = L := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    show (⟨p.a, A.tw (A.tw p.π A.etaT) A.etaTinv, p.d⟩ : Part A.CG) :: twistIso N A (twistIso N A L A.etaT) A.etaTinv = p :: L
    rw [ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)),
      tw_eta_inv N A hLP hC hAN (hL p List.mem_cons_self)]

theorem isBCV_of_perm {i : N.Loc} {P : A.AV i} {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa')
    (hB : IsBCV N A i P Pa) : IsBCV N A i P Pa' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB
  refine ⟨fun p hp => h1 p (h.mem_iff.2 hp), (h.map _).nodup_iff.1 h2, ?_, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_⟩
  · unfold rankIso at h3 ⊢
    rw [← (h.map _).sum_eq]
    exact h3
  · rw [← isoLoc_perm N A h]
    exact h4 w hw
  · rw [← isoLoc_perm N A h]
    exact h5 w hw
  · rw [← h6 τ]
    unfold isoInf
    exact ((h.map _).sum_eq).symm

end Gen

theorem param_of_theta (D : D7) (h0 : SumRepresentations.tie0 D) (h3 : SumRepresentations.adm3 D) (h4 : SumRepresentations.ArchimedeanSignatureMatching D) (h5 : SumRepresentations.adm5 D)
    (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG))
    (hθ : thetaOf D.nd D.naut i σ P) (hB : IsBCV D.nd D.naut i P Pa)
    (hm : (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa) :
    ∃ Sig, HasParamW D.nd D.naut i σ Sig ∧
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := h0.1
  have hC := h4.2.2
  have hAN := h5.1
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm
  set m : Part D.naut.CG := ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ with hmdef
  set L := l₁ ++ l₂ with hLdef
  have hperm : (l₁ ++ m :: l₂).Perm (L ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hLmem : ∀ p ∈ L, p ∈ l₁ ++ m :: l₂ := fun p hp => by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hL : ∀ p ∈ L, 1 ≤ p.a ∧ 1 ≤ p.d := fun p hp =>
    ⟨(hB.1 p (hLmem p hp)).1, (hB.1 p (hLmem p hp)).2.1⟩
  have hB' := isBCV_of_perm D.nd D.naut hperm hB
  refine ⟨twistIso D.nd D.naut L D.naut.etaT, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact hL q hq
  · have hr := hB'.2.2.1
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = rankIso D.nd D.naut L := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1]
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [hmdef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  · intro w hw
    have e1 := h3 i σ P hθ w hw
    rw [← hB'.2.2.2.1 w hw, isoLoc_append, (hLP w (D.naut.locW i σ w) (spehLoc D.nd D.naut (muPart D.nd D.naut i) w)
      (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) 0 (D.naut.locG_dim _ w) (D.naut.locG_dim _ w)).1]
      at e1
    have e2 : isoLoc D.nd D.naut [m] w =
        D.naut.lpChar (spehLoc D.nd D.naut (muPart D.nd D.naut i) w) (D.naut.locG D.naut.etaTinv w) := by
      rw [isoLoc_cons, isoLoc_nil, D.naut.lpSum_zero]
      exact spehLoc_tw D.nd D.naut hLP hC (muPart D.nd D.naut i) D.naut.etaTinv w
    rw [e2] at e1
    have e3 := hC w _ _ _ e1
    rw [isoLoc_twistIso D.nd D.naut hLP hC, e3, (lpChar_eta_inv D.nd D.naut hLP _).2]
  · have e : twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT ++ [muPart D.nd D.naut i])
        D.naut.etaTinv = L ++ [m] := by
      rw [show twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT ++ [muPart D.nd D.naut i])
          D.naut.etaTinv = twistIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) D.naut.etaTinv ++
            twistIso D.nd D.naut [muPart D.nd D.naut i] D.naut.etaTinv from List.map_append ..,
        twistIso_eta_inv D.nd D.naut hLP hC hAN L (fun p hp => (hL p hp).1)]
      rfl
    rw [e]
    exact hB'

end GlobalTheory.RowThetaParam
end
end

