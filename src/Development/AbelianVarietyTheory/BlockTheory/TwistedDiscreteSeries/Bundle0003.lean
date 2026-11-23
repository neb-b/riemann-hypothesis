module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DepthZeroGoodLines
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses

section Finite

variable {F : Type} [Field F] {n : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y]

end Finite

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k :=
  Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)

def red (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) 𝓀[k] :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])

def diagOne (r t : ℕ) : GL (Fin r) 𝒪[k] →* GL (Fin (r + t)) k :=
  (emb₂ k (stdSum (rfl : r + t = r + t))).comp ((MonoidHom.inl _ _).comp (incl k r))

def unipLevel (r : ℕ) : Subgroup (GL (Fin r) 𝒪[k]) := (unipB 𝓀[k] (Fin r)).comap (red k r)

variable {k} {r t n : ℕ} {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

def HasBlocks (h : GL (Fin (r + t)) 𝒪[k]) (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : Prop :=
  (∀ i j, h.val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j) ∧
  (∀ i j, h.val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j) ∧
  ∀ i j, h.val (Fin.natAdd r i) (Fin.castAdd t j) ∈ IsLocalRing.maximalIdeal 𝒪[k]

def IsDatum (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  (σ.IsIrreducible ∧ IsSmooth σ ∧ IsUnitarisable σ) ∧
    IsUnitaryChar χW ∧ IsUnitaryChar χV ∧ IsTame χW ∧ IsUnram (χW * χV⁻¹)

end Local

section Places

variable {ι : Type} [Fintype ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, ValuativeRel (k v)]
  [∀ v, TopologicalSpace (k v)] [∀ v, IsNonarchimedeanLocalField (k v)] (r : ℕ)

variable {k r}

end Places

section Examples

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isDatum_detRep (r : ℕ) {χ χW χV : kˣ →* ℂˣ} (h : IsUnram χ) (hu : IsUnitaryChar χ)
    (hW : IsUnitaryChar χW) (hV : IsUnitaryChar χV) (ht : IsTame χW) (hr : IsUnram (χW * χV⁻¹)) :
    IsDatum (detRep (Fin r) χ) χW χV :=
  ⟨⟨isIrreducible_ofChar _, (isSmooth_ofChar_iff _).2 (GlobalTheory.SmGL.isSmoothChar_of_isUnram h).detChar,
    (isUnitarisable_ofChar_iff _).2 fun _ => hu _⟩, hW, hV, ht, hr⟩

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

def sbRep {Γ X : Type} [Group Γ] [TopologicalSpace X] (r : X → Γ → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ x g h, r x (g * h) = r (r x g) h) (hc : ∀ g, Continuous fun x => r x g) :
    Representation ℂ Γ (SB X) where
  toFun g :=
    { toFun := fun f => ⟨fun x => f.1 (r x g), f.2.1.comp_continuous (hc g),
        f.2.2.comp_homeomorph
          { toFun := fun x => r x g
            invFun := fun x => r x g⁻¹
            left_inv := fun x => by simp only [← hm, mul_inv_cancel, h1]
            right_inv := fun x => by simp only [← hm, inv_mul_cancel, h1]
            continuous_toFun := hc g
            continuous_invFun := hc g⁻¹ }⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (h1 x))
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (funext fun x => congrArg f.1 (hm x g h))

section Ind

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n Γ W : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [Group Γ] [AddCommGroup W] [Module ℂ W]

def actFst (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (γ : Γ) :
    Representation.IntertwiningMap
      (MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k a b).symm.toMonoidHom)
      (MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k a b).symm.toMonoidHom) where
  toLinearMap := τ (γ, 1)
  isIntertwining' m := by
    show τ (γ, 1) * τ (1, _) = τ (1, _) * τ (γ, 1)
    rw [← map_mul, ← map_mul]
    simp

def indSnd (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) :
    Representation ℂ (Γ × GL n k)
      (IndSp (two e) (MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k a b).symm.toMonoidHom)) where
  toFun g := (parIndMap (two e) (actFst τ g.1)).toLinearMap ∘ₗ ind₂ e (τ.comp (MonoidHom.inr Γ _)) g.2
  map_one' := LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (1 : Γ × (GL a k × GL b k)) (f.1.1 (x * 1)) = f.1.1 x
    simp))
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (g.1 * h.1, 1) (f.1.1 (x * (g.2 * h.2))) = τ (g.1, 1) (τ (h.1, 1) (f.1.1 (x * g.2 * h.2)))
    rw [← Module.End.mul_apply, ← map_mul, mul_assoc]
    simp))

theorem indSnd_inr (e : a ⊕ b ≃ n) (τ : Representation ℂ (Γ × (GL a k × GL b k)) W) (h : GL n k) :
    indSnd e τ (1, h) = ind₂ e (τ.comp (MonoidHom.inr Γ _)) h :=
  LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => by
    show τ (1 : Γ × (GL a k × GL b k)) (f.1.1 (x * h)) = f.1.1 (x * h)
    simp))

end Ind

section Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def act (x : Matrix b a k) (γ : GL a k × GL b k) : Matrix b a k := (γ.2⁻¹ : GL b k).val * x * γ.1.val

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_one (x : Matrix b a k) : act x 1 = x := by simp [act]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_mul (x : Matrix b a k) (γ δ : GL a k × GL b k) : act x (γ * δ) = act (act x γ) δ := by
  simp only [act, Prod.fst_mul, Prod.snd_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem continuous_act (γ : GL a k × GL b k) : Continuous fun x : Matrix b a k => act x γ :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rank_act (x : Matrix b a k) (γ : GL a k × GL b k) : (act x γ).rank = x.rank := by
  unfold act
  rw [rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 γ.1.isUnit),
    rank_mul_eq_right_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).1 (γ.2⁻¹).isUnit)]

variable (a b)

def omChar (μ : kˣ →* ℂˣ) : GL a k × GL b k →* ℂˣ :=
  (detChar a (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2))).comp (MonoidHom.fst _ _) *
    (detChar b (μ * absPow k (-(Fintype.card a : ℂ) / 2))).comp (MonoidHom.snd _ _)

def omega (μ : kˣ →* ℂˣ) : Representation ℂ (GL a k × GL b k) (SB (Matrix b a k)) :=
  twist (sbRep act act_one act_mul continuous_act) (omChar a b μ)


variable (k) in
abbrev RankIn (s : Set ℕ) : Type := {x : Matrix b a k // x.rank ∈ s}

def omegaOn (μ : kˣ →* ℂˣ) (s : Set ℕ) : Representation ℂ (GL a k × GL b k) (SB (RankIn (k := k) (a := a) (b := b) s)) :=
  twist (sbRep (fun x γ => ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩)
    (fun x => Subtype.ext (act_one x.1)) (fun x γ δ => Subtype.ext (act_mul x.1 γ δ))
    (fun γ => ((continuous_act γ).comp continuous_subtype_val).subtype_mk _)) (omChar a b μ)

variable {a b}

theorem omegaOn_apply (μ : kˣ →* ℂˣ) (s : Set ℕ) (γ : GL a k × GL b k) (Φ : SB (RankIn (k := k) (a := a) (b := b) s))
    (x : RankIn (k := k) (a := a) (b := b) s) :
    (omegaOn a b μ s γ Φ).1 x =
      (omChar a b μ γ : ℂ) * Φ.1 ⟨act x.1 γ, by rw [rank_act]; exact x.2⟩ := rfl


variable (a b) in
def filt (μ : kˣ →* ℂˣ) (s : Set ℕ) (κ : ℕ) : Subrepresentation (omegaOn a b μ s) where
  toSubmodule :=
    { carrier := {Φ | ∀ x : RankIn (k := k) (a := a) (b := b) s, x.1.rank < κ → Φ.1 x = 0}
      add_mem' := fun {f g} hf hg x hx => by
        show f.1 x + g.1 x = 0
        rw [hf x hx, hg x hx, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun c f hf x hx => by
        show c * f.1 x = 0
        rw [hf x hx, mul_zero] }
  apply_mem_toSubmodule γ Φ hΦ x hx := by
    rw [omegaOn_apply, hΦ _ (by rwa [rank_act]), mul_zero]



end Model

section Statement

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound

def InTrivialRange (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) : Prop :=
  ∀ i, (q : ℝ) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ (q : ℝ) ^ (((n : ℝ) - 1) / 2)

def SatakeTrivialBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (α : Fin n → ℂˣ),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsSpherical π → HasSatake π α →
      InTrivialRange (resCard k) α

section Hecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

end Hecke

section Basic₂

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_lt_resCard : 1 < resCard k := Finite.one_lt_card

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsUnitaryCharacter (μ : kˣ →* ℂˣ) : Prop := IsSmoothChar μ ∧ IsUnitaryChar μ

def IsIrredUnitary {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) : Prop :=
  IsSmooth π ∧ π.IsIrreducible ∧ IsUnitarisable π

def SupportCondition {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ j : ℕ, ¬ InSupport π (μ * absPow k (((t : ℂ) + 1) / 2 + j)) ∧
    ¬ InSupport π (μ * absPow k (-(((t : ℂ) + 1) / 2 + j)))



def invTranspose (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R →* GL (Fin n) R where
  toFun h := ⟨(h⁻¹ : GL (Fin n) R).valᵀ, h.valᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin n) R)⁻¹ : GL (Fin n) R).valᵀ = 1
    rw [inv_one, Units.val_one, transpose_one]
  map_mul' x y := by
    apply Units.ext
    show ((x * y)⁻¹ : GL (Fin n) R).valᵀ = (x⁻¹ : GL (Fin n) R).valᵀ * (y⁻¹ : GL (Fin n) R).valᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul]


end GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion
end
end

