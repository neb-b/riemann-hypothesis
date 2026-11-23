module

public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.LocalToDisplayFree
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

def LocalToDisplay (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (Z : Set X) (p : X' → X) (d : Type) [Fintype d] [DecidableEq d]
    (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsNoetherian R' R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
    (π' : X') (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ), Function.Injective colIdx →
    ∀ (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → R')
      (k0 : ι → G → R'),
    (∀ x', p x' ∉ Z →
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : G, ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ L : Submodule (FractionRing O) (D (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l))) ≤ L ∧
        (∀ a, ∀ s ∈ LinearMap.range
            (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁),
          (fun g : D (colIdx l) => Kc l a g • s) ∈ L) ∧
        (∀ s ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E),
          (fun g : D (colIdx l) => k0 l g • s) ∈ L) ∧
        Module.rank (FractionRing O)
            (L ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))).comap
              L.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))) : ℕ))) →
    ∀ (g₀ : ℕ)
      (n : Fin g₀ → ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0),
      Submodule.span R' (Set.range n) = ⊤ →
      ((g₀ * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
    ∀ (ℓ cB : ℕ) (what₂ qs : Finset ℕ)
      (deg : ℕ → ℕ) (s vhE H0 : ℕ∞) (Sha : ℕ → ℕ∞),
      (∀ l g, ∃ a : R', k0 l g = a * E) →
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ (D w)))
    ∀ (L : Type) [AddCommGroup L] [Module R' L] [Module O L]
      (tens : L →ₗ[O] KO O →ₗ[O] blockRestrictedRepresentationType bl ρk 0) (v₁ : L) (κ : ∀ l, Fin (j (colIdx l)) → G → L)
      (HcG : ∀ c, Submodule O (H1z (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)))
      (Hc F : ∀ c w, Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (D w))))
      (Vo VS : Type) (Io : Vo → Subgroup G) (IS : VS → Subgroup G) (ε : G →* Oˣ)
      (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
      (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] R')
      (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O) (lam : blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O)
      (Cs : ℕ → Type) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
      (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc 0 w →ₗ[O] Cs w →ₗ[O] KO O)
      (Fs Im : ∀ w, Submodule O (Cs w))
      (cT : Fin (t + 1) → ℕ → ℕ) (I : ∀ w, Subgroup (D w)) (γQ : ∀ w, D w) (ζ : ℕ → Tc)
      (ζO : ℕ → O) (nQ : ∀ w, D w → ℕ) (u : ι → G → O),
    InRho (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ (HcG 0) (Hc 0) (F 0)
      Io ε ρ₁ ρ₂ inc π γ lam cls pr Fs Im →
    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ (D w))) ≤ H0) ∧
      InChi (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg (cT c)
        (Sha ((c : ℕ) - 1)) (HcG c) (Hc c) (F c) Io IS I γQ ζ ζO nQ) →
    (let c1 : Fin (t + 1) := ⟨1, by omega⟩
     (∀ l, ∀ g ∈ D (colIdx l), ∀ m : blockRestrictedRepresentationType bl ρk c1,
       k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * u l g) • m) ∧
     (∀ l, ∀ g ∈ I (colIdx l), u l (g : G) = 0) ∧ (∀ l, ∃ g ∈ D (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) (D (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     InChi (blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg (cT c1) vhE
       (HcG c1) (Hc c1) (F c1) Io IS I γQ ζ ζO nQ) →
    vcc T Z (p π') ≤
      ∑ w ∈ what₂, Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype) +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1)

def LocalToDisplayFree (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (Z : Set X) (p : X' → X) (d : Type) [Fintype d] [DecidableEq d]
    (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsNoetherian R' R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
    (π' : X') (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ), Function.Injective colIdx →
    ∀ (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → R')
      (k0 : ι → G → R'),
    (∀ x', p x' ∉ Z →
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : G, ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ L : Submodule (FractionRing O) (D (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l))) ≤ L ∧
        (∀ a, ∀ s ∈ LinearMap.range
            (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁),
          (fun g : D (colIdx l) => Kc l a g • s) ∈ L) ∧
        (∀ s ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E),
          (fun g : D (colIdx l) => k0 l g • s) ∈ L) ∧
        Module.rank (FractionRing O)
            (L ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))).comap
              L.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))) : ℕ))) →
    ∀ (ℓ cB : ℕ) (what₂ qs : Finset ℕ)
      (deg : ℕ → ℕ) (s vhE H0 : ℕ∞) (Sha : ℕ → ℕ∞),
      (∀ l g, ∃ a : R', k0 l g = a * E) →
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ (D w)))
    ∀ (L : Type) [AddCommGroup L] [Module R' L] [Module O L]
      (tens : L →ₗ[O] KO O →ₗ[O] blockRestrictedRepresentationType bl ρk 0) (v₁ : L) (κ : ∀ l, Fin (j (colIdx l)) → G → L)
      (HcG : ∀ c, Submodule O (H1z (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)))
      (Hc F : ∀ c w, Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (D w))))
      (Vo VS : Type) (Io : Vo → Subgroup G) (IS : VS → Subgroup G) (ε : G →* Oˣ)
      (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
      (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] R')
      (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O) (lam : blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O)
      (Cs : ℕ → Type) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
      (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc 0 w →ₗ[O] Cs w →ₗ[O] KO O)
      (Fs Im : ∀ w, Submodule O (Cs w))
      (cT : Fin (t + 1) → ℕ → ℕ) (I : ∀ w, Subgroup (D w)) (γQ : ∀ w, D w) (ζ : ℕ → Tc)
      (ζO : ℕ → O) (nQ : ∀ w, D w → ℕ) (u : ι → G → O),
    InRho (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ (HcG 0) (Hc 0) (F 0)
      Io ε ρ₁ ρ₂ inc π γ lam cls pr Fs Im →
    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ (D w))) ≤ H0) ∧
      InChi (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg (cT c)
        (Sha ((c : ℕ) - 1)) (HcG c) (Hc c) (F c) Io IS I γQ ζ ζO nQ) →
    (let c1 : Fin (t + 1) := ⟨1, by omega⟩
     (∀ l, ∀ g ∈ D (colIdx l), ∀ m : blockRestrictedRepresentationType bl ρk c1,
       k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * u l g) • m) ∧
     (∀ l, ∀ g ∈ I (colIdx l), u l (g : G) = 0) ∧ (∀ l, ∃ g ∈ D (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) (D (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     InChi (blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg (cT c1) vhE
       (HcG c1) (Hc c1) (F c1) Io IS I γQ ζ ζO nQ) →
    vcc T Z (p π') ≤
      ∑ w ∈ what₂, Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype) +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RightIdealImageOfSurjective
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

def StatOntoSpan : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n] [DecidableEq n] (G : Type)
    [Monoid G] (ρ : G →* Matrix n n O), AbsIrr (fun g => (ρ g).map (IsLocalRing.residue O)) →
    Submodule.span O (Set.range ρ) = ⊤

def StatNoeth : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X' : Type) [Finite X']
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O))),
    (∀ a ∈ R', ∀ x' i j, ∃ c : O, algebraMap O (FractionRing O) c = a x' i j) → IsNoetherian R' R'

def StatEMat : Prop :=
  ∀ (K : Type) [Field K] (d : Type) [Fintype d] [DecidableEq d] (e x : Matrix d d K) (t : ℕ)
    (α : ℕ → K), 1 ≤ t → e * e = e → e * x = x → x * e = x →
    blockPoly e x = ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α i)) →
    (∀ i j, i < t → j < t → α i = α j → i = j) →
    let E := e * ((List.range t).tail.map fun i => x - α i • e).prod
    E * E = (∏ i ∈ Finset.Ioo 0 t, (α 0 - α i)) • E ∧ E.rank = 1 ∧ x * E = α 0 • E ∧
      e * E = E ∧ E * e = E ∧ (∏ i ∈ Finset.Ioo 0 t, (α 0 - α i)) ≠ 0

def StatIdemKO : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : Type) [Fintype n]
    [DecidableEq n] (e : Matrix n n O), e * e = e →
    (e.map (algebraMap O (FractionRing O))).rank = 1 →
    Nonempty (↥(LinearMap.range (matEnd O (KO O) n e)) ≃ₗ[O] KO O)

def SplitPts {O X : Type} [CommRing O] (t : ℕ) (P : X → Polynomial O) : Type :=
  {y : X × (Fin t → O) // P y.1 = ∏ i, (Polynomial.X - Polynomial.C (y.2 i))}

def splitRoot {O X : Type} [CommRing O] (t : ℕ) (P : X → Polynomial O) (i : Fin t) :
    SplitPts t P → O := fun y => y.1.2 i

def splitT {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (t : ℕ) (P : X → Polynomial O) :
    Subalgebra O (SplitPts t P → O) :=
  Algebra.adjoin O ({f' | ∃ f ∈ T, f' = fun y => f y.1.1} ∪ Set.range (splitRoot t P))

def StatSplitPts : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (X : Type) (T : Subalgebra O (X → O)) (t : ℕ)
    (P : X → Polynomial O), (∀ k, (fun x => (P x).coeff k) ∈ T) →
    (∀ x, ∃ α : Fin t → O, Function.Injective α ∧
      P x = ∏ i, (Polynomial.X - Polynomial.C (α i))) →
    ∃ b : Fin t.factorial → (SplitPts t P → O),
      (∀ k, b k ∈ splitT T t P) ∧
      (∀ f' ∈ splitT T t P, ∃ a : Fin t.factorial → (X → O), (∀ k, a k ∈ T) ∧
        f' = ∑ k, (fun y => a k y.1.1) * b k) ∧
      (∀ x, ∀ a : Fin t.factorial → O,
        (∀ y : SplitPts t P, y.1.1 = x → ∑ k, a k * b k y = 0) → a = 0)

def StatRootsInt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (P : Polynomial O) (t : ℕ)
    (α : Fin t → FractionRing O),
    P.map (algebraMap O (FractionRing O)) = ∏ i, (Polynomial.X - Polynomial.C (α i)) →
    ∃ β : Fin t → O, (∀ i, algebraMap O (FractionRing O) (β i) = α i) ∧
      P = ∏ i, (Polynomial.X - Polynomial.C (β i))

def BlockRingDecompositionLemma : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X d G : Type)
    [Fintype d] [DecidableEq d] [Group G] (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (T : Subalgebra O (X → O)) (D : RingData O X d G t bl) [IsNoetherian D.R' D.R']
    [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)], D.Top T ht →
    ∀ (Z : Set X) (NN : Type) [AddCommGroup NN] [Module D.R' NN] (g₀ : ℕ) (n : Fin g₀ → NN),
      Submodule.span D.R' (Set.range n) = ⊤ →
      (∀ x', D.p x' ∉ Z → ∃ φ : NN →ₗ[D.R'] EvalSp O d D.R' x', φ ≠ 0) →
      ((g₀ * Fintype.card d : ℕ) : Cardinal) < Cardinal.mk (IsLocalRing.ResidueField O) →
      vcc T Z (D.p D.π') ≤ ∑ k : Fin (t + 1), Module.length O (NN →ₗ[D.R'] blockRestrictedRepresentationType bl D.ρk k)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

