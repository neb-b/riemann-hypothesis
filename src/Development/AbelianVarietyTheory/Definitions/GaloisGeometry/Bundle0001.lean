module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans
section
set_option autoImplicit false

noncomputable section

open CategoryTheory

universe v u v' u'

namespace GlobalTheory.CatH

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{0} R)

abbrev Cn (n : ℕ) : Type (max u v) := ∀ s : ComposableArrows C n, F.obj (s.obj (Fin.last n))

def face {n : ℕ} (i : Fin (n + 2)) (s : ComposableArrows C (n + 1)) : ComposableArrows C n :=
  (Fin.succAboveOrderEmb i).monotone.functor ⋙ s

def toLast {n : ℕ} (i : Fin (n + 2)) (s : ComposableArrows C (n + 1)) :
    (face i s).obj (Fin.last n) ⟶ s.obj (Fin.last (n + 1)) :=
  s.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))

def d (n : ℕ) : Cn F n →ₗ[R] Cn F (n + 1) where
  toFun f s := ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s))
  map_add' f g := by
    funext s
    simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def Bn : ∀ n : ℕ, Submodule R (Cn F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (d F n)

abbrev H (n : ℕ) : Type (max u v) := LinearMap.ker (d F n) ⧸ (Bn F n).submoduleOf (LinearMap.ker (d F n))

variable {F} {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C'] {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'}

structure Mor (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R') (σ : R →+* R') where

  G : C' ⥤ C

  τ : ∀ T : C', F.obj (G.obj T) →ₛₗ[σ] F'.obj T
  nat : ∀ {T T' : C'} (φ : T ⟶ T') (x : F.obj (G.obj T)), τ T' ((F.map (G.map φ)).hom x) = (F'.map φ).hom (τ T x)

namespace Mor

def id (F : C ⥤ ModuleCat.{0} R) : Mor F F (RingHom.id R) where
  G := 𝟭 C
  τ _ := LinearMap.id
  nat _ _ := rfl

def restrict (F : C ⥤ ModuleCat.{0} R) (G : C' ⥤ C) : Mor F (G ⋙ F) (RingHom.id R) where
  G := G
  τ _ := LinearMap.id
  nat _ _ := rfl

def ofNatTrans {F₁ : C ⥤ ModuleCat.{0} R} (α : F ⟶ F₁) : Mor F F₁ (RingHom.id R) where
  G := 𝟭 C
  τ T := (α.app T).hom
  nat φ x := by
    change ((F.map φ ≫ α.app _).hom) x = ((α.app _ ≫ F₁.map φ).hom) x
    rw [α.naturality]

variable (m : Mor F F' σ)

def pullC (n : ℕ) : Cn F n →ₛₗ[σ] Cn F' n where
  toFun f s := m.τ _ (f (s ⋙ m.G))
  map_add' f g := funext fun s => map_add (m.τ _) _ _
  map_smul' r f := funext fun s => LinearMap.map_smulₛₗ (m.τ _) _ _

theorem d_pullC (n : ℕ) (f : Cn F n) : d F' n (m.pullC n f) = m.pullC (n + 1) (d F n f) := by
  funext s
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F'.map (toLast i s)).hom (m.τ _ (f (face i s ⋙ m.G))) =
    m.τ _ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (m.G.map (toLast i s))).hom (f (face i s ⋙ m.G)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, m.nat]

def pullZ (n : ℕ) : LinearMap.ker (d F n) →ₛₗ[σ] LinearMap.ker (d F' n) :=
  ((m.pullC n).domRestrict _).codRestrict _ fun f => by
    change d F' n (m.pullC n f.1) = 0
    rw [m.d_pullC, f.2, map_zero]

def pull (n : ℕ) : H F n →ₛₗ[σ] H F' n :=
  Submodule.mapQ _ _ (m.pullZ n) (by
    intro f hf
    change m.pullC n f.1 ∈ Bn F' n
    have hf' : f.1 ∈ Bn F n := hf
    cases n with
    | zero =>
      have : f.1 = 0 := hf'
      rw [this, map_zero]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨g, hg⟩ := hf'
      exact ⟨m.pullC n g, by rw [m.d_pullC, hg]⟩)

end Mor

end GlobalTheory.CatH
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

def ideal (S : Finset ι) : X.IdealSheafData := ⨆ i ∈ S, I i

theorem le_ideal {S : Finset ι} {i : ι} (h : i ∈ S) : I i ≤ ideal I S :=
  le_iSup₂ (f := fun i (_ : i ∈ S) => I i) i h

theorem ideal_mono {S S' : Finset ι} (h : S ⊆ S') : ideal I S ≤ ideal I S' :=
  iSup₂_le fun _ hi => le_ideal I (h hi)

def Y (S : Finset ι) : Scheme.{0} := (ideal I S).subscheme

def Yι (S : Finset ι) : Y I S ⟶ X := (ideal I S).subschemeι

def incl {S S' : Finset ι} (h : S ⊆ S') : Y I S' ⟶ Y I S :=
  Scheme.IdealSheafData.inclusion (ideal_mono I h)

abbrev Idx (ι : Type) (s : ℕ) : Type := {S : Finset ι // S.card = s + 1}

def Ystr (s : ℕ) : Scheme.{0} := ∐ fun S : Idx ι s => Y I S.1

def inj {s : ℕ} (S : Idx ι s) : Y I S.1 ⟶ Ystr I s := Sigma.ι (fun S : Idx ι s => Y I S.1) S

section Face

variable [LinearOrder ι]

def face {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : Idx ι s :=
  ⟨S.1.erase (S.1.orderEmbOfFin S.2 j), by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), S.2]; rfl⟩

theorem face_subset {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : (face S j).1 ⊆ S.1 :=
  Finset.erase_subset _ _

def δ (s : ℕ) (j : Fin (s + 2)) : Ystr I (s + 1) ⟶ Ystr I s :=
  Sigma.desc fun S : Idx ι (s + 1) => incl I (face_subset S j) ≫ inj I (face S j)

end Face

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section Fibre

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

end Fibre

section BaseChange

variable {X' : Scheme.{0}} (f : X' ⟶ X)

end BaseChange

theorem nonempty_Ystr {s : ℕ} (S : Idx ι s) (y : Y I S.1) : Nonempty (Ystr I s) := ⟨(inj I S).base y⟩

theorem isEmpty_Ystr {s : ℕ} (h : IsEmpty (Idx ι s)) : IsEmpty (Ystr I s) :=
  ⟨fun x => IsEmpty.false ((Sigma.desc (fun S : Idx ι s => (isEmptyElim S : Y I S.1 ⟶ ∅)) : Ystr I s ⟶ ∅).base x)⟩

theorem nonempty_Y_iff (S : Finset ι) : Nonempty (Y I S) ↔ ((ideal I S).support : Set X).Nonempty := by
  rw [← Set.range_nonempty_iff_nonempty (f := (Yι I S).base)]
  unfold Yι
  rw [← Scheme.IdealSheafData.range_subschemeι]
  rfl

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section FibreStr

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

end FibreStr

section BaseChangeStr

variable {X' : Scheme.{0}} (f : X' ⟶ X)

end BaseChangeStr

end GlobalTheory.Strata

namespace GlobalTheory.Strata.Example

open MvPolynomial

variable (O : Type) [CommRing O] (ϖ : O)

abbrev A : Type := MvPolynomial (Fin 2) O ⧸ Ideal.span {X 0 * X 1 - C ϖ}

def T (k : Fin 2) : A O ϖ := Ideal.Quotient.mk _ (X k)

abbrev XS : Scheme.{0} := Spec (CommRingCat.of (A O ϖ))

def compIdeal (k : Fin 2) : (XS O ϖ).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of (A O ϖ))).inv.hom (T O ϖ k)})

def red : A O ϖ →+* O ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.lift _ (eval₂Hom (Ideal.Quotient.mk _) (fun _ => 0)) (by
    intro a ha
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self])

theorem reduction_uniformizerPoint (k : Fin 2) : red O ϖ (T O ϖ k) = 0 := by simp [red, T]

theorem mem_support_compIdeal (x : XS O ϖ) (k : Fin 2) (hx : T O ϖ k ∈ x.asIdeal) :
    x ∈ ((compIdeal O ϖ k).support : Set (XS O ϖ)) := by
  rw [compIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton,
    basicOpen_eq_of_affine]
  exact fun h' => (PrimeSpectrum.mem_basicOpen (x := (x : PrimeSpectrum (A O ϖ))) _).1 h' hx

theorem isEmpty_Ystr_two : IsEmpty (Ystr (compIdeal O ϖ) 2) :=
  isEmpty_Ystr _ ⟨fun S => by have := S.1.card_le_univ; have h2 := S.2; simp at this; omega⟩

theorem nonempty_Ystr_one (h : ¬ IsUnit ϖ) : Nonempty (Ystr (compIdeal O ϖ) 1) := by
  haveI : Nontrivial (O ⧸ Ideal.span {ϖ}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (O ⧸ Ideal.span {ϖ})
  let x : XS O ϖ := ⟨M.comap (red O ϖ), Ideal.comap_isPrime _ _⟩
  have hx : x ∈ ((ideal (compIdeal O ϖ) Finset.univ).support : Set (XS O ϖ)) := by
    simp only [ideal, Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf, Set.mem_iInter]
    intro k _
    refine mem_support_compIdeal O ϖ x k ?_
    show red O ϖ (T O ϖ k) ∈ M
    rw [reduction_uniformizerPoint]; exact zero_mem _
  obtain ⟨y⟩ := (nonempty_Y_iff (compIdeal O ϖ) Finset.univ).2 ⟨x, hx⟩
  exact nonempty_Ystr (compIdeal O ϖ) (s := 1) ⟨Finset.univ, by simp⟩ y

end GlobalTheory.Strata.Example

namespace GlobalTheory.Strata

theorem orderEmbOfFin_univ_fin {n : ℕ} (h : (Finset.univ : Finset (Fin n)).card = n) :
    ((Finset.univ : Finset (Fin n)).orderEmbOfFin h : Fin n → Fin n) = id :=
  (Finset.orderEmbOfFin_unique h (f := id) (fun _ => Finset.mem_univ _) strictMono_id).symm

end GlobalTheory.Strata
end
end

