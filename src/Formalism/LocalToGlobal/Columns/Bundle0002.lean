module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Formalism.LocalToGlobal.HermitianForms.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.CoefCol
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section GLmat

variable (E : Type) [Field E] (n : ℕ)

def toGLm : (Sp E n ≃ₗ[E] Sp E n) ≃* GL (Fin n) E :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E (Sp E n)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

def ufGL [StarRing E] : UF E n →* GL (Fin n) E := (toGLm E n).toMonoidHom.comp (UF E n).subtype

end GLmat

structure CoefPk (X : Fields) (n : ℕ) (D : Type) where

  lam : X.Tau → DomWeight n

  rho : UF X.E n →* Module.End X.K (VV X.K lam)

  pair : VV X.K lam →ₗ⋆[X.K] VV X.K lam →ₗ[X.K] X.K

  Nab : D → Submodule (𝓞 X.K) (VV X.K lam)

  Del : D → Submodule (𝓞 X.K) (VV X.K lam)

namespace CoefPk

variable {X : Fields} {n : ℕ} {D : Type} (C : CoefPk X n D)

abbrev V : Type := VV X.K C.lam

def bV : Basis (VVIdx C.lam) X.K C.V := bVV X.K C.lam

def pull {D' : Type} (e : D' → D) : CoefPk X n D' where
  lam := C.lam
  rho := C.rho
  pair := C.pair
  Nab d' := C.Nab (e d')
  Del d' := C.Del (e d')

end CoefPk

section Pk

variable (X : Fields) {n : ℕ}

def roundPk (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n)) : CoefPk X n D where
  lam := lam
  rho := (rhoVr X.emb lam).comp (ufGL X.E n)
  pair := pairVr X.emb lam 1
  Nab d := nabAtr X.emb lam (L d)
  Del d := delAtr X.emb lam (L d)

def squarePk (lam : X.Tau → DomWeight n) {D : Type} (L : D → Submodule (𝓞 X.E) (Sp X.E n)) : CoefPk X n D where
  lam := lam
  rho := (rhoV X.emb lam).comp (ufGL X.E n)
  pair := pairV X.emb lam 1
  Nab d := nabAt X.emb lam (L d)
  Del d := delAt X.emb lam (L d)

end Pk

section DecoKer

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.LshKer (d : Deco E n ST SG) (P : ST) : Submodule (𝓞 E) (Sp E n) :=
  Submodule.span (𝓞 E) {x | x ∈ d.Lsh ∧ d.f P x = 0}

end DecoKer

section Vals

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def colVal (u : Pr.Word) (j : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    CoefPk X (R.N j) (DecoSet (E := X.E) (n := R.N j) (ST := ST) (SG := SG)) :=
  roundPk X (W.lamTrue u j) fun d => d.1.Lsh

def rowVal (SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    CoefPk X (R.N R.m - 1) (DecoSet (E := X.E) (n := R.N R.m - 1) (ST := ∅) (SG := SG)) :=
  squarePk X W.sgTrue fun d => d.1.N

def mtVal (j : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    CoefPk X R.nV (DecoSet (E := X.E) (n := R.nV) (ST := ∅) (SG := SG)) :=
  roundPk X (W.lamV j) fun d => d.1.N

def BvLat (u : Pr.Word) (j : ℕ) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (P : ST) (d : DecoSet (E := X.E) (n := R.N j) (ST := ST) (SG := SG)) : Submodule (𝓞 X.K) (VV X.K (W.lamTrue u j)) :=
  delAtr X.emb (W.lamTrue u j) (d.1.LshKer P)

end Vals

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.MtRowRep
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace Formalism.L2.Col

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def finTypSetoid (Occ : Set (NG.FinTyp L n)) : Setoid Occ where
  r π π' := π.1.Iso π'.1
  iseqv := ⟨fun π => NG.IsoRep.refl _, fun {π _} h => NG.IsoRep.symm π.1.stable h, fun h h' => NG.IsoRep.trans h h'⟩

abbrev FinTypCls (Occ : Set (NG.FinTyp L n)) : Type := Quotient (finTypSetoid Occ)

def finTypRep (Occ : Set (NG.FinTyp L n)) (c : FinTypCls Occ) : NG.FinTyp L n := (Quotient.out c).1

theorem finTypRep_mem (Occ : Set (NG.FinTyp L n)) (c : FinTypCls Occ) : finTypRep Occ c ∈ Occ := (Quotient.out c).2

theorem finTypRep_inj {Occ : Set (NG.FinTyp L n)} {c c' : FinTypCls Occ}
    (h : (finTypRep Occ c).Iso (finTypRep Occ c')) : c = c' := by
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  exact Quotient.sound h

theorem finTypRep_mk_iso {Occ : Set (NG.FinTyp L n)} (π : Occ) :
    (finTypRep Occ (Quotient.mk (finTypSetoid Occ) π)).Iso π.1 :=
  Quotient.mk_out (s := finTypSetoid Occ) π

end Gen

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedGlMat
section
open Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.Forms (blkOf entN InJ blkMat)

theorem glm_blkIdx {t : ℕ} (ht : 0 < t) (j x : ℕ) : blkIdx (List.replicate j t) x = min (x / t) j := by
  induction j generalizing x with
  | zero => simp [blkIdx]
  | succ j ih =>
    simp only [List.replicate_succ, blkIdx]
    split_ifs with h
    · rw [Nat.div_eq_of_lt h]; omega
    · have hx : x / t = (x - t) / t + 1 := Nat.div_eq_sub_div ht (by omega)
      rw [ih, hx]; omega

section Grp

variable {κ k' : Type} [CommRing κ] [Field k'] {n : ℕ}

end Grp

section Chr

variable {κ k' K : Type} [CommRing κ] [Field k'] [Field K] {n : ℕ}

def glmPsi (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) : AddChar k' ℂ where
  toFun x := σ₀ (ψ (e.symm x))
  map_zero_eq_one' := by rw [map_zero, AddChar.map_zero_eq_one, map_one]
  map_add_eq_mul' x y := by rw [map_add (f := _), AddChar.map_add_eq_mul, map_mul]

theorem glmPsi_apply (e : κ ≃+* k') (σ₀ : K →+* ℂ) (ψ : AddChar κ K) (x : κ) : glmPsi e σ₀ ψ (e x) = σ₀ (ψ x) := by
  show σ₀ (ψ (e.symm (e x))) = σ₀ (ψ x)
  rw [e.symm_apply_apply]


open Classical in
def glmChi (e : κ ≃+* k') (σ₀ : K →+* ℂ) (χ : κˣ →* Kˣ) : MulChar k' ℂ :=
  MulChar.ofUnitHom ((Units.map σ₀.toMonoidHom).comp (χ.comp (Units.map e.symm.toRingHom.toMonoidHom)))

theorem glmChi_apply (e : κ ≃+* k') (σ₀ : K →+* ℂ) (χ : κˣ →* Kˣ) (x : κˣ) :
    glmChi e σ₀ χ (e (x : κ)) = σ₀ ((χ x : Kˣ) : K) := by
  have h : e (x : κ) = ((Units.map e.toRingHom.toMonoidHom x : k'ˣ) : k') := rfl
  rw [h]
  unfold glmChi
  rw [MulChar.ofUnitHom_coe]
  have h2 : (Units.map e.symm.toRingHom.toMonoidHom) (Units.map e.toRingHom.toMonoidHom x) = x := by
    ext
    simp
  simp only [MonoidHom.comp_apply, h2]
  rfl

def equalBlockPositionsEquiv {a t j s : ℕ} (ht : 0 < t) (hs : s < j) (hn : a + j * t ≤ n) :
    Fin t ≃ {i : Fin n // coarse a (List.replicate j t) i.val = s + 1} where
  toFun c := ⟨⟨a + s * t + c, by
      have h1 : (s + 1) * t ≤ j * t := Nat.mul_le_mul_right t hs
      have := c.2
      rw [Nat.add_mul, Nat.one_mul] at h1
      omega⟩, by
    show coarse a (List.replicate j t) (a + s * t + c) = s + 1
    rw [coarse_of_le (by omega), glm_blkIdx ht]
    have h2 : (a + s * t + c - a) / t = s := by
      rw [show a + s * t + c - a = c + t * s by rw [Nat.mul_comm t s]; omega, Nat.add_mul_div_left _ _ ht,
        Nat.div_eq_of_lt c.2, Nat.zero_add]
    rw [h2]; omega⟩
  invFun i := ⟨i.1.val - (a + s * t), by
    have h := i.2
    have ha : a ≤ i.1.val := by
      by_contra hlt
      rw [coarse_of_lt (Nat.not_le.1 hlt)] at h
      omega
    rw [coarse_of_le ha, glm_blkIdx ht] at h
    have h3 : (i.1.val - a) / t = s := by omega
    have h4 := Nat.div_add_mod (i.1.val - a) t
    have h5 := Nat.mod_lt (i.1.val - a) ht
    rw [h3, Nat.mul_comm] at h4
    omega⟩
  left_inv c := by
    apply Fin.ext
    show a + s * t + c - (a + s * t) = c
    omega
  right_inv i := by
    apply Subtype.ext
    apply Fin.ext
    show a + s * t + (i.1.val - (a + s * t)) = i.1.val
    have h := i.2
    have ha : a ≤ i.1.val := by
      by_contra hlt
      rw [coarse_of_lt (Nat.not_le.1 hlt)] at h
      omega
    rw [coarse_of_le ha, glm_blkIdx ht] at h
    have h3 : (i.1.val - a) / t = s := by omega
    have h4 := Nat.div_add_mod (i.1.val - a) t
    rw [h3, Nat.mul_comm] at h4
    omega

theorem glm_blkDet (e : κ ≃+* k') {a t j s : ℕ} (ht : 0 < t) (hs : s < j) (hn : a + j * t ≤ n)
    (M : ↥(blockUT n κ a (List.replicate j t))) :
    e ((blkDet n κ (coarse a (List.replicate j t)) (s + 1) M : κˣ) : κ) =
      (blkMat a t s ((M.1 : Matrix (Fin n) (Fin n) κ).map e)).det := by
  have hA : ((blkDet n κ (coarse a (List.replicate j t)) (s + 1) M : κˣ) : κ) =
      ((M.1 : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => coarse a (List.replicate j t) i.val) (s + 1)).det := rfl
  rw [hA, RingEquiv.map_det, RingEquiv.mapMatrix_apply]
  refine (Matrix.det_submatrix_equiv_self (equalBlockPositionsEquiv ht hs hn) _).symm.trans (congrArg Matrix.det ?_)
  ext c d
  have hc : a + s * t + (c : ℕ) < n := ((equalBlockPositionsEquiv ht hs hn) c).1.isLt
  have hd : a + s * t + (d : ℕ) < n := ((equalBlockPositionsEquiv ht hs hn) d).1.isLt
  simp only [blkMat, entN, dif_pos (And.intro hc hd)]
  rfl

end Chr

end Formalism.L2.Col
end
end

