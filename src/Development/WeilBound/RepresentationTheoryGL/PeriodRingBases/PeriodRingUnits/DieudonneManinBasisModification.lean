module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.DeRhamPotentiallySemistable.DeRhamTwists.ContinuousCyclotomicCharacter
public import Mathlib
public import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite
public import GroundTheory.PAdicHodge.FundamentalSeqBCris
public import GroundTheory.PAdicHodge.Bundle0003

@[expose] public section

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

variable (l : ℕ) [Fact l.Prime]

abbrev GQ : Type := PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l

abbrev Fld : Type := IntermediateField ℚ_[l] (PadicAlgCl l)

abbrev B : Type := Bcris l

def φ : B l →+* B l := φB l

theorem isUnit_iC_l : IsUnit (iC l (l : ACris.ACris ℂ_[l] l)) := by
  rw [map_natCast, ← map_natCast (qQ l)]
  exact (IsUnit.mk0 (l : ℚ_[l]) (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)).map _

theorem isUnit_image_period : IsUnit (iC l (tA l)) := IsUnit.mk0 _ DeRhamTwist.Twist.tQ_ne

def ι : B l →+* BdR l := Loc2.lift (iC l) (isUnit_iC_l l) (isUnit_image_period l)

theorem isUnit_l : IsUnit (l : B l) := by
  rw [← map_natCast (cB l)]
  exact Loc2.isUnit_left _ _

theorem isUnit_zB (z : nonZeroDivisors ℤ_[l]) : IsUnit (zB l z) := by
  have hz : (z : ℤ_[l]) ≠ 0 := nonZeroDivisors.coe_ne_zero z
  rw [PadicInt.unitCoeff_spec hz, map_mul, map_pow, map_natCast]
  exact ((PadicInt.unitCoeff hz).isUnit.map _).mul ((isUnit_l l).pow _)

def qB : ℚ_[l] →+* B l := IsLocalization.lift (M := nonZeroDivisors ℤ_[l]) (isUnit_zB l)

def t : B l := cB l (tA l)

def aB : AInf ℂ_[l] l →+* B l := (cB l).comp (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l))

def Ainf' : Subring (B l) := Subring.closure (Set.range (aB l) ∪ {qB l ((l : ℚ_[l])⁻¹)})

def Plus : Subring (BdR l) := (algebraMap (BdRp l) (BdR l)).range


open Classical in
def th (x : BdR l) : ℂ_[l] := if h : x ∈ Plus l then θD l (RingHom.mem_range.1 h).choose else 0

variable {l}

def σB (g : GQ l) : B l →+* B l := Formalism.Per6.σB g

def σC (g : GQ l) : ℂ_[l] ≃+* ℂ_[l] := galCp (toBot g)

def χ (g : GQ l) : ℚ_[l] := ((DeRhamTwist.Twist.chi0 l g : ℤ_[l]) : ℚ_[l])

def κ (g : GQ l) : ℚ_[l] :=
  (kummerC (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one (toBot g) : ℤ_[l])

def Eig (h : ℕ) (m : ℤ) (x : B l) : Prop := (φ l ^ h) x = qB l ((l : ℚ_[l]) ^ m) * x

structure Base (l : ℕ) [Fact l.Prime] : Prop where
  dom : IsDomain (B l)
  ι_inj : Function.Injective (ι l)
  σ_one : σB (1 : GQ l) = RingHom.id _
  σ_mul : ∀ g h : GQ l, σB (g * h) = (σB g).comp (σB h)
  σD_one : ∀ x, σD (1 : GQ l) x = x
  σD_mul : ∀ (g h : GQ l) x, σD (g * h) x = σD g (σD h x)
  σC_one : ∀ x, σC (1 : GQ l) x = x
  σC_mul : ∀ (g h : GQ l) x, σC (g * h) x = σC g (σC h x)
  φ_σ : ∀ (g : GQ l) x, φ l (σB g x) = σB g (φ l x)
  ι_σ : ∀ (g : GQ l) x, ι l (σB g x) = σD g (ι l x)
  φ_q : ∀ q, φ l (qB l q) = qB l q
  σ_q : ∀ (g : GQ l) q, σB g (qB l q) = qB l q
  ι_q : ∀ q, ι l (qB l q) = qQ l q
  ι_t : ι l (t l) = tQ l
  t_unit : IsUnit (t l)
  frobenius_period : φ l (t l) = (l : B l) * t l
  galois_t_transform : ∀ g : GQ l, σB g (t l) = qB l (χ g) * t l
  σ_u : ∀ g : GQ l, σD g (uQ l) = uQ l + qQ l (κ g) * tQ l
  κ_mul : ∀ g h : GQ l, κ (g * h) = κ g + χ g * κ h
  κ_cont : Continuous (κ : GQ l → ℚ_[l])
  χ_cont : Continuous (χ : GQ l → ℚ_[l])
  ι_Bst : ∀ x, ι l x ∈ Bst l
  u_Bst : uQ l ∈ Bst l
  plus_σ : ∀ (g : GQ l) x, x ∈ Plus l → σD g x ∈ Plus l
  th_σ : ∀ (g : GQ l) x, x ∈ Plus l → th l (σD g x) = σC g (th l x)
  th_add : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x + y) = th l x + th l y
  th_mul : ∀ x ∈ Plus l, ∀ y ∈ Plus l, th l (x * y) = th l x * th l y
  th_q : ∀ q, qQ l q ∈ Plus l ∧ th l (qQ l q) = algebraMap ℚ_[l] ℂ_[l] q
  th_zero : ∀ x ∈ Plus l, (th l x = 0 ↔ ∃ y ∈ Plus l, x = tQ l * y)
  t_plus : tQ l ∈ Plus l
  val : ∀ x : BdR l, x ≠ 0 → ∃ (i : ℤ) (u v : BdR l), u ∈ Plus l ∧ v ∈ Plus l ∧ u * v = 1 ∧ x = tQ l ^ i * u
  orbit : ∀ x : ℂ_[l], Continuous fun g : GQ l => σC g x
  fs_ker : ∀ x, φ l x = x → ι l x ∈ Plus l → ∃ q, x = qB l q
  fs_surj : ∀ z : BdR l, ∃ x, φ l x = x ∧ ι l x - z ∈ Plus l
  ainf_φ : ∀ x ∈ Ainf' l, φ l x ∈ Ainf' l
  ainf_σ : ∀ (g : GQ l), ∀ x ∈ Ainf' l, σB g x ∈ Ainf' l
  ainf_plus : ∀ x ∈ Ainf' l, ι l x ∈ Plus l
  ainf_eig : ∀ (h : ℕ) (m : ℤ), m ≠ 0 → ∀ x ∈ Ainf' l, Eig h m x → x = 0
  fixed : ∀ L : Fld l, FiniteDimensional ℚ_[l] L → ∃ (f : ℕ) (b : Fin f → B l),
    (∀ i, b i ∈ Ainf' l ∧ ∀ σ ∈ L.fixingSubgroup, σB σ (b i) = b i) ∧
    ∀ x, (∀ σ ∈ L.fixingSubgroup, σB σ x = x) → ∃ q : Fin f → ℚ_[l], x = ∑ i, qB l (q i) * b i
  no_kummer : ∀ L : Fld l, FiniteDimensional ℚ_[l] L → ∀ x : B l,
    ¬ ∀ σ ∈ L.fixingSubgroup, σB σ x - x = qB l (κ σ) * t l

def PeriodRingBase : Prop := ∀ (l : ℕ) [Fact l.Prime], Base l

end period_ring_base
