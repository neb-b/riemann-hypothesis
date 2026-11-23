module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows
open scoped ContDiff

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CutOff

section Row

variable {R : Type} [CommRing R] {k : ℕ}

def eRow (R : Type) [CommRing R] (k : ℕ) : Fin k → R := fun c => if (c : ℕ) + 1 = k then 1 else 0

def lastEnt (r : Fin k → R) : R := ∑ c : Fin k, if (c : ℕ) + 1 = k then r c else 0

def lastRowM (A : Matrix (Fin k) (Fin k) R) : Fin k → R := fun c => ∑ i : Fin k, if (i : ℕ) + 1 = k then A i c else 0

def rowM (r : Fin k → R) : Matrix (Fin k) (Fin k) R :=
  Matrix.of fun i c => if (i : ℕ) + 1 = k then r c else (1 : Matrix (Fin k) (Fin k) R) i c

def rowI (r : Fin k → R) : Fin k → R :=
  fun c => if (c : ℕ) + 1 = k then Ring.inverse (lastEnt r) else -(r c * Ring.inverse (lastEnt r))

theorem rowM_apply_last (r : Fin k → R) (i c : Fin k) (h : (i : ℕ) + 1 = k) : rowM r i c = r c := by
  simp [rowM, h]

theorem rowM_apply_ne (r : Fin k → R) (i c : Fin k) (h : (i : ℕ) + 1 ≠ k) :
    rowM r i c = (1 : Matrix (Fin k) (Fin k) R) i c := by
  simp [rowM, h]

theorem lastEnt_eq (r : Fin k → R) (l : Fin k) (hl : (l : ℕ) + 1 = k) : lastEnt r = r l := by
  rw [lastEnt, Finset.sum_eq_single l]
  · simp [hl]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · simp

theorem rowM_mul_rowM (r t : Fin k → R) (l : Fin k) (hl : (l : ℕ) + 1 = k) (i c : Fin k) :
    (rowM r * rowM t) i c = if (i : ℕ) + 1 = k then
      (if (c : ℕ) + 1 = k then r l * t c else r c + r l * t c) else rowM t i c := by
  have hlast : ∀ j : Fin k, (j : ℕ) + 1 = k → j = l := fun j hj => Fin.ext (by omega)
  by_cases hi : (i : ℕ) + 1 = k
  · rw [if_pos hi, Matrix.mul_apply]
    have e : ∀ j, rowM r i j * rowM t j c =
        r j * (if j = l then t c else (1 : Matrix (Fin k) (Fin k) R) j c) := fun j => by
      rw [rowM_apply_last r i j hi]
      by_cases hj : j = l
      · subst hj; rw [rowM_apply_last t _ c hl, if_pos rfl]
      · rw [rowM_apply_ne t j c (fun h => hj (hlast j h)), if_neg hj]
    simp only [e]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    have e2 : ∀ j ∈ Finset.univ.erase l, r j * (if j = l then t c else (1 : Matrix (Fin k) (Fin k) R) j c) =
        if j = c then r j else 0 := fun j hj => by
      rw [if_neg (Finset.ne_of_mem_erase hj), Matrix.one_apply]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e2, if_pos rfl, Finset.sum_ite_eq' ]
    by_cases hc : (c : ℕ) + 1 = k
    · have : c = l := hlast c hc
      subst this
      simp [hc]
    · have : c ≠ l := fun h => hc (h ▸ hl)
      simp [hc, this, add_comm]
  · rw [if_neg hi, Matrix.mul_apply]
    simp only [rowM_apply_ne r i _ hi, Matrix.one_apply]
    simp

variable {r : Fin k → R}

theorem rowM_mul_rowI (h : IsUnit (lastEnt r)) : rowM r * rowM (rowI r) = 1 := by
  ext i c
  by_cases hk : ∃ l : Fin k, (l : ℕ) + 1 = k
  · obtain ⟨l, hl⟩ := hk
    have hu : r l * Ring.inverse (r l) = 1 := by
      rw [← lastEnt_eq r l hl] at *
      exact Ring.mul_inverse_cancel _ h
    rw [rowM_mul_rowM _ _ l hl]
    have e : Ring.inverse (lastEnt r) = Ring.inverse (r l) := by rw [lastEnt_eq r l hl]
    by_cases hi : (i : ℕ) + 1 = k
    · have hil : i = l := Fin.ext (by omega)
      subst hil
      by_cases hc : (c : ℕ) + 1 = k
      · have hcl : c = i := Fin.ext (by omega)
        subst hcl
        simp only [if_pos hl, rowI, e, Matrix.one_apply, if_true]
        exact hu
      · have hcl : i ≠ c := fun h => hc (h ▸ hl)
        simp only [if_pos hl, if_neg hc, rowI, e, Matrix.one_apply, if_neg hcl]
        linear_combination (- r c) * hu
    · rw [if_neg hi, rowM_apply_ne _ _ _ hi]
  · exact absurd ⟨⟨k - 1, by have := i.2; omega⟩, by have := i.2; simp; omega⟩ hk

theorem rowI_mul_rowM (h : IsUnit (lastEnt r)) : rowM (rowI r) * rowM r = 1 := by
  ext i c
  by_cases hk : ∃ l : Fin k, (l : ℕ) + 1 = k
  · obtain ⟨l, hl⟩ := hk
    have hu : r l * Ring.inverse (r l) = 1 := by
      rw [← lastEnt_eq r l hl] at *
      exact Ring.mul_inverse_cancel _ h
    rw [rowM_mul_rowM _ _ l hl]
    have e : Ring.inverse (lastEnt r) = Ring.inverse (r l) := by rw [lastEnt_eq r l hl]
    have el : rowI r l = Ring.inverse (r l) := by simp [rowI, hl, e]
    by_cases hi : (i : ℕ) + 1 = k
    · have hil : i = l := Fin.ext (by omega)
      subst hil
      by_cases hc : (c : ℕ) + 1 = k
      · have hcl : c = i := Fin.ext (by omega)
        subst hcl
        simp only [if_pos hl, el, Matrix.one_apply, if_true]
        linear_combination hu
      · have hcl : i ≠ c := fun h => hc (h ▸ hl)
        simp only [if_pos hl, if_neg hc, el, Matrix.one_apply, if_neg hcl]
        simp only [rowI, if_neg hc, e]
        ring
    · rw [if_neg hi, rowM_apply_ne _ _ _ hi]
  · exact absurd ⟨⟨k - 1, by have := i.2; omega⟩, by have := i.2; simp; omega⟩ hk


open Classical in
def rowGL (r : Fin k → R) : GL (Fin k) R :=
  if h : IsUnit (lastEnt r) then ⟨rowM r, rowM (rowI r), rowM_mul_rowI h, rowI_mul_rowM h⟩ else 1

theorem rowGL_val (h : IsUnit (lastEnt r)) : (rowGL r).val = rowM r := by
  simp [rowGL, h]

theorem rowGL_inv_val (h : IsUnit (lastEnt r)) : ((rowGL r)⁻¹).val = rowM (rowI r) := by
  simp [rowGL, h]

theorem lastEnt_eRow (hk : 1 ≤ k) : lastEnt (eRow R k) = 1 := by
  rw [lastEnt_eq _ ⟨k - 1, by omega⟩ (by simp; omega)]
  simp [eRow]; omega

theorem rowM_eRow : rowM (eRow R k) = 1 := by
  ext i c
  by_cases hi : (i : ℕ) + 1 = k
  · rw [rowM_apply_last _ _ _ hi, eRow, Matrix.one_apply]
    by_cases hc : (c : ℕ) + 1 = k
    · rw [if_pos hc, if_pos (Fin.ext (by omega))]
    · rw [if_neg hc, if_neg (fun h : i = c => hc (h ▸ hi))]
  · rw [rowM_apply_ne _ _ _ hi]

theorem rowGL_eRow (hk : 1 ≤ k) : rowGL (eRow R k) = 1 := by
  by_cases h : IsUnit (lastEnt (eRow R k))
  · exact Units.ext ((rowGL_val h).trans rowM_eRow)
  · simp [rowGL, h]

theorem lastRow_mul_rowGL_inv (A : GL (Fin k) R) (h : IsUnit (lastEnt r)) (hA : lastRowM A.val = r) :
    Mir (k - 1) (A * (rowGL r)⁻¹) := by
  intro i j hij
  have hi : (i : ℕ) + 1 = k := by have := i.2; have := j.2; omega
  have e1 : ∀ m, A.val i m = rowM r i m := fun m => by
    rw [rowM_apply_last _ _ _ hi, ← hA, lastRowM, Finset.sum_eq_single i]
    · rw [if_pos hi]
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext (by omega))
    · simp
  have e2 : (A * (rowGL r)⁻¹).val i j = (rowM r * rowM (rowI r)) i j := by
    rw [Units.val_mul, rowGL_inv_val h, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun m _ => by rw [e1]
  rw [e2, rowM_mul_rowI h]

end Row

section Adelic

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

def latS (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)) : AddSubgroup (Af E) where
  carrier := {a | (∀ w, w ∉ S → pLoc E w a ∈ Formalism.UG.Ov E w) ∧ ∀ w ∈ S, pLoc E w a ∈ B w}
  add_mem' := fun {a b} ha hb => ⟨fun w hw => by
      rw [map_add (pLoc E w)]
      exact add_mem (ha.1 w hw) (hb.1 w hw), fun w hw => by
      rw [map_add (pLoc E w)]
      exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
  zero_mem' := ⟨fun w _ => by rw [map_zero]; exact zero_mem _, fun w _ => by rw [map_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun w hw => by
      rw [map_neg]; exact neg_mem (ha.1 w hw), fun w hw => by
      rw [map_neg]; exact neg_mem (ha.2 w hw)⟩


variable (E k) in
def nuFin : Measure (Fin k → Af E) := Measure.pi fun _ => GroundTheory.Global.finiteAdeleMeasure E

def boxL (L : Set (Af E)) (c : Fin k → Af E) : Set (Fin k → Af E) := {f | ∀ i, f i - c i ∈ L}

variable [_root_.NumberField.IsTotallyComplex E]


variable (E k) in
def nuInf : Measure (Fin k → Cinf E) :=
  (Measure.pi fun _ => GroundTheory.Global.infiniteAdeleMeasure E).map fun y i => (infEq E).symm (y i)

def glue (S : Finset (Pl E)) (a : GL (Fin k) (Cinf E)) (u : ∀ w : Pl E, GL (Fin k) (w.adicCompletion E)) : GA E k :=
  (S.toList.map fun w => fl k w (u w)).prod * infGL E k a

def sOf (S : Finset (Pl E)) (y : Fin k → Ad E) : GA E k :=
  glue S (rowGL fun i => pInf E (y i)) fun w => rowGL fun i => pLoc E w (pFin E (y i))

def etaOf (b : (Fin k → Cinf E) → ℝ) (L : Set (Af E)) (y : Fin k → Ad E) : ℝ :=
  b (fun i => pInf E (y i)) * (boxL L (eRow (Af E) k)).indicator (fun _ => 1) fun i => pFin E (y i)

end Adelic

end GlobalTheory.CompanionTheory.CutOff
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbLeviProjMemKm
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.KmIwahori

open GlobalTheory.CompanionTheory.HeckeJacquet (mem_Km_iff val_unif_lt_one)
open GlobalTheory.LocGL.IwahoriFactor (one_same one_ne)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_mem_Km {N m : ℕ} (hm : 1 ≤ m) {M : Matrix (Fin N) (Fin N) k}
    (h : ∀ i j, valuation k (M i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
      valuation k (((Zls.unifU k : kˣ) : k) ^ m)) :
    ∃ g ∈ Zls.Km k N m, g.val = M := by
  have hlt : valuation k (((Zls.unifU k : kˣ) : k) ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' (val_unif_lt_one k) (by omega)
  obtain ⟨g, -, hg⟩ := GlobalTheory.StepData.exists_mem_KOne (k := k) (n := Fin N) (M := M)
    fun i j => by
      rw [Matrix.sub_apply]
      exact (h i j).trans_lt hlt
  exact ⟨g, (mem_Km_iff N hm g).2 (by rw [hg]; exact h), hg⟩

variable {α : Type} {μ : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (μ a)]
  [∀ a, DecidableEq (μ a)]

theorem exists_mul_mem_parab {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ c ∈ Zls.Km k N m ⊓ unipRadLower k e, x * c ∈ parab k e := by
  have hx' := (mem_Km_iff N hm x).1 hx
  have hA : ∀ a : α, ∃ y ∈ Zls.Km k N m, y.val =
      Matrix.of fun i l => if a < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l := fun a =>
    exists_mem_Km hm fun i l => by
      simp only [Matrix.of_apply]
      split_ifs
      · exact hx' i l
      · simp
  choose y hy hyv using hA
  obtain ⟨c, hc, hcv⟩ := exists_mem_Km hm (M := Matrix.of fun i j => (y (blk e j))⁻¹.val i j)
    fun i j => (mem_Km_iff N hm _).1 (inv_mem (hy (blk e j))) i j
  have key : ∀ i j, ∑ l, (if blk e j < blk e i then x.val i l else (1 : Matrix (Fin N) (Fin N) k) i l) *
      c.val l j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j => by
    have := congrFun (congrFun (y (blk e j)).mul_inv i) j
    rw [Matrix.mul_apply, hyv] at this
    rw [hcv]
    exact this
  have h1 : ∀ i j, blk e i ≤ blk e j → c.val i j = (1 : Matrix (Fin N) (Fin N) k) i j := fun i j h => by
    have := key i j
    simp only [if_neg h.not_gt] at this
    rwa [← Matrix.mul_apply, Matrix.one_mul] at this
  refine ⟨c, ⟨hc, (mem_unipRadLower k).2 ⟨(mem_parabLower_iff k).2 fun a b i j h => ?_, fun a i j => ?_⟩⟩,
    mem_parab_iff.2 fun a b i j h => ?_⟩
  · rw [h1 _ _ (by simpa using h.le), one_ne e h.ne]
  · rw [h1 _ _ (by simp), one_same]
  · have := key (e ⟨a, i⟩) (e ⟨b, j⟩)
    simp only [blk_apply, if_pos h] at this
    rw [Units.val_mul, Matrix.mul_apply, this, one_ne e h.ne']

theorem leviEmb_leviProj_mem_Km {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) (p : parab k e)
    (hp : (p : GL (Fin N) k) ∈ Zls.Km k N m) :
    leviEmb k e (leviProj k e p) ∈ Zls.Km k N m := by
  refine (mem_Km_iff N hm _).2 fun i j => ?_
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    have := (mem_Km_iff N hm _).1 hp (e ⟨a, i⟩) (e ⟨a, j⟩)
    simpa [leviEmb, Matrix.blockDiagonal'_apply_eq] using this
  · have hz : ((leviEmb k e (leviProj k e p) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
      simp [leviEmb, Matrix.blockDiagonal'_apply, h]
    rw [hz, one_ne e h]
    simp

theorem exists_factor {N m : ℕ} (hm : 1 ≤ m) (e : (Σ a, μ a) ≃ Fin N) {x : GL (Fin N) k}
    (hx : x ∈ Zls.Km k N m) :
    ∃ a ∈ Zls.Km k N m ⊓ unipRadLower k e, ∃ b ∈ Zls.Km k N m ⊓ (leviEmb k e).range,
      ∃ c ∈ Zls.Km k N m ⊓ unipRad k e, x = a * b * c := by
  obtain ⟨c, hc, hp⟩ := exists_mul_mem_parab hm e (inv_mem hx)
  have hq : (x⁻¹ * c)⁻¹ ∈ parab k e := inv_mem hp
  have hqK : (x⁻¹ * c)⁻¹ ∈ Zls.Km k N m := inv_mem (mul_mem (inv_mem hx) hc.1)
  have hs : ∀ (g : Levi k μ) a (i j : μ a),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
        (g a : Matrix (μ a) (μ a) k) i j := by
    intro g a i j
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  have hn : ∀ (g : Levi k μ) {a b : α}, a ≠ b → ∀ (i : μ a) (j : μ b),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b h i j
    simp [leviEmb, Matrix.blockDiagonal'_apply, h]
  let p : parab k e := ⟨_, hq⟩
  have hL : leviEmb k e (leviProj k e p) ∈ parab k e :=
    mem_parab_iff.2 fun a b i j h => hn _ h.ne' i j
  let L : parab k e := ⟨_, hL⟩
  have hproj : leviProj k e L = leviProj k e p := by
    funext a
    ext i j
    simp only [leviProj_apply]
    exact hs _ _ _ _
  have hu : ((L⁻¹ * p : parab k e) : GL (Fin N) k) ∈ unipRad k e := by
    change ((L⁻¹ * p : parab k e) : GL (Fin N) k) ∈ (leviProj k e).ker.map (parab k e).subtype
    refine ⟨L⁻¹ * p, MonoidHom.mem_ker.2 ?_, rfl⟩
    rw [map_mul, map_inv, hproj, inv_mul_cancel]
  let u : GL (Fin N) k := ((L⁻¹ * p : parab k e) : GL (Fin N) k)
  have hqu : (x⁻¹ * c)⁻¹ = leviEmb k e (leviProj k e p) * u := by
    change (p : GL (Fin N) k) = (L : GL (Fin N) k) * ((L⁻¹ * p : parab k e) : GL (Fin N) k)
    simp
  have hd := leviEmb_leviProj_mem_Km hm e ⟨_, hq⟩ hqK
  refine ⟨c, hc, _, ⟨hd, ⟨_, rfl⟩⟩, u, ⟨?_, hu⟩, ?_⟩
  · have : u = (leviEmb k e (leviProj k e ⟨_, hq⟩))⁻¹ * (x⁻¹ * c)⁻¹ := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hqu.symm
    show u ∈ Zls.Km k N m
    rw [this]
    exact mul_mem (inv_mem hd) hqK
  · rw [mul_assoc, ← hqu]
    group

theorem c0 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    PositivityTheory.Lbc.C0 k := by
  intro k _ _ _ _ N m h d hd hm
  exact ⟨GlobalTheory.CompanionTheory.HeckeKm.isOpen_Km N m, GlobalTheory.CompanionTheory.HeckeKm.isCompact_Km N m,
    fun x hx => exists_factor hm (stdBlocks d hd) hx⟩

end GlobalTheory.CompanionTheory.KmIwahori

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateFieldStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_bridge_lubin_tate_field : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | exact GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | (intros; apply GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormInfinitePlaceBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_infinite_place_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (w : InfinitePlace F) (e : EmbOver E w) (u : J → E) (δ : (w.Completion ⊗[F] E)ˣ) (z : J → w.Completion ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : w.Completion) ⊗ₜ[F] u f) * δ.1) → (∀ f, ‖infEmb e (z f)‖₊ ≤ c) →
    GlobalTheory.Doubling.absEw F E w δ * locInf w u ≤ c ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le | exact GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateUnramifiedDegreeOneStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_unramified_degree_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {Ωv : Type} [Field Ωv] [ValuativeRel Ωv] [TopologicalSpace Ωv] [IsValuativeTopology Ωv]
    [Algebra F Ωv] [ValuativeExtension F Ωv] [IsSepClosure F Ωv] [IsSepClosed Ωv]
    {π : 𝒪[F]} (hπ : Irreducible π) {f : PowerSeries 𝒪[F]} (hf : IsLubinTateSeries π f)
    (u : 𝒪[F]ˣ) (τ : Ωv ≃ₐ[F] Ωv), unramifiedDegree F Ωv τ = 1 →
    (∀ n, ∀ x ∈ lubinTateTorsion Ωv (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = (u : 𝒪[F]) • x) →
    ∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension F Ωv),
    ((localArtinMap F Ωv (unitsIncl F u⁻¹) ⟨y, hy⟩ : maximalAbelianExtension F Ωv) : Ωv) = τ y := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia | exact GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia | (intros; apply GlobalTheory.CompanionTheory.LTLink.lt_local_artin_inertia <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticIntegralCoefficientsBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_integral_coefficients_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : E, ∃ y₁ y₂ : F,
    x ^ 2 - algebraMap F E y₁ * x + algebraMap F E y₂ = 0 ∧ ∀ (v : Pl (F := F)) (τ : E →ₐ[F] FvBar F v),
      ‖algebraMap F (Fv F v) y₁‖₊ ≤ max (absBar F v (τ x)) (absBar F v (τ (σ x))) ∧
      ‖algebraMap F (Fv F v) y₂‖₊ = absBar F v (τ x) * absBar F v (τ (σ x)) := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes | exact GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes | (intros; apply GlobalTheory.CompanionTheory.GodementH.trace_norm_local_sizes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactEntriesIntegralStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_compact_entries_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)),
    IsStdK (σ := σ) (Y := Y) B b K → ∀ k ∈ K, ∀ (v : Pl (F := F)) (i j : Fin n ⊕ Fin n), absFin F v (compFin F E v (inFrame b k i j)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one | exact GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one | (intros; apply GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one <;> assumption)
end

