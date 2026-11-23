module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
section
noncomputable section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix
open scoped TensorProduct Classical
namespace GlobalTheory.LKRes.Model
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem sigKQ_inclK (r : ℕ) (a : K) : sigKQ p K r (inclK p K r a) = inclK p K r a := by
  change Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) = a ⊗ₜ[ℚ_[p]] (1 : Qr p r)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem sigKQ_inclQ (r : ℕ) (b : Qr p r) : sigKQ p K r (inclQ p K r b) = inclQ p K r (frobQ p r b) := by
  change Algebra.TensorProduct.map (AlgHom.id ℚ_[p] K) (frobQ p r) ((1 : K) ⊗ₜ[ℚ_[p]] b) = (1 : K) ⊗ₜ[ℚ_[p]] frobQ p r b
  rw [Algebra.TensorProduct.map_tmul, map_one]

theorem frobQ_norm (r : ℕ) (b : Qr p r) : ‖((frobQ p r b : Qr p r) : PadicAlgCl p)‖ = ‖(b : PadicAlgCl p)‖ :=
  norm_map_GK p (Q0 p) (frobK p (Q0 p)) b

theorem frobQ_intR (r : ℕ) (b : Qr p r) (hb : b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r) :
    frobQ p r b ∈ GlobalTheory.LKLoc.intR p (Q0 p) r := by
  simp only [GlobalTheory.LKLoc.intR, Subring.mem_comap] at *
  have := (mem_Obar_iff (p := p)).1 hb
  exact (mem_Obar_iff (p := p)).2 (by
    show ‖((frobQ p r b : Qr p r) : PadicAlgCl p)‖ ≤ 1
    rw [frobQ_norm]; exact this)

theorem sigKQ_intKQ (r : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) : sigKQ p K r x ∈ intKQ p K r := by
  have : intKQ p K r ≤ (intKQ p K r).comap (sigKQ p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [sigKQ_inclK]; exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [sigKQ_inclQ]; exact Subring.subset_closure (Or.inr ⟨⟨_, frobQ_intR p r b.1 b.2⟩, rfl⟩)
  exact this hx

theorem sigRes_Kres (n r : ℕ) (g : GL (Fin n) (KQ p K r)) (hg : g ∈ Kres p K n r) :
    sigRes p K n r g ∈ Kres p K n r := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨GeneralLinearGroup.map ((sigKQ p K r).toRingHom.restrict (intKQ p K r) (intKQ p K r)
    (fun x hx => sigKQ_intKQ p K r x hx)) h, ?_⟩
  ext i j
  simp [sigRes, GeneralLinearGroup.map]

def mulMap (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] PadicAlgCl p :=
  Algebra.TensorProduct.productMap K.val (Qr p r).val

theorem mulMap_intKQ (r : ℕ) (x : KQ p K r) (hx : x ∈ intKQ p K r) : ‖mulMap p K r x‖ ≤ 1 := by
  have : intKQ p K r ≤ (Obar p).toSubring.comap (mulMap p K r).toRingHom := by
    refine (Subring.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (mulMap p K r (a.1 ⊗ₜ[ℚ_[p]] (1 : Qr p r))) ∈ Obar p
      show (a.1 : PadicAlgCl p) * 1 ∈ Obar p
      rw [mul_one]; exact a.2
    · simp only [SetLike.mem_coe, Subring.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      change (mulMap p K r ((1 : K) ⊗ₜ[ℚ_[p]] b.1)) ∈ Obar p
      show 1 * (b.1 : PadicAlgCl p) ∈ Obar p
      rw [one_mul]; exact b.2
  exact (mem_Obar_iff (p := p)).1 (this hx)

theorem sigHT_KHT (m n r : ℕ) (Kw : Fin m → IntermediateField ℚ_[p] (PadicAlgCl p)) (g : GHT p m n r Kw)
    (hg : g ∈ KHT p m n r Kw) : sigHT p m n r Kw g ∈ KHT p m n r Kw := by
  refine ⟨?_, fun i hi => sigRes_Kres p (Kw i) n r _ (hg.2 i hi)⟩
  obtain ⟨h, e⟩ := hg.1
  refine ⟨GeneralLinearGroup.map ((frobQ p r).toRingHom.restrict (GlobalTheory.LKLoc.intR p (Q0 p) r)
    (GlobalTheory.LKLoc.intR p (Q0 p) r) (fun x hx => frobQ_intR p r x hx)) h, ?_⟩
  show _ = GlobalTheory.LKLoc.sig p (Q0 p) 1 r g.1
  rw [← e]
  ext i j
  rfl

end GlobalTheory.LKRes.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory

namespace GlobalTheory.JSW.WhitModel

open GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem mem_NA_iff (u : GA E a) : u ∈ NA (E := E) (a := a) ↔ ∃ X : Pos a → Ad E, u = uGL X := by
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun p => (u : Matrix (Fin a) (Fin a) (Ad E)) p.1.1 p.1.2, Units.ext ?_⟩
    refine Matrix.ext fun i j => ?_
    rw [coe_uGL, uMat_apply]
    split_ifs with h h'
    · subst h; exact h1 i
    · rfl
    · exact h0 i j (lt_of_le_of_ne (not_lt.1 h') (Ne.symm h))
  · rintro ⟨X, rfl⟩
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · rw [coe_uGL, uMat_apply, if_neg (ne_of_gt h), dite_eq_right (not_lt.2 h.le)]
    · rw [coe_uGL, uMat_apply, if_pos rfl]

theorem superDiag_uGL (X : Pos a → Ad E) : GlobalTheory.Whittaker.superDiag (uGL X) = supSum 0 X := by
  classical
  unfold GlobalTheory.Whittaker.superDiag supSum
  refine (Finset.sum_sigma' _ _ _).trans ?_
  symm
  refine Finset.sum_bij (fun p _ => ⟨p.1.1, p.1.2⟩) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp.1]
  · intro p _ q _ h
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  · rintro ⟨i, j⟩ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact ⟨⟨(i, j), by rw [Fin.lt_def]; simp only; omega⟩, by simp [h], rfl⟩
  · intro p _
    simp only [coe_uGL, uMat_apply]
    rw [if_neg (ne_of_lt p.2), dite_eq_left p.2]

theorem whit_mul {F : GA E a → ℂ} (hc : Continuous F) (hl : AutomorphicForm.IsLeftInvariant F) {u : GA E a}
    (hu : u ∈ NA (E := E) (a := a)) (g : GA E a) : whit F (u * g) = psiN u * whit F g := by
  obtain ⟨X, rfl⟩ := (mem_NA_iff u).1 hu
  rw [psiN, superDiag_uGL]
  exact MultiplicityOne.whittaker_uGL_mul hc hl X g

theorem psiLoc_eq (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    psiLoc w x = (GroundTheory.Global.localAdelicChar E w x : ℂ) := by
  classical
  rw [psiLoc, GroundTheory.Global.localAdelicChar_apply]
  congr 2

theorem loc_mem_supS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) (w.adicCompletion E)) : finGL E a (locGL E a w g) ∈ supS (E := E) (a := a) S ↔ w ∈ S ∨ g = 1 := by
  have hc : ∀ v, ∀ g : GA E a, GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) g) := fun _ _ => rfl
  constructor
  · intro h
    by_cases hw : w ∈ S
    · exact Or.inl hw
    · have := h w hw
      rw [hc, pFin_finGL, pLoc_locGL] at this
      exact Or.inr this
  · rintro (h | rfl) v hv
    · rw [hc, pFin_finGL, pLoc_locGL_of_ne (fun e : v = w => hv (by rw [e]; exact h))]
    · simp

variable [_root_.NumberField.IsTotallyComplex E]

end GlobalTheory.JSW.WhitModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure Core5 (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  thP : R.IsThP

theorem Core5.of_core {R : RealDat D A Ks} {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : Core5 R F :=
  ⟨h.lev, h.grp, h.fam, h.models, h.thP⟩

end GlobalTheory

end
end

