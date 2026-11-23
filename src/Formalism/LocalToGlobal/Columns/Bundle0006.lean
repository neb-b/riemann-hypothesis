module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.AtTLemmas
public import Formalism.LocalToGlobal.Columns.HeckeInert
public import Formalism.LocalToGlobal.Columns.GSetLemmas
public import Formalism.LocalToGlobal.Columns.UnipotentRightActionFunctionsW
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Formalism.LocalToGlobal.Columns.TiedRec
public import Formalism.LocalToGlobal.HermitianForms.FormsTied

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.AtTOwedU
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem SameAt.symm {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N') :
    SameAt Q N' N := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  exact ⟨a', ha', a, ha, h2, h1⟩

theorem SameAt.trans {Q : HeightOneSpectrum (𝓞 E)} {N N' N'' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (h' : SameAt Q N' N'') : SameAt Q N N'' := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  obtain ⟨b, hb, b', hb', k1, k2⟩ := h'
  refine ⟨a * b, fun hm => (Q.isPrime.mem_or_mem hm).elim ha hb, b' * a',
    fun hm => (Q.isPrime.mem_or_mem hm).elim hb' ha', fun x hx => ?_, fun x hx => ?_⟩
  · rw [mul_smul]
    exact h1 _ (k1 _ hx)
  · rw [mul_smul]
    exact k2 _ (h2 _ hx)

theorem SameAt.sup {Q : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)} (h : SameAt Q N N')
    (S : Submodule (𝓞 E) (Sp E n)) : SameAt Q (N ⊔ S) (N' ⊔ S) := by
  obtain ⟨a, ha, a', ha', h1, h2⟩ := h
  refine ⟨a, ha, a', ha', fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h1 y hy) (S.smul_mem a hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    exact Submodule.add_mem_sup (h2 y hy) (S.smul_mem a' hz)

end Loc

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.DiamondPreservesRamified
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Moves

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}


theorem Deco.L_dia (d : Deco E n ST SG) (c : DiaG (E := E) (ST := ST)) : (d.dia c).L = d.L := by
  unfold Deco.L
  congr 1
  ext x
  show (x ∈ d.N ∧ ∀ P : ST, (c P).1 * d.f P x = 0) ↔ (x ∈ d.N ∧ ∀ P : ST, d.f P x = 0)
  simp only [Units.mul_right_eq_zero]

theorem Deco.Lsh_dia (d : Deco E n ST SG) (c : DiaG (E := E) (ST := ST)) : (d.dia c).Lsh = d.Lsh := by
  unfold Deco.Lsh
  rw [Deco.L_dia]

end Moves

section Ops

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Ops

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end Cols

section Adj

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Adj

section AtW

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end AtW

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.HeckeInertLemmas
section
noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module Pointwise

section Fin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem DecoSet.inertSet_finite {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    (d.inertSet P s).Finite := by
  have hPk : P ^ s.sum ≠ ⊥ := pow_ne_zero _ hP
  obtain ⟨a, haP, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPk
  have hI : Ideal.span {a} * P ^ s.sum ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨fun h => ha (Ideal.span_singleton_eq_bot.1 h), hPk⟩
  have hfin := finite_between ((Ideal.span {a} * P ^ s.sum) • d.1.N) d.1.N
    (finite_quot_smul d.1.N d.2.lat.fg _ hI)
  refine Set.Finite.of_injOn (f := fun e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) => Ideal.span {a} • e.1.N) ?_ ?_ hfin
  · intro e he
    obtain ⟨h1, h2⟩ := he.1.smul_le
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact Submodule.smul_mono le_rfl h1
    · exact (Submodule.smul_mono ((Ideal.span_singleton_le_iff_mem _).2 haP) le_rfl).trans h2
  · intro e he e' he' h
    have hN : e.1.N = e'.1.N := by
      simp only [Submodule.ideal_span_singleton_smul] at h
      have hinj : Function.Injective fun x : Sp E n => a • x := smul_right_injective (Sp E n) ha
      have hsub : ∀ A B : Submodule (𝓞 E) (Sp E n), a • A = a • B → A ≤ B := by
        intro A B hAB x hx
        have : a • x ∈ a • B := hAB ▸ Submodule.smul_mem_pointwise_smul x a A hx
        obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 this
        rwa [← hinj hyx]
      exact le_antisymm (hsub _ _ h) (hsub _ _ h.symm)
    exact Subtype.ext (Deco.ext hN (he.2.1.trans he'.2.1.symm) (he.2.2.trans he'.2.2.symm))

theorem DecoSet.mem_inertNb {P : Ideal (𝓞 E)} (hP : P ≠ ⊥) (s : List ℕ) (d e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) :
    e ∈ d.inertNb P s ↔ e ∈ d.inertSet P s := by
  unfold DecoSet.inertNb
  rw [dite_eq_left (DecoSet.inertSet_finite hP s d), Set.Finite.mem_toFinset]

theorem DecoSet.sum_inertNb_smul {M : Type} [AddCommMonoid M] (P : Ideal (𝓞 E)) (s : List ℕ)
    (g : UF E n × GLG (E := E) (n := n) (SG := SG)) (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (ψ : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) → M) :
    ∑ e ∈ (g • d).inertNb P s, ψ e = ∑ e ∈ d.inertNb P s, ψ (g • e) := by
  symm
  exact Finset.sum_equiv (MulAction.toPerm g) (fun e => (DecoSet.smul_mem_inertNb_iff g).symm) (fun e _ => rfl)

end Fin

section Op

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

end Op

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_asAlgebraHom_eq (a : MonoidAlgebra K A) : ρ.asAlgebraHom a = ∑ t : A, a.coeff t • ρ t := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  simp [Finsupp.sum_fintype]

theorem rf_coord_act (t : A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ t φ) = ((S.toCSD h).actMat (S.repCSD h ρ) t).mulVec (S.coordOf h S.outSec φ) := by
  have c : ∀ x, S.coordOf h S.outSec x = (S.toCSD h).basis.equivFun (S.res h x) := fun x => rfl
  have e1 : (S.repCSD h ρ) t (S.res h φ) = S.res h (ρ t φ) := by
    show (S.res h) (ρ t ((S.res h).symm (S.res h φ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [c, c]
  unfold CSD.actMat
  simp only [Basis.equivFun_apply]
  rw [LinearMap.toMatrix_mulVec_repr, e1]

theorem rf_coord_ga (a : MonoidAlgebra K A) (φ : S.EqFun) :
    S.coordOf h S.outSec (ρ.asAlgebraHom a φ) =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVec (S.coordOf h S.outSec φ) := by

  have hsum : ∀ {m : ℕ} (M : A → Matrix (Fin m) (Fin m) K) (c : A → K) (v : Fin m → K),
      (∑ t, c t • M t).mulVec v = ∑ t, c t • (M t).mulVec v := by
    intro m M c v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Matrix.toLin'_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [rf_asAlgebraHom_eq, LinearMap.sum_apply, map_sum]
  unfold CSD.gaMat
  rw [hsum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [LinearMap.smul_apply, map_smul, rf_coord_act]

theorem rf_range_ga (a : MonoidAlgebra K A) :
    (LinearMap.range (ρ.asAlgebraHom a)).map (S.coordOf h S.outSec).toLinearMap =
      LinearMap.range ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin := by
  have e : (S.coordOf h S.outSec).toLinearMap ∘ₗ ρ.asAlgebraHom a =
      ((S.toCSD h).gaMat (S.repCSD h ρ) a).mulVecLin ∘ₗ (S.coordOf h S.outSec).toLinearMap := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    exact rf_coord_ga S h ρ a φ
  rw [← LinearMap.range_comp, e, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

private theorem range_subE_lemma {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (Z : Submodule K (Fin n → K)) :
    LinearMap.range (subE Z).mulVecLin = Z := by
  rw [Matrix.range_mulVecLin]
  have e : (subE Z).col = ⇑Z.subtype ∘ ⇑(subBasis Z) := by
    funext j i
    rfl
  rw [e, Set.range_comp, Submodule.span_image, Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem invariantSubspace_coords_X (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : (mtildeKGSD W Ch sel mu).Ok) :
    (V0X W Ch sel mu Xg P).map ((mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec).toLinearMap =
      LinearMap.range ((V0C W Ch sel mu h Xg P).E).mulVecLin := by
  unfold V0X
  rw [rf_range_ga]
  exact (range_subE_lemma _).symm

end Rows

section LvlPart

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (h : S.Ok) {A : Type} [Group A] [Fintype A]
  (ρ : Representation K A S.EqFun)

theorem rf_mem_lvlPart_iff (P : Subgroup A) (ψ : P →* Kˣ) (φ : S.EqFun) :
    S.coordOf h S.outSec φ ∈ (S.toCSD h).lvlPart (S.repCSD h ρ) P ψ ↔
      ∀ a : P, ρ (a : A) φ = ((ψ a : Kˣ) : K) • φ := by
  show (∀ a : P, ((S.toCSD h).actMat (S.repCSD h ρ) (a : A)).mulVec (S.coordOf h S.outSec φ) =
      ((ψ a : Kˣ) : K) • S.coordOf h S.outSec φ) ↔ _
  refine forall_congr' (fun a => ?_)
  rw [← rf_coord_act, ← map_smul]
  exact (S.coordOf h S.outSec).injective.eq_iff

end LvlPart

section RowsLvl

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem mem_lvlPartX_iff (h : (mtildeKGSD W Ch sel mu).Ok) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    (mtildeKGSD W Ch sel mu).coordOf h (mtildeKGSD W Ch sel mu).outSec φ ∈
        (MtildeKCSD W Ch sel mu h).lvlPart (g0Act W Ch sel mu h) P.grp P.chr ↔
      φ.1 ∈ (mtildeGSD W Ch sel mu P).EqFun := by
  refine Iff.trans ?_ (mem_MtildeV_iff W Ch sel mu P φ.1).symm
  exact (rf_mem_lvlPart_iff _ h (g0HatRepEqFunX W Ch sel mu) P.grp P.chr φ).trans ⟨fun H => ⟨φ.2, H⟩, fun ⟨_, H⟩ => H⟩

end RowsLvl

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.TiedCF
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

section Step

variable (D : ColRec)

def sigD : D.host.E →ₐ[D.host.F] D.host.E := letI := D.host.cmStar; D.sp.cm.sig

def embT : D.what₂.Tau → D.host.E →+* ℂ := fun τ => D.host.emb (D.eTau τ : D.R.GG)

theorem rankN (i : ℕ) (hi : i ≤ D.R.m) : letI := D.host.cmStar; (D.sp.X i).rank = D.R.N i :=
  letI := D.host.cmStar; D.sp.X_rank i hi

def gramN (i : ℕ) (hi : i ≤ D.R.m) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E :=
  letI := D.host.cmStar
  (D.sp.X i).gram.reindex (finCongr (rankN D i hi)) (finCongr (rankN D i hi))

def clsCrd (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.clsLat u i c).map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def selfDualLatticeCoords (i : ℕ) (hi : i ≤ D.R.m) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.sp.X i).L0.map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def badG : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | (D.host.g 0 : 𝓞 D.host.F) ∈ v.asIdeal ∨ (D.host.g 1 : 𝓞 D.host.F) ∈ v.asIdeal}

abbrev PlT (u : D.what₂.Word) : Type :=
  {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

variable {D}

def lamT (u : D.what₂.Word) (i : ℕ) : D.what₂.Tau → DomWeight (D.R.N i) :=
  fun τ => shW ((D.fm u).lam i τ) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)


set_option maxHeartbeats 1000000 in
structure ClsTied (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) where

  lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) (D.mem u).A.T D.R.f (badG D)

  y : (D.mem u).C.cls i → UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  y_lat : ∀ c (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (clsCrd D u i hi c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb

  stabI : ∀ c, (D.mem u).C.stab i c →* UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom


end Step

section AtT

variable {D : ColRec}

structure AtTTied (u : D.what₂.Word) where

  eV : (D.mem u).A.vT ≃ PlT D u

  piU : 𝓞 D.host.E
  piU_K : (piU : D.host.E) ∈ D.host.K
  piU_norm : (piU : D.host.E) * D.host.conj piU = ((D.mem u).A.T : D.host.E)
  piU_cong : piU - 1 ∈ Ideal.span
    {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}

  res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v
  res_surj : ∀ v, Function.Surjective (res v)
  res_pi : ∀ v, res v piU = 0

  res_conj : ∀ v (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj piU → res v pb ≠ 0
  res_v : ∀ v (x : 𝓞 D.host.F), x ∈ (eV v).1.asIdeal ↔ res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = 0

  tauOf : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ v (x : 𝓞 D.host.F),
    x ∈ (eV v).1.asIdeal ↔ (0 : WithTop ℤ) < D.what₂.places.val w
      (D.embE (D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
        (algebraMap (𝓞 D.host.F) D.host.E x)))

  seenP : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ τ : D.what₂.Tau,
    (0 : WithTop ℤ) < D.what₂.places.val w (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG)
      (if (D.fm u).seenP w = true then (piU : D.host.E) else D.host.conj piU)))

def AtTTied.Pv {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) : Ideal (𝓞 D.host.E) := RingHom.ker (A.res v)

abbrev Ld (D : ColRec) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  dualL (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)

abbrev Lk {u : D.what₂.Word} (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  clsCrd D u i hi c ⊔ A.Pv v • Ld D u i hi c


set_option maxHeartbeats 1000000 in
structure LvTied (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) where

  pr : ∀ v c, ↥(Ld D u i hi c) →+ (D.fm u).lv i v c
  pr_surj : ∀ v c, Function.Surjective (pr v c)
  pr_smul : ∀ v c (a : 𝓞 D.host.E) z, pr v c (a • z) = A.res v a • pr v c z
  pr_ker : ∀ v c z, pr v c z = 0 ↔ z.1 ∈ A.Pv v • Ld D u i hi c

  fv_ker : ∀ v c z, (D.fm u).fv i v c (pr v c z) = 0 ↔ z.1 ∈ Lk A i hi v c

  prk : ∀ v c, ↥(Lk A i hi v c) →+ (D.fm u).lk i v c
  prk_surj : ∀ v c, Function.Surjective (prk v c)
  prk_smul : ∀ v c (a : 𝓞 D.host.E) z, prk v c (a • z) = A.res v a • prk v c z
  prk_ker : ∀ v c z, prk v c z = 0 ↔ z.1 ∈ A.Pv v • Lk A i hi v c

  te : ∀ v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c (pr v c z) = 1 →
    ∀ h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ Lk A i hi v c, prk v c ⟨_, h⟩ = (D.fm u).te i v c

variable {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m}




end AtT

end Formalism.L2.Col.CF

end
end

