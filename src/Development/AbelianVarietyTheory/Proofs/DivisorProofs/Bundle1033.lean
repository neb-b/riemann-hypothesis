module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasBlocksOfSystemOccursInBlockPart
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.OccBlock

open Module Module.End

section Gen

variable {L V J : Type} [Field L] [DecidableEq L] [AddCommGroup V] [Module L V]

def jointGen (T : J → End L V) (y : J → L) : Submodule L V := ⨅ j, (T j).maxGenEigenspace (y j)

theorem mem_iSup_filter (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y) {θ : J → L} {f : V}
    (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (j : J) (hY : f ∈ ⨆ y ∈ Y, p y) :
    f ∈ ⨆ y ∈ Y.filter (fun y => y j = θ j), p y := by
  have hsplit : (⨆ y ∈ Y, p y) ≤ (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ⊔
      (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) := by
    refine iSup₂_le fun y hy => ?_
    by_cases h : y j = θ j
    · exact le_sup_of_le_left (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
    · exact le_sup_of_le_right (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hsplit hY)
  have hA : (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ≤ (T j).maxGenEigenspace (θ j) := by
    refine iSup₂_le fun y hy => ?_
    have hyj := (Finset.mem_filter.1 hy).2
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ = (T j).maxGenEigenspace (θ j) := by rw [hyj]
  have hB : (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) ≤ ⨆ (μ : L) (_ : μ ≠ θ j), (T j).maxGenEigenspace μ := by
    refine iSup₂_le fun y hy => ?_
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ ≤ _ := le_biSup (fun μ => (T j).maxGenEigenspace μ) (show y j ∈ {μ | μ ≠ θ j} from (Finset.mem_filter.1 hy).2)
  have hfθ : f ∈ (T j).maxGenEigenspace (θ j) := by
    rw [mem_maxGenEigenspace]
    exact ⟨1, by simp [hf j]⟩
  have hb0 : b = 0 := by
    have hb1 : b ∈ (T j).maxGenEigenspace (θ j) := by
      have hbe : b = f - a := by rw [← hab]; abel
      rw [hbe]
      exact Submodule.sub_mem _ hfθ (hA ha)
    exact (Submodule.disjoint_def.1 ((Module.End.independent_maxGenEigenspace (T j)) (θ j))) b hb1 (hB hb)
  rw [← hab, hb0, add_zero]
  exact ha

theorem mem_of_mem_iSup_finset (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y)
    {θ : J → L} {f : V} (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (hY : f ∈ ⨆ y ∈ Y, p y) : f ∈ p θ := by
  induction Y using Finset.strongInduction with
  | H Y ih =>
    by_cases h : ∃ y ∈ Y, y ≠ θ
    · obtain ⟨y0, hy0, hne⟩ := h
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
      exact ih _ (Finset.filter_ssubset.2 ⟨y0, hy0, hj⟩) (mem_iSup_filter T p hp hf Y j hY)
    · push_neg at h
      exact (iSup₂_le fun y hy => by rw [h y hy] : (⨆ y ∈ Y, p y) ≤ p θ) hY

end Gen

section Read

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)

def heckeQ (i : F.I) : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) where
  toFun h g := F.emb (F.cst i) • ∑ s ∈ F.tr i, h (g * s)
  map_add' h h' := by
    funext g
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' c h := by
    funext g
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_smul, smul_smul, mul_comm]

variable {F lam} {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type}
  {B : BlockDat K G0 Pl0} {w : HeightOneSpectrum (𝓞 K)}

theorem rd_pow (R : Reads F lam B w) (i : F.I) (a : K) (k : ℕ) (v : B.S.Forms) :
    R.rd (((B.op (R.ix i) - a • (1 : End K B.S.Forms)) ^ k) v) =
      ((heckeQ F lam i - R.e0 a • (1 : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam))) ^ k) (R.rd v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    funext g
    simp [map_sub, map_smulₛₗ, R.hecke, heckeQ]

end Read

theorem hasBlock_of_occurs : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type)
    (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N)
    (lam : ι → ℕ → ℕ) (R : Reads F lam B w) (Z : Submodule K B.S.Forms), (∀ P, B.op (P, 0) = 1) →
    Z ≤ B.ZH → ∀ θ, R.Occurs Z θ → R.HasBlock θ ∧ F.IsEig lam θ := by
  intro K _ _ _ G0 _ _ Pl0 B w l _ ι _ N F lam R Z hop hZ θ hocc
  obtain ⟨f, hfspan, hfe⟩ := hocc
  refine ⟨?_, ⟨f, hfe⟩⟩
  classical
  let S : Set (F.I → PadicAlgCl l) :=
    {y | ∃ x : B.Pl × ℕ → K, (∀ P, x (P, 0) = 1) ∧ Formalism.L2.Col.HasBlocks B.n B.q B.t B.bl x ∧ ∀ i, y i = R.e0 (x (R.ix i))}
  let p : (F.I → PadicAlgCl l) → Submodule (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) :=
    fun y => ⨆ (_ : y ∈ S), jointGen (heckeQ F lam) y
  have hp : ∀ y, p y ≤ jointGen (heckeQ F lam) y := fun y => iSup_le fun _ => le_rfl
  have key : B.ZH ≤ (⨆ y, p y).comap R.rd := by
    rw [BlockDat.ZH, Formalism.L2.Col.blockSum, Formalism.L2.Col.eigSum]
    refine iSup₂_le fun x hx => ?_
    intro v hv
    rw [Submodule.mem_comap]
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
      exact Submodule.zero_mem _
    have hx1 : ∀ P, x (P, 0) = 1 := fun P =>
      GlobalTheory.ExpFrame.eq_one_of_occurs (op := B.op) ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩) (hop P)
    refine Submodule.mem_iSup_of_mem (fun i => R.e0 (x (R.ix i))) ?_
    refine Submodule.mem_iSup_of_mem (show (fun i => R.e0 (x (R.ix i))) ∈ S from ⟨x, hx1, hx, fun i => rfl⟩) ?_
    rw [jointGen, Submodule.mem_iInf]
    intro i
    have hv' := Formalism.L2.Col.eigAt_le B.op x (R.ix i) hv
    rw [mem_maxGenEigenspace] at hv' ⊢
    obtain ⟨k, hk⟩ := hv'
    exact ⟨k, by rw [← rd_pow, hk, map_zero]⟩
  have hspan : Submodule.span (PadicAlgCl l) (R.rd '' Z) ≤ ⨆ y, p y := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact key (hZ hz)
  obtain ⟨Y, hY⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hspan hfspan)
  have hf : ∀ i, heckeQ F lam i f = θ i • f := fun i => by
    funext g
    exact hfe.2.2 i g
  have hθ := mem_of_mem_iSup_finset (heckeQ F lam) p hp hf Y hY
  by_cases hθS : θ ∈ S
  · exact hθS
  · exfalso
    have h0 : p θ = ⊥ := by simp [p, hθS]
    rw [h0, Submodule.mem_bot] at hθ
    exact hfe.1 hθ

end GlobalTheory.OccBlock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
section
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaSatake

open GlobalTheory.ThetaPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev cw (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  conjSrc (IsCMField.complexConj E).toRingEquiv w

theorem theta_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((cw w).adicCompletion E)) :
    thetaGL n (cFin E) (locGL E n (cw w) g) =
      locGL E n w (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL n (cFin E) (locGL E n (cw w) g)) =
      thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cw v)) (locGL E n (cw w) g))) := fun v =>
    map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
      (Matrix.GeneralLinearGroup.map (cFin E) (locGL E n (cw w) g))
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL n (cFin E) (locGL E n (cw w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v)
        (locGL E n w (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g))) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one, map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin n) (v.adicCompletion E) => u.val i j) (key2 v)

theorem conjLoc_surj (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem absNorm_cw (w : HeightOneSpectrum (𝓞 E)) : Ideal.absNorm (cw w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
  simp only [Ideal.absNorm_eq_natCard]
  exact Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)) w.asIdeal (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv

def cloc (w : HeightOneSpectrum (𝓞 E)) : (cw w).adicCompletion E ≃+* w.adicCompletion E :=
  RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surj w⟩

theorem thetaGL_conj (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((cw w).adicCompletion E)) :
    thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      PhiU n _ * GlobalTheory.LFun.ConjPlace.invT (cloc w) n g * (PhiU n _)⁻¹ := by
  have e1 : GlobalTheory.LFun.ConjPlace.invT (cloc w) n g =
      GlobalTheory.CuspRep.invT n _ (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) :=
    Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
  rw [e1]
  rfl

theorem phiU_mem {K : Type} [Field K] (O : Subring K) (n : ℕ) : PhiU n K ∈ Formalism.UG.GLint (Fin n) O := by
  have h : ∀ i j : Fin n, GlobalTheory.Tw.Phi n K i j ∈ O := fun i j => by
    simp only [GlobalTheory.Tw.Phi, Matrix.of_apply]
    split_ifs
    · exact pow_mem (neg_mem (one_mem O)) _
    · exact zero_mem O
  exact GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨h, fun i j => h j i⟩

theorem hasSatGL_of_invT {w w' : HeightOneSpectrum (𝓞 E)} {a : ℕ}
    (c : w.adicCompletion E ≃+* w'.adicCompletion E) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : Formalism.UG.qV E w' = Formalism.UG.qV E w)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w'.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' (GlobalTheory.LFun.ConjPlace.invT c a g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w' ρ' (B.map (·⁻¹)) := by
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) c (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc)
  have hf : ∀ g y, T.toLinearMap ((ρ.comp (GlobalTheory.LFun.ConjPlace.invT c a).symm.toMonoidHom) g y) =
      ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ ((GlobalTheory.LFun.ConjPlace.invT c a).symm g) y) = ρ' g (T y)
    rw [← hT, MulEquiv.apply_symm_apply]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w' ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c hc hq hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT] at this

theorem hasSat_thetaSub {a : ℕ} (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (C : Multiset ℂˣ)
    (h : (CG.mk π).HasSat (cw w) C) : (CG.mk (thetaSub π)).HasSat w (C.map (·⁻¹)) := by
  rw [CG.hasSat_mk] at h ⊢
  let ρ' := (thetaSub π).locRep w
  let T₀ : π.V ≃ₗ[ℂ] (thetaSub π).V := (pull E a).submoduleMap π.V
  have h0 : ∀ g x, ρ' (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) (T₀ x) =
      T₀ (π.locRep (cw w) g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq, ← theta_locGL]
    exact Subtype.ext (pull_act (.fin (locGL E a (cw w) g)) x.1).symm
  let k := PhiU a (w.adicCompletion E)
  let S : (thetaSub π).V ≃ₗ[ℂ] (thetaSub π).V :=
    LinearEquiv.ofLinear (ρ' k⁻¹) (ρ' k) (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
  refine hasSatGL_of_invT (cloc w) (conjLoc_spec _ w).2.2 (absNorm_cw w).symm (T₀.trans S) (fun g x => ?_) h
  change ρ' _ (ρ' k⁻¹ (T₀ x)) = ρ' k⁻¹ (T₀ _)
  rw [← h0, thetaGL_conj, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  dsimp only [k]
  group

end GlobalTheory.ThetaSatake
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.GalDef

def wAt {n : ℕ} (lam : DomWeight n) (k : ℕ) : ℤ := if h : k < n then lam.w ⟨k, h⟩ else 0

def IsRunAt {n : ℕ} (lam : DomWeight n) (p t : ℕ) : Prop :=
  p + t ≤ n ∧ (∀ k, p ≤ k → k < p + t → wAt lam k = wAt lam p) ∧ (1 ≤ p → wAt lam p < wAt lam (p - 1)) ∧
    (p + t < n → wAt lam (p + t) < wAt lam p)

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def jumpsOf (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight n) (τ : E →+* Qbar l) : Multiset ℤ :=
  Finset.univ.val.map fun k : Fin n => (k : ℤ) - (lam (ι.toRingHom.comp τ)).w k

def FrobSat (ι : Qbar l ≃+* ℂ) (π : Submodule ℂ (UA E n → ℂ)) (sgn : ℤˣ) (cp : G E Ω → Polynomial (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → IsUnramU π w →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → GlobalTheory.LFun.HasSatGL w σ.ρ T →
      ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
        cp (g ^ (sgn : ℤ)) = (T.map fun z : ℂˣ =>
          X - C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod

def HasString (l : ℕ) (π : Submodule ℂ (UA E n → ℂ)) (t : ℕ) : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 E), IsSplitAt w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ IsUnramU π w ∧
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (T : Multiset ℂˣ) (ν : ℂ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ T ∧ ‖ν‖ = 1 ∧
        (Multiset.range t).map (fun c : ℕ => ν * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤
          T.map fun z : ℂˣ => (z : ℂ)

end GlobalTheory.GalDef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeStableOfHeckeFramePolynomialAction
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial

namespace GlobalTheory.ExpFrame

theorem map_mk_smul_sum {O A : Type} [CommRing O] [Ring A] [Algebra O A] {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [AddCommGroup W] [Module O W] [Module A W] [IsScalarTower O A W] (U : Submodule A V)
    (ψ : U →ₗ[A] W) {κ : Type} (S : Finset κ) (c : O) (v : κ → V) (hv : ∀ s, v s ∈ U) (x : V) (hx : x ∈ U)
    (e : x = c • ∑ s ∈ S, v s) : c • ∑ s ∈ S, ψ ⟨v s, hv s⟩ = ψ ⟨x, hx⟩ := by
  have e' : (⟨x, hx⟩ : U) = c • ∑ s ∈ S, (⟨v s, hv s⟩ : U) := by
    apply Subtype.ext
    simpa using e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e', LinearMap.map_smul_of_tower, map_sum]

section
variable {O A G I : Type} [CommRing O] [Ring A] [Algebra O A] [Group G] (Γ : Subgroup G) {K : Subgroup G} (jK : K →* A)
  (tr : I → Finset G) (cst : I → O)

theorem hecke_values_mem {V : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (U : Submodule A V) (t : MvPolynomial I O) :
    ∀ f : Forms O Γ jK V, (∀ g, (f : G → V) g ∈ U) →
      ∀ g, ((t • f : Forms O Γ jK V) : G → V) g ∈ U := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f hf g
    rw [hV.1 c f]
    exact U.smul_of_tower_mem c (hf g)
  | add p q hp hq =>
    intro f hf g
    rw [add_smul]
    exact U.add_mem (hp f hf g) (hq f hf g)
  | mul_X p i hp =>
    intro f hf g
    rw [mul_smul]
    apply hp
    intro g'
    rw [hV.2 i f g']
    exact U.smul_of_tower_mem _ (U.sum_mem fun s _ => hf _)

theorem hecke_values_map {V W : Type} [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s))
    (U : Submodule A V)
    (ψ : U →ₗ[A] W) (t : MvPolynomial I O) :
    ∀ (f : Forms O Γ jK V) (φ : Forms O Γ jK W)
      (hf : ∀ g, (f : G → V) g ∈ U), (∀ g, (φ : G → W) g = ψ ⟨(f : G → V) g, hf g⟩) →
      ∀ g (h : ((t • f : Forms O Γ jK V) : G → V) g ∈ U),
        ((t • φ : Forms O Γ jK W) : G → W) g = ψ ⟨_, h⟩ := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    intro f φ hf hφ g h
    have e : (⟨_, h⟩ : U) = c • ⟨(f : G → V) g, hf g⟩ := by
      apply Subtype.ext
      simp only [hV.1 c f]
      rfl
    rw [e, LinearMap.map_smul_of_tower, ← hφ g, hW.1 c φ]
    rfl
  | add p q hp hq =>
    intro f φ hf hφ g h
    have hp' := hecke_values_mem Γ jK tr cst hV U p f hf g
    have hq' := hecke_values_mem Γ jK tr cst hV U q f hf g
    have e : (⟨_, h⟩ : U) = ⟨_, hp'⟩ + ⟨_, hq'⟩ := by
      apply Subtype.ext
      simp only [add_smul]
      rfl
    rw [e, map_add (f := _), ← hp f φ hf hφ g hp', ← hq f φ hf hφ g hq', add_smul]
    rfl
  | mul_X p i hp =>
    intro f φ hf hφ g h
    have hX := hecke_values_mem Γ jK tr cst hV U (X i) f hf
    have hφX : ∀ g', (((X i : MvPolynomial I O) • φ : Forms O Γ jK W) : G → W) g' = ψ ⟨_, hX g'⟩ := by
      intro g'
      refine (hW.2 i φ g').trans (Eq.trans ?_ (map_mk_smul_sum U ψ (tr i) (cst i) (fun s => (f : G → V) (g' * s))
        (fun s => hf _) _ (hX g') (hV.2 i f g')))
      exact congrArg (fun z => cst i • z) (Finset.sum_congr rfl fun s _ => hφ (g' * s))
    have h2 : ((p • ((X i : MvPolynomial I O) • f) : Forms O Γ jK V) : G → V) g ∈ U := by
      rw [← mul_smul]
      exact h
    have e : (⟨_, h⟩ : U) = ⟨_, h2⟩ := by
      apply Subtype.ext
      simp only [mul_smul]
    rw [e, mul_smul]
    exact hp _ _ hX hφX g h2

theorem hecke_stable_nat (V W : Type) [AddCommGroup V] [Module O V] [Module A V]
    [IsScalarTower O A V] [Module (MvPolynomial I O) (Forms O Γ jK V)]
    [AddCommGroup W] [Module O W] [Module A W]
    [IsScalarTower O A W] [Module (MvPolynomial I O) (Forms O Γ jK W)]
    (hV : (∀ (c : O) (f : Forms O Γ jK V), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK V) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK V) : G → V) g =
        cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (hW : (∀ (c : O) (f : Forms O Γ jK W), (C c : MvPolynomial I O) • f = c • f) ∧
      ∀ i (f : Forms O Γ jK W) (g : G), (((X i : MvPolynomial I O) • f : Forms O Γ jK W) : G → W) g =
        cst i • ∑ s ∈ tr i, (f : G → W) (g * s)) :
    HeckeStable O Γ jK (MvPolynomial I O) V ∧ HeckeNat O Γ jK (MvPolynomial I O) V W :=
  ⟨fun U t f hf => hecke_values_mem Γ jK tr cst hV U t f hf,
    fun U ψ t f φ hf hf' hφ g => hecke_values_map Γ jK tr cst hV hW U ψ t f φ hf hφ g (hf' g)⟩

end


set_option maxHeartbeats 1000000 in
theorem heckeStable_heckeNat_of_isHecke : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] (W : Type) [AddCommGroup W] [Module F.O W] [Module (alg F.O N lam) W] [IsScalarTower F.O (alg F.O N lam) W] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK W)], F.IsHecke lam jK (NablaT F.O N lam) → F.IsHecke lam jK W → HeckeStable F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) ∧ HeckeNat F.O (A := alg F.O N lam) F.Γ jK F.T (NablaT F.O N lam) W := by
  intro l _ ι _ _ N F lam jK i1 W i2 i3 i4 i5 i6 hV hW
  refine @hecke_stable_nat F.O (alg F.O N lam) F.G F.I _ _ _ _ F.Γ F.K jK F.tr F.cst (NablaT F.O N lam) W _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · exact hV
  · exact hW

end GlobalTheory.ExpFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
section
noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.KSplit

namespace GlobalTheory.JacLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk3 (a b : ℕ) : Fin 1 ⊕ Fin (a + b) ⊕ Fin 1 ≃ Fin (a + (b + 2)) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (by omega))

def IsJacMap (a b : ℕ) (α β : kˣ →* ℂˣ) (χ₁ χ₂ : kˣ → ℂ) (φ : indSp a (b + 2) α β →ₗ[ℂ] indSp a b α β) : Prop :=
  (∀ (u : GL (Fin (a + (b + 2))) k) (X : Matrix (Fin 1) (Fin (a + b) ⊕ Fin 1) k) (Y : Matrix (Fin (a + b)) (Fin 1) k),
      u.val.submatrix (blk3 a b) (blk3 a b) = fromBlocks 1 X 0 (fromBlocks 1 Y 0 1) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * u)) →
        φ f₁ = φ f) ∧
  ∀ (m : GL (Fin (a + (b + 2))) k) (x y : kˣ) (g : GL (Fin (a + b)) k),
      m.val.submatrix (blk3 a b) (blk3 a b) =
        fromBlocks (of fun _ _ => (x : k)) 0 0 (fromBlocks g.val 0 0 (of fun _ _ => (y : k))) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * m)) →
        ∀ h, (φ f₁ : GL (Fin (a + b)) k → ℂ) h = χ₁ x * χ₂ y * (φ f : GL (Fin (a + b)) k → ℂ) (h * g)

end GlobalTheory.JacLine

end
end

