module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitSatLoc

section Local
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def rtHom (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] : GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun x := NG.rt L n x
  map_one' := LinearMap.ext fun f => funext fun g => by simp [NG.rt]
  map_mul' x y := LinearMap.ext fun f => funext fun g => by simp [NG.rt, mul_assoc]

theorem map_symm_map (s : SplitPlace L) (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) {n : ℕ} (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    Matrix.GeneralLinearGroup.map c.symm.toRingHom
      (Matrix.GeneralLinearGroup.map c.toRingHom g : GL (Fin n) (s.w.adicCompletion L)) = g :=
  Units.ext (Matrix.ext fun a b => by simp)

theorem map_map_symm (s : SplitPlace L) (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) {n : ℕ} (g : GL (Fin n) (s.w.adicCompletion L)) :
    Matrix.GeneralLinearGroup.map c.toRingHom
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom g : GL (Fin n) (s.v.adicCompletion L⁺)) = g :=
  Units.ext (Matrix.ext fun a b => by simp)

theorem mem_Ov_iff {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    (a : s.v.adicCompletion L⁺) :
    c a ∈ Formalism.UG.Ov L s.w ↔ a ∈ (s.v.adicCompletionIntegers L⁺).toSubring := by
  show c a ∈ s.w.adicCompletionIntegers L ↔ a ∈ s.v.adicCompletionIntegers L⁺
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    GlobalTheory.SplitConjVal.valuation_eq s c hc hcL]

theorem map_mem_KGL_iff {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) {n : ℕ}
    (g : GL (Fin n) (s.v.adicCompletion L⁺)) :
    Matrix.GeneralLinearGroup.map c.toRingHom g ∈ GlobalTheory.LFun.KGL s.w (n := n) ↔
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring := by
  rw [GlobalTheory.LFun.KGL, GlobalTheory.HeckeScalarSph.mem_GLint_iff, GlobalTheory.HeckeScalarSph.mem_GLint_iff, ← map_inv]
  simp only [Matrix.GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, mem_Ov_iff hc hcL]

theorem isUnifV_map {s : SplitPlace L} {c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L} (hc : Continuous c) (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ) : Formalism.UG.IsUnifV L s.w (c ϖ) := by
  show Valued.v (c ϖ) = _
  rw [GlobalTheory.SplitConjVal.valuation_eq s c hc hcL]
  exact hϖ

theorem coe_glMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ} (g : GL (Fin n) A) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map f :=
  rfl

theorem diagJ_map {A B : Type} [Field A] [Field B] (f : A →+* B) (n : ℕ) (ϖ : A) (k : ℕ) :
    (Formalism.UG.diagJ n ϖ k).map f = Formalism.UG.diagJ n (f ϖ) k := by
  simp only [Formalism.UG.diagJ, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  split_ifs <;> simp

end Local

section Key
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def locAct (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n) :
    Representation ℂ (GL (Fin n) (s.w.adicCompletion L)) (GAf L n → W) :=
  (rtHom n W).comp (e.comp (Matrix.GeneralLinearGroup.map c.symm.toRingHom))

theorem locAct_apply (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n)
    (g : GL (Fin n) (s.w.adicCompletion L)) (f : GAf L n → W) :
    locAct n W s c e g f = NG.rt L n (e (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)) f := rfl

theorem heckeD_eq_heckeVec {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (s : SplitPlace L)
    (c : s.v.adicCompletion L⁺ ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hcL : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x)
    (e : GL (Fin n) (s.v.adicCompletion L⁺) →* GAf L n) (he1 : ∀ g, TrivOutside {s.v} (e g))
    (he2 : ∀ g, s.loc n (e g) = g) (J : Subgroup (GAf L n))
    (hJ : ∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) {ϖ : s.v.adicCompletion L⁺} (hϖ : IsUnif L s.v ϖ)
    (k : ℕ) {F : GAf L n → W} (hF : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ F = F) :
    NG.heckeD J (tSet L n s ϖ k) F =
      GlobalTheory.LFun.heckeVec (locAct n W s c e) (GlobalTheory.LFun.KGL s.w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov L s.w) (c ϖ) k) F := by
  classical
  have hψφ : ∀ g : GL (Fin n) (s.v.adicCompletion L⁺),
      Matrix.GeneralLinearGroup.map c.symm.toRingHom
        (Matrix.GeneralLinearGroup.map c.toRingHom g : GL (Fin n) (s.w.adicCompletion L)) = g := map_symm_map s c
  have hφψ : ∀ g : GL (Fin n) (s.w.adicCompletion L),
      Matrix.GeneralLinearGroup.map c.toRingHom
        (Matrix.GeneralLinearGroup.map c.symm.toRingHom g : GL (Fin n) (s.v.adicCompletion L⁺)) = g := map_map_symm s c
  obtain ⟨α0, -, hT0⟩ := GlobalTheory.HeckeScalarSph.exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_repsU (n := n) s.v α0
  have hR1' : ∀ γ ∈ R, γ ∈ tSet L n s ϖ k := fun γ hγ => (hT0 γ).2 (hR1 γ hγ)
  have hR2' : ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n := fun x hx => hR2 x ((hT0 x).1 hx)
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun x hx => hx.1
  rw [GlobalTheory.HeckeEigConj.heckeD_eq_sum_of_agree J hJ hD hR1' hR2' hF]
  have hU := isUnifV_map hc hcL hϖ
  rw [GlobalTheory.SatHecke.Tj_eq_dosetInd hU k]
  have hK : ∀ x, TrivOutside {s.v} x →
      (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ GlobalTheory.LFun.KGL s.w (n := n) ↔ x ∈ Umax L n) := fun x hx =>
    (map_mem_KGL_iff hc hcL _).trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)
  have hFK : F ∈ GlobalTheory.PRep.fixed (locAct n W s c e) (GlobalTheory.LFun.KGL s.w (n := n)) := by
    refine GlobalTheory.LGrp.mem_fixed.2 fun A hA => ?_
    rw [locAct_apply]
    refine hF _ ((hK _ (he1 _)).1 ?_) (he1 _)
    rw [he2, hφψ]; exact hA
  have hdiag : ∀ a b x : GL (Fin n) (s.v.adicCompletion L⁺),
      (x : Matrix (Fin n) (Fin n) _) = (a : Matrix (Fin n) (Fin n) _) * Formalism.UG.diagJ n ϖ k * (b : Matrix (Fin n) (Fin n) _) →
      (Matrix.GeneralLinearGroup.map c.toRingHom x : GL (Fin n) (s.w.adicCompletion L)) =
        Matrix.GeneralLinearGroup.map c.toRingHom a *
          Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) *
            Matrix.GeneralLinearGroup.map c.toRingHom b := by
    intro a b x h
    refine Units.ext ?_
    simp only [Units.val_mul, coe_glMap, h, Matrix.map_mul, diagJ_map,
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    rfl
  have hinj : Set.InjOn (fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
      GL (Fin n) (s.w.adicCompletion L))) R := by
    intro γ hγ δ hδ h
    have h' : s.loc n γ = s.loc n δ := by
      have := congrArg (Matrix.GeneralLinearGroup.map c.symm.toRingHom) h
      simpa only [hψφ] using this
    exact GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n s γ δ (hD γ (hR1' γ hγ)) (hD δ (hR1' δ hδ)) h'
  have hmem : ∀ γ ∈ R, (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) : GL (Fin n) (s.w.adicCompletion L)) ∈
      DoubleCoset.doubleCoset (Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
        (GlobalTheory.SatHecke.diagJ_det_ne hU k)) (GlobalTheory.LFun.KGL s.w (n := n) : Set (GL (Fin n) (s.w.adicCompletion L)))
        (GlobalTheory.LFun.KGL s.w (n := n)) := by
    intro γ hγ
    obtain ⟨-, a, ha, b, hb, h⟩ := hR1' γ hγ
    exact DoubleCoset.mem_doubleCoset.2 ⟨_, (map_mem_KGL_iff hc hcL a).2 ha, _, (map_mem_KGL_iff hc hcL b).2 hb,
      hdiag a b _ h⟩
  have huniq : ∀ g ∈ DoubleCoset.doubleCoset (Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
        (GlobalTheory.SatHecke.diagJ_det_ne hU k)) (GlobalTheory.LFun.KGL s.w (n := n) : Set (GL (Fin n) (s.w.adicCompletion L)))
        (GlobalTheory.LFun.KGL s.w (n := n)),
      ∃! r, r ∈ R.image (fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
        GL (Fin n) (s.w.adicCompletion L))) ∧ r⁻¹ * g ∈ GlobalTheory.LFun.KGL s.w (n := n) := by
    intro g hg
    obtain ⟨y, hy, z, hz, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    obtain ⟨x, hx⟩ : ∃ x, x = e (Matrix.GeneralLinearGroup.map c.symm.toRingHom (y *
        Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z)) :=
      ⟨_, rfl⟩
    have hxt : TrivOutside {s.v} x := hx ▸ he1 _
    have hxT : x ∈ tSet L n s ϖ k := by
      refine ⟨hxt, Matrix.GeneralLinearGroup.map c.symm.toRingHom y, ?_,
        Matrix.GeneralLinearGroup.map c.symm.toRingHom z, ?_, ?_⟩
      · exact (map_mem_KGL_iff hc hcL _).1 (by rw [hφψ]; exact hy)
      · exact (map_mem_KGL_iff hc hcL _).1 (by rw [hφψ]; exact hz)
      · rw [hx, he2, map_mul, map_mul, Units.val_mul, Units.val_mul]
        congr 2
        rw [coe_glMap, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagJ_map]
        simp
    obtain ⟨γ, ⟨hγR, hγx⟩, hγu⟩ := hR2' x hxT
    have hkey : ∀ δ ∈ R, ((Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n δ) :
        GL (Fin n) (s.w.adicCompletion L))⁻¹ * (y * Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k)
          (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z) ∈ GlobalTheory.LFun.KGL s.w (n := n) ↔ δ⁻¹ * x ∈ Umax L n) := by
      intro δ hδ
      have e1 : (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n δ) : GL (Fin n) (s.w.adicCompletion L))⁻¹ *
          (y * Matrix.GeneralLinearGroup.mkOfDetNeZero (Formalism.UG.diagJ n (c ϖ) k) (GlobalTheory.SatHecke.diagJ_det_ne hU k) * z) =
          Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (δ⁻¹ * x)) := by
        rw [map_mul, map_mul, map_inv, map_inv, hx, he2, hφψ]
      rw [e1]
      exact hK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hD δ (hR1' δ hδ))) hxt)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hγR, (hkey γ hγR).2 hγx⟩, ?_⟩
    rintro r ⟨hr, hr'⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hr
    rw [hγu δ ⟨hδ, (hkey δ hδ).1 hr'⟩]
  rw [GlobalTheory.LFun.heckeVec_dosetInd hFK (R := R.image fun γ => (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n γ) :
    GL (Fin n) (s.w.adicCompletion L))) (fun r hr => ?_) huniq, Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [locAct_apply, hψφ, GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n s (e (s.loc n γ)) γ (he1 _)
      (hD γ (hR1' γ hγ)) (he2 _)]
  · obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hr
    exact hmem γ hγ

end Key
section Main


end Main

end GlobalTheory.SplitSatLoc

end
