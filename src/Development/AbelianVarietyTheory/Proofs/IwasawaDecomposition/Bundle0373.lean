module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Formalism.LocalToGlobal.Columns.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRationalGLOfUnitaryGroupGramUnitGram
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtInRat

variable {D : D7}

theorem toGf_injective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : Function.Injective (toGf P) := by
  intro a b h
  have h1 : finHom V (P.ψ a) = finHom V (P.ψ b) := congrArg Subtype.val h
  have h2 : Formalism.IndefR.Lev.finE V (P.ψ a) = Formalism.IndefR.Lev.finE V (P.ψ b) := by
    simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, h1]
  rw [hU, hU] at h2
  exact Subtype.ext h2

theorem toGf_surjective {V : HSp D} (P : principalLevelFrame.RowPsi V V.rank) : Function.Surjective (toGf P) := by
  rintro ⟨_, x, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V x)
  obtain ⟨h, hh⟩ := P.onto k k1
  refine ⟨h, Subtype.ext ?_⟩
  show finHom V (P.ψ h) = finHom V x
  rw [hh, k2]

theorem af_nontrivial : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := by
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
    (NumberField.RingOfIntegers.not_isField (maximalRealSubfield D.host.E))
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop.ne
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := ⟨M, hM.isPrime, fun h => by
    rw [h] at hIM
    exact hbot.ne' (le_bot_iff.mp hIM)⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (ReciprocityTheory.Aut.evalAt D.host.E v) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

theorem inclL_injective :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) := by
  haveI := af_nontrivial (D := D)
  haveI : Nontrivial (ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
      (algebraMap (maximalRealSubfield D.host.E) (ReciprocityTheory.Aut.AFplus D.host.E)).injective
  exact (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E).injective

theorem inclA_injective : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

def glL (n : ℕ) : GL (Fin n) D.host.E →* GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E) :=
  Matrix.GeneralLinearGroup.map Algebra.TensorProduct.includeLeftRingHom

theorem glL_injective (n : ℕ) : Function.Injective (glL (D := D) n) := fun a b h =>
  Units.ext (Matrix.map_injective inclL_injective (congrArg Units.val h))

theorem glL_mem (n : ℕ) (x : GL (Fin n) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E n) :
    glL (D := D) n x ∈ ReciprocityTheory.Aut.GA D.host.E n := by
  have h : (x : Matrix (Fin n) (Fin n) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  have h2 := congrArg (fun M => Matrix.map M
    (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)) h
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  show (x : Matrix (Fin n) (Fin n) D.host.E).map _ * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
    ((x : Matrix (Fin n) (Fin n) D.host.E).map _) = 1
  rw [← h2]
  congr 1

def toStd (n : ℕ) : ReciprocityTheory.Aut.GQ0 D.host.E n →* ReciprocityTheory.Aut.GQ D.host.E n where
  toFun x := ⟨⟨glL (D := D) n x.1, glL_mem n x.1 x.2⟩, Subgroup.mem_subgroupOf.2 ⟨x.1, x.2, rfl⟩⟩
  map_one' := by ext1; ext1; exact map_one _
  map_mul' a b := by ext1; ext1; exact map_mul _ _ _

theorem toStd_bij (n : ℕ) : Function.Bijective (toStd (D := D) n) := by
  refine ⟨fun a b h => Subtype.ext (glL_injective n (congrArg (fun y => y.1.1) h)), fun γ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext he)⟩

section V

variable {V : HSp D}

theorem cT_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M =
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) M := rfl

theorem mem_UJ (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E) (hx : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  have h : (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x = 1 := hx
  show Formalism.UG.cT _ (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x = V.gram
  rw [hV, Matrix.mul_one, cT_eq]
  exact mul_eq_one_comm.1 h

theorem mem_rationalGL_of_unitaryGroupGram_unitGram (hV : V.gram = 1) (x : GL (Fin V.rank) D.host.E)
    (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) : x ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  rw [hV, Matrix.mul_one, cT_eq] at h
  exact mul_eq_one_comm.1 h

theorem mem_HR (x : GL (Fin V.rank) D.host.E) (hx : x ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
  have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * x =
    V.gram := hx
  have h2 := GlobalTheory.UnitarySplit.map_cond (inclR (F := D.host.F) (AF D.host.F)) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (sigR (AF D.host.F) D.sp.cm.sig) (fun y => rfl) V.gram x.1
  rw [h] at h2
  exact h2.symm

def toV (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ0 D.host.E V.rank →* Formalism.L2.Theta.GQ V where
  toFun x := ⟨⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) x.1, mem_HR x.1 (mem_UJ hV x.1 x.2)⟩,
    Subgroup.mem_subgroupOf.2 ⟨x.1, mem_UJ hV x.1 x.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext (p := fun g => g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)
    exact map_mul _ _ _

theorem toV_bij (hV : V.gram = 1) : Function.Bijective (toV hV) := by
  refine ⟨fun a b h => Subtype.ext (Units.ext (Matrix.map_injective inclA_injective
    (congrArg (fun y : Formalism.L2.Theta.GQ V => Units.val (y.1 : HR (AF D.host.F) D.sp.cm.sig V.gram).1) h))), fun δ => ?_⟩
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 δ.2)
  exact ⟨⟨x, mem_rationalGL_of_unitaryGroupGram_unitGram hV x hx⟩, Subtype.ext (Subtype.ext he)⟩

def ratE (hV : V.gram = 1) : ReciprocityTheory.Aut.GQ D.host.E V.rank ≃* Formalism.L2.Theta.GQ V :=
  (MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm.trans (MulEquiv.ofBijective (toV hV) (toV_bij hV))

theorem ratE_toStd (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    ratE hV (toStd (D := D) V.rank x) = toV hV x :=
  congrArg (toV hV) ((MulEquiv.ofBijective (toStd (D := D) V.rank) (toStd_bij V.rank)).symm_apply_apply x)

theorem swapAE_injective : Function.Injective (swapAE D) :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective

theorem finHom_eq_of_finE {g h : GA D V} (e : Formalism.IndefR.Lev.finE V g = Formalism.IndefR.Lev.finE V h) :
    finHom V g = finHom V h :=
  Units.ext (Matrix.map_injective swapAE_injective (congrArg Units.val e))

theorem finE_toV (hV : V.gram = 1) (x : ReciprocityTheory.Aut.GQ0 D.host.E V.rank) :
    Formalism.IndefR.Lev.finE V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) =
      km D V.rank (toStd (D := D) V.rank x).1 := by
  apply Units.ext
  ext i j
  show swapAE D ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] (x.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
  simp [Algebra.TensorProduct.map_tmul, swapAE, glL]
  rfl

theorem ratIso_ratE (hV : V.gram = 1) (P : principalLevelFrame.RowPsi V V.rank) (hU : UnitFr P) : RatIso P (ratE hV) := by
  intro γ
  obtain ⟨x, rfl⟩ := (toStd_bij (D := D) V.rank).2 γ
  have hr := ratE_toStd hV x
  refine ⟨(congrArg (Bridge.ratF V) hr).trans (Subtype.ext ?_), fun γ₀ h => ?_⟩
  · exact finHom_eq_of_finE ((finE_toV hV x).trans (hU (toStd (D := D) V.rank x).1).symm)
  · have hx : x.1 = γ₀ := glL_injective V.rank (Units.ext h)
    have key : Bridge.IsRatMat V (toV hV x) γ₀ := by
      show Formalism.L2.Theta.matHom V ((toV hV x : Formalism.L2.Theta.GQ V) : GA D V) = Formalism.UG.bc (incA D) γ₀
      rw [← hx]
      rfl
    exact hr ▸ key

end V

theorem toGf_bij_ratIso : ∀ (D : D7) (V : HSp D) (P : principalLevelFrame.RowPsi V V.rank), V.gram = 1 → UnitFr P →
    Function.Bijective (toGf P) ∧ ∃ e, RatIso P e := by
  intro D V P hV hU
  exact ⟨⟨toGf_injective P hU, toGf_surjective P⟩, ratE hV, ratIso_ratE hV P hU⟩

end GlobalTheory.MtInRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChart
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

section Same

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

structure SameG {y : Ys X n} (p p' : PtY ST SG Q y) : Prop where
  fr : p'.1.1.1.2 = p.1.1.1.2
  ys : p'.1.2 = p.1.2
  at_eq : ∀ w : SG, p'.1.1.deco.1.at w.1 = p.1.1.deco.1.at w.1
  be : p'.1.1.deco.1.be = p.1.1.deco.1.be

theorem SameG.refl {y : Ys X n} (p : PtY ST SG Q y) : SameG p p :=
  ⟨rfl, rfl, fun _ => rfl, rfl⟩

private theorem locP_gmap_eq_of_locP_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (g : Sp E n ≃ₗ[E] Sp E n) {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N') = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g N) := by
  have hs : ∀ (s : 𝓞 E) (z : Sp E n), g.symm (s • z) = s • g.symm z := fun s z =>
    ((g.symm : Sp E n →ₗ[E] Sp E n).restrictScalars (𝓞 E)).map_smul s z
  have hmemL : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ↔ ∃ s ∈ P.asIdeal.primeCompl, s • x ∈ M := fun _ _ => Iff.rfl

  have hmemg : ∀ (M : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap g M) ↔ g.symm x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := by
    intro M x
    rw [hmemL, hmemL]
    constructor
    · rintro ⟨s, hs0, hx⟩
      obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
      have hz' : z = g.symm (s • x) := by
        rw [← hzx]
        simp
      exact ⟨s, hs0, by rw [← hs, ← hz']; exact hz⟩
    · rintro ⟨s, hs0, hx⟩
      refine ⟨s, hs0, Submodule.mem_map.mpr ⟨g.symm (s • x), by rw [hs]; exact hx, by simp⟩⟩
  ext x
  rw [hmemg, hmemg, h]

theorem SameG.smul {y : Ys X n} {Λ : LevFam X.E X.K n SG} {Θ : LevQFam X.E X.K n Q} (h : FrmG Λ Θ) {p p' : PtY ST SG Q y}
    (r : SameG p p') : SameG ((ptYAct y Λ Θ).toSMul.smul h p) ((ptYAct y Λ Θ).toSMul.smul h p') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact congrArg (fun F => fun P => (FrmG.incl Λ Θ h).1.1 * F P * ((FrmG.incl Λ Θ h).2.2 P)⁻¹.1) r.fr
  · exact congrArg (fun S => (fun v => h.1.1 v) '' S) r.ys
  · intro w
    show Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p'.1.1.deco.1.N) =
      Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal (Formalism.HermitianLatticesTheory.gmap h.1.1 p.1.1.deco.1.N)
    exact locP_gmap_eq_of_locP_eq w.1 h.1.1 (r.at_eq w)
  · exact congrArg (fun B => fun w x => ((FrmG.incl Λ Θ h).2.1 w).1.mulVec (B w (h.1.1.symm x))) r.be

theorem SameG.dn {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) :
    SameG p (p.mv (p.1.1.deco.dn P f')) := by
  classical
  unfold PtY.mv
  refine Eq.mpr (apply_dite (SameG p) _ _ _) ?_
  split
  · refine ⟨rfl, rfl, fun w => ?_, ?_⟩
    · show (p.1.1.deco.dn P f').1.at w.1 = p.1.1.deco.1.at w.1
      unfold DecoSet.dn
      split_ifs with hok
      · exact ((p.1.1.deco.2.dnN_spec P hP.ne).2.2.1 w.1 (hP.sg w).1 (hP.sg w).2).localization_eq
      · rfl
    · show (p.1.1.deco.dn P f').1.be = p.1.1.deco.1.be
      unfold DecoSet.dn
      split_ifs <;> rfl
  · exact SameG.refl p

end Same

section Coset

private theorem cosetIn_eq_of_sameG' {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q := by
  have hfr : ∀ P, frsF sel mu q'.1.1 P = frsF sel mu q.1.1 P := by
    intro P
    unfold frsF
    split_ifs with hP
    · unfold Deco.liftFr
      rw [r.at_eq ⟨P.1, hP⟩, r.be]
    · exact congrFun r.fr _
  funext P
  unfold cosetIn
  rw [r.ys, hfr P]


open Classical GlobalTheory.TopStep in
theorem cosetIn_eq_of_sameG {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (hX : X.Ok) (hPr : Pr.Ok)
    {q q' : PtAt R sel mu cst u j} (r : SameG q q') : cosetIn q' = cosetIn q :=
  cosetIn_eq_of_sameG' r

end Coset

section Normal

theorem prefRep_pref {G D : Type} [Group G] [MulAction G D] (pref : D → Prop) (q : MulAction.orbitRel.Quotient G D)
    (h : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = q ∧ pref p) : pref (prefRep pref q) := by
  unfold prefRep
  rw [dite_eq_left h]
  exact h.choose_spec.2

theorem GStep.NormalFor.eq {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} {b : S.β} {f : S.D b → A}
    {q q' : S.D b} (hq : S.NormalFor b f q) (hq' : S.NormalFor b f q')
    (h : ∀ r, (∃ g : S.G b, r = f (g • q)) ↔ ∃ g : S.G b, r = f (g • q')) : f q = f q' := by
  unfold GStep.NormalFor at hq hq'
  rw [hq, hq']
  exact congrArg (@Classical.epsilon A ⟨f q⟩) (funext fun r => propext (h r))

theorem GStep.exists_normalFor {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (q : S.D b) : ∃ g : S.G b, S.NormalFor b f (g • q) := by
  have hex : ∃ r, ∃ g : S.G b, r = f (g • q) := ⟨f q, 1, by rw [one_smul]⟩
  obtain ⟨g, hg⟩ := Classical.epsilon_spec hex
  refine ⟨g, ?_⟩
  have hset : (fun r => ∃ g : S.G b, r = f (g • q)) = (fun r => ∃ g' : S.G b, r = f (g' • g • q)) := by
    funext r
    apply propext
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩
    · rintro ⟨g', rfl⟩
      exact ⟨g' * g, by rw [mul_smul]⟩
  unfold GStep.NormalFor
  exact hg.symm.trans (congrArg (@Classical.epsilon A ⟨f q⟩) hset)

theorem GStep.prefRep_eq_of_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hn : ∀ q : MulAction.orbitRel.Quotient (S.G b) (S.D b), S.NormalFor b f (prefRep pf q)) (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) (d' : S.D b)
    (hd : ∀ h : S.G b, f (h • d') = f (h • prefRep pf q)) :
    f (prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d')) = f (prefRep pf q) := by
  obtain ⟨k, hk⟩ : ∃ k : S.G b, k • d' = prefRep pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d') :=
    Quotient.exact (prefRep_spec pf (Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) d'))
  refine GStep.NormalFor.eq (hn _) (hn q) fun r => ⟨?_, ?_⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k, by rw [← hk, ← mul_smul, hd]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * k⁻¹, by rw [← hd, ← hk, mul_smul, inv_smul_smul]⟩

theorem GStep.prefRep_normal {E K A : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (b : S.β) (f : S.D b → A)
    (pf : S.D b → Prop) (hpf : ∀ p, pf p → S.NormalFor b f p) (hnp : ∀ p, S.NormalFor b f p → pf p)
    (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) : S.NormalFor b f (prefRep pf q) := by
  obtain ⟨g, hg⟩ := GStep.exists_normalFor S b f (Quotient.out q)
  have hex : ∃ p, Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) p = q ∧ pf p :=
    ⟨g • Quotient.out q, (Quotient.sound (s := MulAction.orbitRel (S.G b) (S.D b)) (MulAction.mem_orbit _ g)).trans
      (Quotient.out_eq q), hnp _ hg⟩
  exact hpf _ (prefRep_pref pf q hex)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem TC.pref_of_normalFor (u : B.Word) (a : I.ι) (j : ℕ) (hj : j + 1 = B.R.m) (b : (I.stp0 u a j).β) (p : (I.stp0 u a j).D b)
    (h : (I.stp0 u a j).NormalFor b (fun q' : (I.stp0 u a j).D b => cosetIn q') p) : I.pref u a j b p := by
  have hm := B.R.two_le_m
  refine ⟨fun h0 => absurd hj (by omega), fun _ => h, ?_⟩
  show ∀ h : j = B.R.m, _
  intro hjm
  exact absurd hjm (by omega)

private theorem TC.cosetIn_rep_cl_dn_eq (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (v : (B.primes X).vT u)
    (c : (I.stp u a i).Cl) (f : Sp B.fields.E (B.R.N i) → Res v.1) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (((I.atIn u a).A i).dn c.1 ((I.stp u a i).rep c) v f))) =
      cosetIn ((I.stp u a i).rep c) := by
  obtain ⟨b, q⟩ := c
  have r0 : SameG ((I.stp u a i).rep ⟨b, q⟩) (((I.atIn u a).A i).dn b ((I.stp u a i).rep ⟨b, q⟩) v f) :=
    SameG.dn _ v (moveHyp_of_ok hPr u v) f
  by_cases hi : i + 1 = B.R.m
  · exact GStep.prefRep_eq_of_normal (I.stp0 u a i) b (fun q' => cosetIn q') (I.pref u a i b)
      (GStep.prefRep_normal (I.stp0 u a i) b _ (I.pref u a i b) (fun p hp => hp.2.1 hi)
        (fun p hp => I.pref_of_normalFor u a i hi b p hp)) q _
      (fun h => cosetIn_eq_of_sameG' (SameG.smul h r0))
  ·
    have hemp : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u i, cosetIn p = fun _ => ∅ := by
      intro p
      have hys : ∀ (Y : Set (Sp B.fields.E (B.R.N i))) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))),
          Y ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) i).ys N → Y = ∅ := by
        intro Y N hY
        unfold ysAt at hY
        rw [if_neg hi] at hY
        exact hY
      have hp : p.1.2 = ∅ := hys _ _ p.2
      funext P
      unfold cosetIn
      rw [hp]
      ext z
      simp
    exact (hemp _).trans (hemp _).symm

end Normal

theorem TC.dn_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → chOf ((I.fm l u a).dn i v c.1 g) = β := by
  intro B X I _ _ l Z u a i hi bad Ch chOf K eY eV L hK _ _ _ v β c g _

  obtain ⟨k, hR⟩ := hK
  exact ((hR.key ((I.fm l u a).dn i v c.1 g) c.1).mpr ⟨rfl, I.cosetIn_rep_cl_dn_eq l.pr u a i v c.1 _⟩).trans c.2

end GlobalTheory.Mem.Col2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatPrimeNotMem
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.TwistPlaces

theorem natPrime_not_mem {A : Type} [CommRing A] (P : Ideal A) [hP : P.IsPrime] {p l : ℕ} (hp : p.Prime) (hl : l.Prime)
    (hne : l ≠ p) (hpP : (p : A) ∈ P) : (l : A) ∉ P :=
  _root_.GlobalTheory.NatCastNotMemPrime.natCast_notMem_of_prime_ne P hp hl hne hpP

theorem twistPlaces : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ a : I.ι,
    (∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP) → Formalism.IndefR.Lev.IsTwistPlaces (D := X.toD7) X.toD7.host.g (I.Q a) ∧
    ∀ PP ∈ I.Q a, ((X.toD7.host.QS * X.toD7.host.q * X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal ∧
      ∀ u : X.toD7.what₂.Word, (((X.toD7.mem u).A.T : ℕ) : 𝓞 X.toD7.host.E) ∉ PP.asIdeal := by
  intro X px I hI a hU
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host _ X.B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := fun PP (hPP : PP ∈ I.Q a) => htw.2.2.2 PP (hU PP hPP)
  have hstar : ∀ x : X.B.host.E, star x = X.B.host.conj x := bridge_star_holds X.B.R X.B.host

  have off : ∀ PP ∈ I.Q a, ∀ l : ℕ, l.Prime → l ∈ I.S → ((l : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := by
    intro PP hPP l hl hS
    obtain ⟨-, hp, -, hpS⟩ := key PP hPP
    exact natPrime_not_mem PP.asIdeal hp hl (fun e => hpS (e ▸ hS)) (Ideal.absNorm_mem PP.asIdeal)
  refine ⟨fun PP hPP => ⟨?_, fun PP' hPP' hc => ?_⟩, fun PP hPP => ⟨?_, fun u => ?_⟩⟩
  · obtain ⟨-, hp, hsq, hpS⟩ := key PP hPP
    refine ⟨Ideal.absNorm PP.asIdeal, hp, ?_, hsq, fun i e => hpS (e ▸ hI.g_mem i)⟩
    show Nat.card (𝓞 X.B.host.E ⧸ PP.asIdeal) = Ideal.absNorm PP.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  · obtain ⟨v, -, rfl, -⟩ := I.exists_of_mem_Q hPP
    obtain ⟨v', -, rfl, -⟩ := I.exists_of_mem_Q hPP'
    have hle : v.asIdeal ≤ v'.asIdeal := by
      intro c hc'
      have h1 : algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c ∈ (I.sel v).asIdeal := by
        have := hI.sel_ok v
        rw [← this] at hc'
        exact hc'
      obtain ⟨c', h2, h3⟩ := hc _ h1
      have h4 : c' = algebraMap (𝓞 X.B.host.F) (𝓞 X.B.host.E) c := by
        apply RingOfIntegers.ext
        rw [h3]
        show star (algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)) = algebraMap X.B.host.F X.B.host.E (c : X.B.host.F)
        rw [hstar, ← X.B.conjF_eq, AlgHom.commutes]
      rw [h4] at h2
      rw [← hI.sel_ok v']
      exact h2
    have hv : v = v' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)
    subst hv
    obtain ⟨⟨x, hx, hy⟩, -⟩ := key _ hPP
    obtain ⟨c', h2, h3⟩ := hc x hx
    exact hy c' (h3.trans (hstar _)) h2
  · have hp2 : ((X.B.host.QS : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := fun h => by
      rw [← Nat.prod_primeFactorsList X.B.host.QS_pos.ne', Nat.cast_list_prod] at h
      have := PP.isPrime
      obtain ⟨a, ha, h'⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem PP.isPrime
        ((X.B.host.QS.primeFactorsList.map Nat.cast : List (𝓞 X.B.host.E)) : Multiset _)).1 (by simpa using h)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 ha)
      exact off PP hPP l (Nat.prime_of_mem_primeFactorsList hl)
        (hI.mem_of_dvd_QS (Nat.prime_of_mem_primeFactorsList hl) (Nat.dvd_of_mem_primeFactorsList hl)) h'
    have hq : ((X.B.host.q : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.1 hI.two_q_d_mem.2.1
    have hd : ((X.B.host.d : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal := off PP hPP _ X.B.host.hyp.2.1 hI.two_q_d_mem.2.2
    have hT : ((X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal :=
      off PP hPP _ (X.B.T_prime X.B.u₀) (hI.T_mem X.B.u₀)
    have hsp : X.toD7.sp.T = X.B.T X.B.u₀ := X.B.sp_T
    rw [hsp]
    show ((X.B.host.QS * X.B.host.q * X.B.host.d * X.B.T X.B.u₀ : ℕ) : 𝓞 X.B.host.E) ∉ PP.asIdeal
    have hPr := PP.isPrime
    push_cast
    intro h
    rcases hPr.mem_or_mem h with h | h
    · rcases hPr.mem_or_mem h with h | h
      · rcases hPr.mem_or_mem h with h | h
        · exact hp2 (by exact_mod_cast h)
        · exact hq h
      · exact hd h
    · exact hT h
  · have hA : (X.toD7.mem u).A.T = X.B.T u := X.C.A_T u
    rw [hA]
    exact off PP hPP _ (X.B.T_prime u) (hI.T_mem u)

end GlobalTheory.Mem.TwistPlaces
end

